use crate::net::{NetDevice, NetIfaceFamily, NetProtocol, NetProtocolType, ProtocolStack, Result};
use log::{debug, error, info};
use std::net::Ipv4Addr;
use std::sync::Mutex;
use std::str::FromStr;

// IP バージョン
pub const IP_VERSION_IPV4: u8 = 4;

// IP ヘッダサイズ
pub const IP_HDR_SIZE_MIN: usize = 20;
pub const IP_HDR_SIZE_MAX: usize = 60;

// IP パケットサイズ
pub const IP_TOTAL_SIZE_MAX: usize = u16::MAX as usize;
pub const IP_PAYLOAD_SIZE_MAX: usize = IP_TOTAL_SIZE_MAX - IP_HDR_SIZE_MIN;

// IP アドレス長
pub const IP_ADDR_LEN: usize = 4;

// IP ヘッダフラグ
pub const IP_HDR_FLAG_MF: u16 = 0x2000; // more fragments flag
pub const IP_HDR_FLAG_DF: u16 = 0x4000; // don't fragment flag
pub const IP_HDR_FLAG_RF: u16 = 0x8000; // reserved

pub const IP_HDR_OFFSET_MASK: u16 = 0x1fff;

// 特殊IPアドレス
pub const IP_ADDR_ANY: u32 = 0x00000000;       // 0.0.0.0
pub const IP_ADDR_BROADCAST: u32 = 0xffffffff; // 255.255.255.255

/// IPインタフェース
#[derive(Debug, Clone)]
pub struct IpIface {
    /// 所属デバイスのインデックス
    dev_index: Option<u32>,
    /// ユニキャストアドレス
    pub unicast: Ipv4Addr,
    /// ネットマスク
    pub netmask: Ipv4Addr,
    /// ブロードキャストアドレス
    pub broadcast: Ipv4Addr,
}

impl IpIface {
    /// 新しいIPインタフェースを作成
    pub fn new(unicast: Ipv4Addr, netmask: Ipv4Addr) -> Self {
        // broadcast = (unicast & netmask) | ~netmask
        let unicast_bits: u32 = unicast.into();
        let netmask_bits: u32 = netmask.into();
        let broadcast_bits = (unicast_bits & netmask_bits) | !netmask_bits;

        IpIface {
            dev_index: None,
            unicast,
            netmask,
            broadcast: Ipv4Addr::from(broadcast_bits),
        }
    }

    /// 文字列からIPインタフェースを作成
    pub fn alloc(unicast: &str, netmask: &str) -> Result<Self> {
        let unicast_addr = Ipv4Addr::from_str(unicast)
            .map_err(|_| format!("invalid unicast address: {}", unicast))?;
        let netmask_addr = Ipv4Addr::from_str(netmask)
            .map_err(|_| format!("invalid netmask: {}", netmask))?;

        Ok(IpIface::new(unicast_addr, netmask_addr))
    }

    pub fn dev_index(&self) -> Option<u32> {
        self.dev_index
    }

    pub fn set_dev_index(&mut self, index: u32) {
        self.dev_index = Some(index);
    }
}

/// グローバルIPインタフェースリスト
static IP_IFACES: Mutex<Vec<IpIface>> = Mutex::new(Vec::new());

/// IPインタフェースをデバイスに登録
pub fn ip_iface_register(dev: &mut NetDevice, mut iface: IpIface) -> Result<usize> {
    info!(
        "dev={}, unicast={}, netmask={}, broadcast={}",
        dev.name(),
        iface.unicast,
        iface.netmask,
        iface.broadcast
    );

    let mut ifaces = IP_IFACES.lock().map_err(|e| format!("lock error: {}", e))?;
    let iface_index = ifaces.len();

    // デバイスにインタフェースを追加
    dev.add_iface(NetIfaceFamily::IP, iface_index)?;
    iface.set_dev_index(dev.index());

    ifaces.push(iface);
    Ok(iface_index)
}

/// 指定アドレスを持つIPインタフェースを検索
pub fn ip_iface_select(addr: Ipv4Addr) -> Option<IpIface> {
    let ifaces = IP_IFACES.lock().ok()?;
    for iface in ifaces.iter() {
        if iface.unicast == addr {
            return Some(iface.clone());
        }
    }
    None
}

/// デバイスに関連付けられたIPインタフェースを取得
pub fn ip_iface_get(dev: &NetDevice) -> Option<IpIface> {
    let iface_index = dev.get_iface_index(NetIfaceFamily::IP)?;
    let ifaces = IP_IFACES.lock().ok()?;
    ifaces.get(iface_index).cloned()
}

/// インターネットチェックサム (RFC 1071)
pub fn cksum16(data: &[u8], init: u32) -> u16 {
    let mut sum = init;

    // 2バイトずつ加算
    let mut chunks = data.chunks_exact(2);
    for chunk in chunks.by_ref() {
        sum += u16::from_be_bytes([chunk[0], chunk[1]]) as u32;
    }

    // 奇数バイトの場合、最後の1バイトを処理
    if let Some(&last) = chunks.remainder().first() {
        sum += (last as u32) << 8;
    }

    // キャリーを折り返し
    while (sum >> 16) != 0 {
        sum = (sum & 0xffff) + (sum >> 16);
    }

    !(sum as u16)
}

/// IPv4 ヘッダ構造体
/// 
/// ```text
///  0                   1                   2                   3
///  0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
/// +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
/// |Version|  IHL  |Type of Service|          Total Length         |
/// +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
/// |         Identification        |Flags|      Fragment Offset    |
/// +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
/// |  Time to Live |    Protocol   |         Header Checksum       |
/// +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
/// |                       Source Address                          |
/// +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
/// |                    Destination Address                        |
/// +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
/// |                    Options                    |    Padding    |
/// +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
/// ```
#[repr(C, packed)]
#[derive(Debug, Clone, Copy)]
pub struct IpHdr {
    /// Version (4 bits) + IHL (4 bits)
    pub vhl: u8,
    /// Type of Service
    pub tos: u8,
    /// Total Length
    pub total: u16,
    /// Identification
    pub id: u16,
    /// Flags (3 bits) + Fragment Offset (13 bits)
    pub offset: u16,
    /// Time to Live
    pub ttl: u8,
    /// Protocol
    pub protocol: u8,
    /// Header Checksum
    pub sum: u16,
    /// Source Address
    pub src: u32,
    /// Destination Address
    pub dst: u32,
}

impl IpHdr {
    /// バージョンを取得 (上位4ビット)
    pub fn version(&self) -> u8 {
        (self.vhl >> 4) & 0x0f
    }

    /// ヘッダ長を取得 (下位4ビット, 4バイト単位)
    pub fn ihl(&self) -> u8 {
        self.vhl & 0x0f
    }

    /// ヘッダ長をバイト単位で取得
    pub fn hdr_len(&self) -> usize {
        (self.ihl() as usize) * 4
    }

    /// Version と IHL を設定
    pub fn set_vhl(version: u8, ihl: u8) -> u8 {
        ((version & 0x0f) << 4) | (ihl & 0x0f)
    }

    /// フラグを取得 (上位3ビット)
    pub fn flags(&self) -> u8 {
        ((u16::from_be(self.offset) >> 13) & 0x07) as u8
    }

    /// フラグメントオフセットを取得 (下位13ビット)
    pub fn fragment_offset(&self) -> u16 {
        u16::from_be(self.offset) & 0x1fff
    }

    /// Total Length を取得 (ホストバイトオーダー)
    pub fn total_len(&self) -> u16 {
        u16::from_be(self.total)
    }

    /// Identification を取得 (ホストバイトオーダー)
    pub fn identification(&self) -> u16 {
        u16::from_be(self.id)
    }

    /// Source Address を Ipv4Addr として取得
    pub fn src_addr(&self) -> Ipv4Addr {
        Ipv4Addr::from(u32::from_be(self.src))
    }

    /// Destination Address を Ipv4Addr として取得
    pub fn dst_addr(&self) -> Ipv4Addr {
        Ipv4Addr::from(u32::from_be(self.dst))
    }

    /// バイトスライスから IpHdr への参照を取得
    pub fn from_bytes(data: &[u8]) -> Option<&IpHdr> {
        if data.len() < IP_HDR_SIZE_MIN {
            return None;
        }
        Some(unsafe { &*(data.as_ptr() as *const IpHdr) })
    }
}

/// IPヘッダをデバッグ出力
fn ip_print(data: &[u8]) {
    let hdr = match IpHdr::from_bytes(data) {
        Some(h) => h,
        None => return,
    };

    let v = hdr.version();
    let hl = hdr.ihl();
    let hlen = hdr.hdr_len();
    let total = hdr.total_len();
    let offset = u16::from_be(hdr.offset);

    eprintln!("        vhl: 0x{:02x} [v: {}, hl: {} ({})]", hdr.vhl, v, hl, hlen);
    eprintln!("        tos: 0x{:02x}", hdr.tos);
    eprintln!("      total: {} (payload: {})", total, total as usize - hlen);
    eprintln!("         id: {}", hdr.identification());
    eprintln!("     offset: 0x{:04x} [flags={:x}, offset={}]",
              offset, offset >> 13, offset & IP_HDR_OFFSET_MASK);
    eprintln!("        ttl: {}", hdr.ttl);
    eprintln!("   protocol: {}", hdr.protocol);
    eprintln!("        sum: 0x{:04x}", u16::from_be(hdr.sum));
    eprintln!("        src: {}", hdr.src_addr());
    eprintln!("        dst: {}", hdr.dst_addr());
}

fn dummy_handler(_data: &[u8]) -> Result<()> {
    println!("IP protocol handler invoked.");
    Ok(())
}

pub fn ip_init(protocols: &mut Vec<NetProtocol>) -> Result<()> {
    println!("Initializing IP stack...");
    // IP stack initialization logic here
    let protocol = NetProtocol::new(
        NetProtocolType::IPv4,
        dummy_handler,        
    );

    protocols.push(protocol);
    Ok(())
}

fn ip_input(data: &[u8], dev: &NetDevice) -> Result<()> {
    debug!("dev={}, len={}", dev.name(), data.len());

    // 最小ヘッダサイズチェック
    if data.len() < IP_HDR_SIZE_MIN {
        error!("too short");
        return Err("too short".into());
    }

    let hdr = IpHdr::from_bytes(data).ok_or("failed to parse IP header")?;

    // バージョンチェック
    let v = hdr.version();
    if v != IP_VERSION_IPV4 {
        error!("ip version error: v={}", v);
        return Err("ip version error".into());
    }

    // ヘッダ長チェック
    let hlen = hdr.hdr_len();
    if data.len() < hlen {
        error!("header length error: len={} < hlen={}", data.len(), hlen);
        return Err("header length error".into());
    }

    // チェックサム検証
    if cksum16(&data[..hlen], 0) != 0 {
        error!("checksum error");
        return Err("checksum error".into());
    }

    // トータル長チェック
    let total = hdr.total_len() as usize;
    if data.len() < total {
        error!("total length error: len={} < total={}", data.len(), total);
        return Err("total length error".into());
    }

    // フラグメントチェック（未サポート）
    let offset = u16::from_be(hdr.offset);
    if (offset & IP_HDR_FLAG_MF) != 0 || (offset & IP_HDR_OFFSET_MASK) != 0 {
        error!("fragments does not support");
        return Err("fragments does not support".into());
    }

    // インタフェースチェック
    let iface = match ip_iface_get(dev) {
        Some(iface) => iface,
        None => {
            // インタフェースがない場合は無視
            return Ok(());
        }
    };

    // 宛先アドレスチェック
    let dst = hdr.dst_addr();
    let dst_bits: u32 = dst.into();
    let iface_unicast_bits: u32 = iface.unicast.into();
    let iface_broadcast_bits: u32 = iface.broadcast.into();

    if dst_bits != iface_unicast_bits {
        // ユニキャストアドレスでない場合、ブロードキャストかチェック
        if dst_bits != iface_broadcast_bits && dst_bits != IP_ADDR_BROADCAST {
            // 他のホスト宛のパケットは無視
            return Ok(());
        }
    }

    debug!("permit, dev={}, iface={}", dev.name(), iface.unicast);
    ip_print(&data[..total]);

    Ok(())
}
