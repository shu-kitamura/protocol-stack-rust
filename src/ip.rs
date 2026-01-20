use crate::net::{NetProtocol, NetProtocolType, ProtocolStack, Result};
use log::{debug, error};
use std::net::Ipv4Addr;

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

fn ip_input(data: &[u8], dev_name: &str) -> Result<()> {
    debug!("dev={}, len={}", dev_name, data.len());

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

    ip_print(&data[..total]);

    Ok(())
}
