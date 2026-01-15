
use crate::platform::{platform_init, platform_run, platform_shutdown};


pub type Result<T> = std::result::Result<T, String>;

const NetDeviceAddrMaxLen: usize = 16;

pub struct ProtocolStack {
    protocols: Vec<NetProtocol>,
}

impl ProtocolStack {
    pub fn new() -> Self {
        let mut protocols: Vec<NetProtocol> = Vec::new();

        // register IP protocol
        crate::ip::ip_init(&mut protocols).expect("Failed to initialize IP protocol");

        ProtocolStack {
            protocols,
        }
    }

    pub fn register_protocol(&mut self, protocol: NetProtocol) -> Result<()> {
        // Check for duplicate protocol types
        for p in &self.protocols {
            if p.protocol_type == protocol.protocol_type {
                return Err(format!(
                    "Protocol type {:?} is already registered",
                    protocol.protocol_type
                ));
            }
        }
        self.protocols.push(protocol);
        Ok(())
    }

    pub fn handle_input(&self, protocol_type: NetProtocolType, data: &[u8]) -> Result<()> {
        for protocol in &self.protocols {
            if protocol.protocol_type == protocol_type {
                (protocol.handler)(data)?;
                return Ok(());
            }
        }
        Err(format!("No handler registered for protocol type {:?}", protocol_type))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NetProtocolType {
    IPv4 = 0x0800,
    ARP  = 0x0806,
    RARP = 0x8035,
    IPv6 = 0x86dd,
}

pub struct NetProtocol {
    // Fields for network protocol
    protocol_type: NetProtocolType,
    handler: fn(&[u8]) -> Result<()>,
}

impl NetProtocol {
    pub fn new(protocol_type: NetProtocolType, handler: fn(&[u8]) -> Result<()>) -> Self {
        NetProtocol {
            protocol_type,
            handler,
        }
    }
}

pub enum NetDeviceType {
    Dummy  = 0x0000,
    Loopback = 0x0001,
    Ethernet = 0x0002,
}

pub enum NetDeviceFlag {
    Up          = 0x0001,
    Loopback    = 0x0010,
    Broadcast   = 0x0020,
    P2P         = 0x0040,
    NeedARP     = 0x0100,
}

pub struct NetDevices {
    devices: Vec<NetDevice>,
}

pub trait NetDeviceOps {
    // Placeholder for network device operations
    fn init(&self) -> Result<()>;
    
    fn output(&self, data: &[u8]) -> Result<()>;

}

impl NetDevices {
    pub fn new() -> Self {
        NetDevices {
            devices: Vec::new(),
        }
    }

    pub fn net_device_register(&mut self, mut device: NetDevice) -> Result<()> {
        device.index = self.devices.len() as u32;
        device.name = format!("eth{}", device.index);

        self.devices.push(device);
        Ok(())
    }
}

pub struct NetDevice {
    index: u32,
    name: String,
    type_id: NetDeviceType,
    mtu: u16,
    flags: u8,
    hlen: u8,
    alen: u8,
    addr: [u8; NetDeviceAddrMaxLen],
    broadcast_addr: [u8; NetDeviceAddrMaxLen],
    net_device_ops: Option<Box<dyn NetDeviceOps>>,
    void_ptr: Option<*mut ()>,
}

impl NetDevice {
    pub fn new() -> Self {
        NetDevice {
            index: 0,
            name: String::new(),
            type_id: NetDeviceType::Ethernet,
            mtu: 1500,
            flags: 0,
            hlen: 6,
            alen: 6,
            addr: [0; NetDeviceAddrMaxLen],
            broadcast_addr: [0xFF; NetDeviceAddrMaxLen],
            net_device_ops: None,
            void_ptr: None,
        }
    }

    pub fn open(&mut self) -> Result<()> {
        self.flags = self.flags | NetDeviceFlag::Up as u8;
        Ok(())
    }

    pub fn close(&mut self) -> Result<()> {
        self.flags = self.flags & !(NetDeviceFlag::Up as u8);
        Ok(())
    }
}

pub fn net_init() -> Result<()> {
    println!("Initializing network stack...");
    match platform_init() {
        Ok(_) => {
            println!("Network stack initialized successfully.");
            Ok(())
        }
        Err(e) => {
            eprintln!("Failed to initialize network stack: {}", e);
            Err(format!("Network initialization error: {}", e))
        }
    }
}

pub fn net_run(net_devices: &mut NetDevices) -> Result<()> {
    println!("Starting network stack...");
    match platform_run() {
        Ok(_) => {
            for device in net_devices.devices.iter_mut() {
                match device.open() {
                    Err(e) => eprintln!("Failed to open device {}: {}", device.name, e),
                    Ok(_) => println!("Device {} is now up.", device.name),
                }
            }
            Ok(())
        }
        Err(e) => {
            eprintln!("Failed to run network stack: {}", e);
            Err(format!("Network run error: {}", e))
        }
    }
}

pub fn net_shutdown(net_devices: &mut NetDevices) -> Result<()> {
    println!("Shutting down network stack...");
    match platform_shutdown() {
        Ok(_) => {
            println!("Network stack shutdown successfully.");
            for device in net_devices.devices.iter_mut() {
                match device.close() {
                    Err(e) => eprintln!("Failed to close device {}: {}", device.name, e),
                    Ok(_) => println!("Device {} is now down.", device.name),
                }
            }
            Ok(())
        }
        Err(e) => {
            eprintln!("Failed to shutdown network stack: {}", e);
            Err(format!("Network shutdown error: {}", e))
        }
    }
}
