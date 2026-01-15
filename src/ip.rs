use crate::net::{NetProtocol, NetProtocolType, ProtocolStack, Result};

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

fn ip_input(protocol_stack: &ProtocolStack, data: &[u8]) -> Result<()> {
    println!("IP input processing...");
    protocol_stack.handle_input(NetProtocolType::IPv4, data)
}