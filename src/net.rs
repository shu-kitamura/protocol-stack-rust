
use crate::platform::{platform_init, platform_run, platform_shutdown};


pub type Result<T> = std::result::Result<T, String>;


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

pub fn net_run() -> Result<()> {
    println!("Starting network stack...");
    match platform_run() {
        Ok(_) => {
            println!("Network stack is running.");
            Ok(())
        }
        Err(e) => {
            eprintln!("Failed to run network stack: {}", e);
            Err(format!("Network run error: {}", e))
        }
    }
}

pub fn net_shutdown() -> Result<()> {
    println!("Shutting down network stack...");
    match platform_shutdown() {
        Ok(_) => {
            println!("Network stack shutdown successfully.");
            Ok(())
        }
        Err(e) => {
            eprintln!("Failed to shutdown network stack: {}", e);
            Err(format!("Network shutdown error: {}", e))
        }
    }
}