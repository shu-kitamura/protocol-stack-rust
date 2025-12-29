mod platform;

use platform::{platform_init, platform_run, platform_shutdown};

fn main() {
    println!("Initializing platform...");
    
    if let Err(e) = platform_init() {
        eprintln!("Failed to initialize platform: {}", e);
        return;
    }
    
    println!("Platform initialized successfully");
    println!("Random u16: {}", platform::random16());
    
    if let Err(e) = platform_run() {
        eprintln!("Failed to run platform: {}", e);
        return;
    }
    
    if let Err(e) = platform_shutdown() {
        eprintln!("Failed to shutdown platform: {}", e);
        return;
    }
    
    println!("Platform shutdown complete");
}
