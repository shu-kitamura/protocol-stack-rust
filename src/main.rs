mod platform;
mod sched;
mod timer;

use platform::{platform_init, platform_run, platform_shutdown};
use timer::TimerManager;
use std::sync::Arc;
use std::sync::atomic::{AtomicU32, Ordering};
use std::time::Duration;

fn main() {
    // Initialize logger
    env_logger::init();

    println!("Initializing platform...");
    
    if let Err(e) = platform_init() {
        eprintln!("Failed to initialize platform: {}", e);
        return;
    }
    
    println!("Platform initialized successfully");
    println!("Random u16: {}", platform::random16());

    // Timer demo
    println!("\n--- Timer Demo ---");
    let mut timer_manager = TimerManager::new();
    let counter = Arc::new(AtomicU32::new(0));
    let counter_clone = Arc::clone(&counter);

    // Register a timer that fires every 100ms
    timer_manager
        .register(Duration::from_millis(100), move || {
            let count = counter_clone.fetch_add(1, Ordering::SeqCst) + 1;
            println!("Timer fired! Count: {}", count);
        })
        .expect("Failed to register timer");

    // Start the timer
    timer_manager.run().expect("Failed to start timer");

    // Let it run for 500ms
    std::thread::sleep(Duration::from_millis(500));

    // Stop the timer
    timer_manager.shutdown().expect("Failed to shutdown timer");
    
    println!(
        "Timer demo complete. Total fires: {}",
        counter.load(Ordering::SeqCst)
    );
    println!("--- End Timer Demo ---\n");
    
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
