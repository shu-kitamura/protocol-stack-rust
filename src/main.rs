mod platform;
mod net;
mod driver;

use platform::intr::{InterruptManager, irq, flags};
use platform::timer::TimerManager;
use net::{net_init, net_run, net_shutdown};
use std::sync::Arc;
use std::sync::atomic::{AtomicU32, Ordering};
use std::time::Duration;

fn main() {
    // Initialize logger
    env_logger::init();

    if let Err(e) = net_init() {
        eprintln!("Network initialization failed: {}", e);
        return;
    }

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

    // Interrupt demo
    println!("--- Interrupt Demo ---");
    let mut intr_manager = InterruptManager::new();
    let irq_counter = Arc::new(AtomicU32::new(0));
    let irq_counter_clone = Arc::clone(&irq_counter);

    // Register an interrupt handler
    intr_manager
        .register(irq::IRQ_USER, move |irq_num| {
            let count = irq_counter_clone.fetch_add(1, Ordering::SeqCst) + 1;
            println!("IRQ {} handled! Count: {}", irq_num, count);
        }, 0)
        .expect("Failed to register IRQ");

    // Start the interrupt handler
    intr_manager.run().expect("Failed to start interrupt handler");

    // Raise some interrupts
    for _ in 0..3 {
        intr_manager.raise(irq::IRQ_USER).expect("Failed to raise IRQ");
        std::thread::sleep(Duration::from_millis(100));
    }

    // Shutdown interrupt handler
    intr_manager.shutdown().expect("Failed to shutdown interrupt handler");

    println!(
        "Interrupt demo complete. Total IRQs handled: {}",
        irq_counter.load(Ordering::SeqCst)
    );
    println!("--- End Interrupt Demo ---\n");

    let mut net_devices = net::NetDevices::new();
    let device = net::NetDevice::new();
    net_devices.net_device_register(device).expect("Failed to register device");
    
    if let Err(e) = net_run(&mut net_devices) {
        eprintln!("Network run failed: {}", e);
        return;
    }
    if let Err(e) = net_shutdown(&mut net_devices) {
        eprintln!("Network shutdown failed: {}", e);
        return;
    }

    println!("Platform shutdown complete");
}
