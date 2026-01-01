//! Interrupt handling module for the protocol stack
//!
//! This module provides software interrupt functionality corresponding to
//! microps/platform/linux/intr.c
//!
//! ソフトウェア割り込みはネットワークプロトコルスタックで以下の用途に使用されます：
//! - パケット受信通知
//! - タイマーイベント処理
//! - 非同期イベント処理

use std::collections::HashMap;
use std::sync::{Arc, Mutex, atomic::{AtomicBool, Ordering}};
use std::thread::{self, JoinHandle};

/// IRQ numbers corresponding to Unix signals
/// These match the C version's definitions in intr.h
pub mod irq {
    /// Soft interrupt (corresponds to SIGUSR1)
    pub const IRQ_SOFT: u32 = 10;  // SIGUSR1
    /// User interrupt (corresponds to SIGUSR2)
    pub const IRQ_USER: u32 = 12;  // SIGUSR2
    /// Timer interrupt (corresponds to SIGALRM)
    pub const IRQ_TIMER: u32 = 14; // SIGALRM
    /// Base for real-time signals
    pub const IRQ_BASE: u32 = 34;  // SIGRTMIN+1
}

/// Flags for IRQ registration
pub mod flags {
    /// Allow multiple handlers for the same IRQ
    pub const IRQ_SHARED: u32 = 0x0001;
}

/// Error type for interrupt operations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IntrError {
    /// IRQ registration conflict
    IrqConflict(u32),
    /// Memory allocation failed
    AllocationFailed,
    /// Already running
    AlreadyRunning,
    /// Not running
    NotRunning,
    /// Lock operation failed
    LockError,
    /// IRQ not found
    IrqNotFound(u32),
    /// Thread creation failed
    ThreadCreateFailed(String),
}

impl std::fmt::Display for IntrError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IntrError::IrqConflict(irq) => {
                write!(f, "Conflicts with already registered IRQ: {}", irq)
            }
            IntrError::AllocationFailed => write!(f, "Memory allocation failed"),
            IntrError::AlreadyRunning => write!(f, "Interrupt handler is already running"),
            IntrError::NotRunning => write!(f, "Interrupt handler is not running"),
            IntrError::LockError => write!(f, "Lock operation failed"),
            IntrError::IrqNotFound(irq) => write!(f, "IRQ {} not found", irq),
            IntrError::ThreadCreateFailed(msg) => {
                write!(f, "Thread creation failed: {}", msg)
            }
        }
    }
}

impl std::error::Error for IntrError {}

pub type Result<T> = std::result::Result<T, IntrError>;

/// Interrupt Service Routine type
///
/// Corresponds to `typedef void (*intr_isr_t)(unsigned int irq, void *arg)` in intr.h
pub type IsrHandler = Box<dyn Fn(u32) + Send + Sync>;

/// A single IRQ entry
///
/// Corresponds to `struct irq_entry` in intr.c
struct IrqEntry {
    /// The IRQ number
    irq: u32,
    /// The interrupt service routine
    isr: IsrHandler,
    /// Flags (e.g., IRQ_SHARED)
    flags: u32,
}

/// Interrupt manager that handles software interrupts
///
/// This struct manages a list of IRQ handlers and processes interrupts
/// in a background thread. It uses channels instead of Unix signals
/// for cross-platform compatibility and safety.
pub struct InterruptManager {
    /// Registered IRQ handlers
    irqs: Arc<Mutex<Vec<IrqEntry>>>,
    /// Pending interrupts queue
    pending: Arc<Mutex<Vec<u32>>>,
    /// Flag to indicate if the interrupt loop is running
    running: Arc<AtomicBool>,
    /// Handle to the background interrupt thread
    thread_handle: Option<JoinHandle<()>>,
    /// Condvar for waking up the interrupt thread
    notify: Arc<(Mutex<bool>, std::sync::Condvar)>,
}

impl InterruptManager {
    /// Create a new interrupt manager
    ///
    /// Corresponds to `intr_init()` in intr.c
    pub fn new() -> Self {
        Self {
            irqs: Arc::new(Mutex::new(Vec::new())),
            pending: Arc::new(Mutex::new(Vec::new())),
            running: Arc::new(AtomicBool::new(false)),
            thread_handle: None,
            notify: Arc::new((Mutex::new(false), std::sync::Condvar::new())),
        }
    }

    /// Register an interrupt handler for the given IRQ
    ///
    /// Corresponds to `intr_register()` in intr.c
    ///
    /// # Arguments
    /// * `irq` - The IRQ number to register
    /// * `isr` - The interrupt service routine to call
    /// * `flags` - Flags (e.g., `flags::IRQ_SHARED`)
    ///
    /// # Returns
    /// * `Ok(())` on success
    /// * `Err(IntrError::IrqConflict)` if the IRQ conflicts with existing registration
    pub fn register<F>(&self, irq: u32, isr: F, flags: u32) -> Result<()>
    where
        F: Fn(u32) + Send + Sync + 'static,
    {
        let mut irqs = self.irqs.lock().map_err(|_| IntrError::LockError)?;

        // Check for conflicts
        for entry in irqs.iter() {
            if entry.irq == irq {
                // Both must have SHARED flag to allow multiple handlers
                if (entry.flags & flags::IRQ_SHARED) == 0 || (flags & flags::IRQ_SHARED) == 0 {
                    log::error!("Conflicts with already registered IRQ: {}", irq);
                    return Err(IntrError::IrqConflict(irq));
                }
            }
        }

        let entry = IrqEntry {
            irq,
            isr: Box::new(isr),
            flags,
        };

        irqs.push(entry);
        log::info!("IRQ {} registered successfully", irq);

        Ok(())
    }

    /// Raise an interrupt (send IRQ to the interrupt handler thread)
    ///
    /// Corresponds to `intr_raise()` in intr.c
    ///
    /// # Arguments
    /// * `irq` - The IRQ number to raise
    pub fn raise(&self, irq: u32) -> Result<()> {
        {
            let mut pending = self.pending.lock().map_err(|_| IntrError::LockError)?;
            pending.push(irq);
        }

        // Wake up the interrupt thread
        let (lock, cvar) = &*self.notify;
        let mut notified = lock.lock().map_err(|_| IntrError::LockError)?;
        *notified = true;
        cvar.notify_one();

        Ok(())
    }

    /// Start the interrupt handling loop
    ///
    /// Corresponds to `intr_run()` in intr.c
    /// This spawns a background thread that processes pending interrupts.
    pub fn run(&mut self) -> Result<()> {
        if self.running.load(Ordering::SeqCst) {
            return Err(IntrError::AlreadyRunning);
        }

        self.running.store(true, Ordering::SeqCst);

        let irqs = Arc::clone(&self.irqs);
        let pending = Arc::clone(&self.pending);
        let running = Arc::clone(&self.running);
        let notify = Arc::clone(&self.notify);

        let handle = thread::spawn(move || {
            log::info!("Interrupt handler thread started");

            while running.load(Ordering::SeqCst) {
                // Wait for notification or timeout
                let (lock, cvar) = &*notify;
                {
                    let mut notified = lock.lock().unwrap();
                    // Wait with timeout to periodically check running flag
                    let result = cvar
                        .wait_timeout(notified, std::time::Duration::from_millis(100))
                        .unwrap();
                    notified = result.0;
                    *notified = false;
                }

                // Process all pending interrupts
                let irqs_to_process: Vec<u32> = {
                    let mut pending_guard = pending.lock().unwrap();
                    std::mem::take(&mut *pending_guard)
                };

                for irq in irqs_to_process {
                    if irq != irq::IRQ_TIMER {
                        log::debug!("IRQ <{}> occurred", irq);
                    }

                    let irqs_guard = irqs.lock().unwrap();
                    for entry in irqs_guard.iter() {
                        if entry.irq == irq {
                            (entry.isr)(irq);
                            // If not shared, only call the first matching handler
                            if (entry.flags & flags::IRQ_SHARED) == 0 {
                                break;
                            }
                        }
                    }
                }
            }

            log::info!("Interrupt handler thread terminated");
        });

        self.thread_handle = Some(handle);
        log::info!("Interrupt handler started");

        Ok(())
    }

    /// Shutdown the interrupt handling loop
    ///
    /// Corresponds to `intr_shutdown()` in intr.c
    pub fn shutdown(&mut self) -> Result<()> {
        if !self.running.load(Ordering::SeqCst) {
            return Err(IntrError::NotRunning);
        }

        self.running.store(false, Ordering::SeqCst);

        // Wake up the thread so it can exit
        let (lock, cvar) = &*self.notify;
        {
            let mut notified = lock.lock().map_err(|_| IntrError::LockError)?;
            *notified = true;
        }
        cvar.notify_one();

        // Wait for the thread to finish
        if let Some(handle) = self.thread_handle.take() {
            handle.join().map_err(|_| {
                IntrError::ThreadCreateFailed("Failed to join interrupt thread".to_string())
            })?;
        }

        log::info!("Interrupt handler shutdown complete");
        Ok(())
    }

    /// Check if the interrupt handler is running
    pub fn is_running(&self) -> bool {
        self.running.load(Ordering::SeqCst)
    }

    /// Get the number of registered IRQs
    pub fn registered_count(&self) -> Result<usize> {
        let irqs = self.irqs.lock().map_err(|_| IntrError::LockError)?;
        Ok(irqs.len())
    }
}

impl Default for InterruptManager {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for InterruptManager {
    fn drop(&mut self) {
        if self.running.load(Ordering::SeqCst) {
            let _ = self.shutdown();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU32, Ordering};
    use std::time::Duration;

    #[test]
    fn test_register_and_raise() {
        let mut manager = InterruptManager::new();
        let counter = Arc::new(AtomicU32::new(0));
        let counter_clone = Arc::clone(&counter);

        // Register an IRQ handler
        manager
            .register(irq::IRQ_USER, move |_irq| {
                counter_clone.fetch_add(1, Ordering::SeqCst);
            }, 0)
            .expect("Failed to register IRQ");

        // Start the interrupt handler
        manager.run().expect("Failed to start interrupt handler");

        // Raise the interrupt
        manager.raise(irq::IRQ_USER).expect("Failed to raise IRQ");

        // Wait a bit for the handler to process
        thread::sleep(Duration::from_millis(200));

        // Check that the handler was called
        assert_eq!(counter.load(Ordering::SeqCst), 1);

        // Shutdown
        manager.shutdown().expect("Failed to shutdown");
    }

    #[test]
    fn test_shared_irq() {
        let mut manager = InterruptManager::new();
        let counter1 = Arc::new(AtomicU32::new(0));
        let counter2 = Arc::new(AtomicU32::new(0));
        let c1 = Arc::clone(&counter1);
        let c2 = Arc::clone(&counter2);

        // Register two shared IRQ handlers for the same IRQ
        manager
            .register(irq::IRQ_SOFT, move |_| {
                c1.fetch_add(1, Ordering::SeqCst);
            }, flags::IRQ_SHARED)
            .expect("Failed to register first IRQ");

        manager
            .register(irq::IRQ_SOFT, move |_| {
                c2.fetch_add(1, Ordering::SeqCst);
            }, flags::IRQ_SHARED)
            .expect("Failed to register second IRQ");

        manager.run().expect("Failed to start");

        // Raise the interrupt
        manager.raise(irq::IRQ_SOFT).expect("Failed to raise");

        thread::sleep(Duration::from_millis(200));

        // Both handlers should be called
        assert_eq!(counter1.load(Ordering::SeqCst), 1);
        assert_eq!(counter2.load(Ordering::SeqCst), 1);

        manager.shutdown().expect("Failed to shutdown");
    }

    #[test]
    fn test_irq_conflict() {
        let manager = InterruptManager::new();

        // Register a non-shared IRQ
        manager
            .register(irq::IRQ_USER, |_| {}, 0)
            .expect("Failed to register first IRQ");

        // Try to register another non-shared handler for the same IRQ
        let result = manager.register(irq::IRQ_USER, |_| {}, 0);
        assert!(matches!(result, Err(IntrError::IrqConflict(_))));
    }
}
