//! Timer module for the protocol stack
//!
//! This module provides software timer functionality corresponding to
//! microps/platform/linux/timer.c
//!
//! タイマーはネットワークプロトコルスタックで以下の用途に使用されます：
//! - TCP再送タイマー
//! - 接続タイムアウト検出
//! - ARPキャッシュの有効期限管理
//! - 定期的なハウスキーピング処理

use std::sync::{Arc, Mutex, atomic::{AtomicBool, Ordering}};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

/// Error type for timer operations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TimerError {
    AllocationFailed,
    AlreadyRunning,
    NotRunning,
    CreateFailed(String),
    LockError,
}

impl std::fmt::Display for TimerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TimerError::AllocationFailed => write!(f, "Memory allocation failed"),
            TimerError::AlreadyRunning => write!(f, "Timer is already running"),
            TimerError::NotRunning => write!(f, "Timer is not running"),
            TimerError::CreateFailed(msg) => write!(f, "Timer creation failed: {}", msg),
            TimerError::LockError => write!(f, "Lock operation failed"),
        }
    }
}

impl std::error::Error for TimerError {}

pub type Result<T> = std::result::Result<T, TimerError>;

/// A single timer entry
///
/// Corresponds to `struct timer` in timer.c
struct TimerEntry {
    /// Timer interval
    interval: Duration,
    /// Last time the handler was called
    last: Instant,
    /// Handler function to call when timer expires
    handler: Box<dyn Fn() + Send + Sync>,
}

/// Timer manager that handles multiple timers
///
/// This struct manages a list of timers and runs them in a background thread.
/// Each timer has an interval and a handler function that gets called when
/// the interval elapses.
pub struct TimerManager {
    /// List of registered timers
    timers: Arc<Mutex<Vec<TimerEntry>>>,
    /// Flag to indicate if the timer loop is running
    running: Arc<AtomicBool>,
    /// Handle to the background timer thread
    thread_handle: Option<JoinHandle<()>>,
    /// Tick interval for checking timers (default: 1ms like in C version)
    tick_interval: Duration,
}

impl TimerManager {
    /// Create a new timer manager
    ///
    /// Corresponds to `timer_init()` in timer.c
    pub fn new() -> Self {
        Self {
            timers: Arc::new(Mutex::new(Vec::new())),
            running: Arc::new(AtomicBool::new(false)),
            thread_handle: None,
            tick_interval: Duration::from_millis(1), // 1ms like in C version
        }
    }

    /// Create a new timer manager with a custom tick interval
    pub fn with_tick_interval(tick_interval: Duration) -> Self {
        Self {
            timers: Arc::new(Mutex::new(Vec::new())),
            running: Arc::new(AtomicBool::new(false)),
            thread_handle: None,
            tick_interval,
        }
    }

    /// Register a new timer with the given interval and handler
    ///
    /// Corresponds to `timer_register()` in timer.c
    ///
    /// # Arguments
    /// * `interval` - The interval at which the handler should be called
    /// * `handler` - The function to call when the timer expires
    ///
    /// # Example
    /// ```ignore
    /// let mut manager = TimerManager::new();
    /// manager.register(Duration::from_secs(1), || {
    ///     println!("Timer fired!");
    /// })?;
    /// ```
    pub fn register<F>(&self, interval: Duration, handler: F) -> Result<()>
    where
        F: Fn() + Send + Sync + 'static,
    {
        let entry = TimerEntry {
            interval,
            last: Instant::now(),
            handler: Box::new(handler),
        };

        let mut timers = self.timers.lock().map_err(|_| TimerError::LockError)?;
        timers.push(entry);

        log::info!(
            "Timer registered: interval={:?}, total_timers={}",
            interval,
            timers.len()
        );

        Ok(())
    }

    /// Start the timer loop
    ///
    /// Corresponds to `timer_run()` in timer.c
    /// This spawns a background thread that checks timers at the tick interval.
    pub fn run(&mut self) -> Result<()> {
        if self.running.load(Ordering::SeqCst) {
            return Err(TimerError::AlreadyRunning);
        }

        self.running.store(true, Ordering::SeqCst);

        let timers = Arc::clone(&self.timers);
        let running = Arc::clone(&self.running);
        let tick_interval = self.tick_interval;

        let handle = thread::spawn(move || {
            log::info!(
                "Timer thread started: tick_interval={:?}",
                tick_interval
            );

            while running.load(Ordering::SeqCst) {
                // Sleep for the tick interval
                thread::sleep(tick_interval);

                // Process all timers
                if let Ok(mut timers) = timers.lock() {
                    let now = Instant::now();
                    for timer in timers.iter_mut() {
                        let elapsed = now.duration_since(timer.last);
                        if elapsed >= timer.interval {
                            // Call the handler
                            (timer.handler)();
                            timer.last = now;
                        }
                    }
                }
            }

            log::info!("Timer thread stopped");
        });

        self.thread_handle = Some(handle);

        log::info!(
            "Timer run started: interval={:?}",
            self.tick_interval
        );

        Ok(())
    }

    /// Stop the timer loop
    ///
    /// Corresponds to `timer_shutdown()` in timer.c
    pub fn shutdown(&mut self) -> Result<()> {
        if !self.running.load(Ordering::SeqCst) {
            return Err(TimerError::NotRunning);
        }

        // Signal the thread to stop
        self.running.store(false, Ordering::SeqCst);

        // Wait for the thread to finish
        if let Some(handle) = self.thread_handle.take() {
            handle.join().map_err(|_| TimerError::LockError)?;
        }

        log::info!("Timer shutdown complete");

        Ok(())
    }

    /// Check if the timer loop is running
    pub fn is_running(&self) -> bool {
        self.running.load(Ordering::SeqCst)
    }

    /// Get the number of registered timers
    pub fn timer_count(&self) -> Result<usize> {
        let timers = self.timers.lock().map_err(|_| TimerError::LockError)?;
        Ok(timers.len())
    }

    /// Clear all registered timers
    pub fn clear(&self) -> Result<()> {
        let mut timers = self.timers.lock().map_err(|_| TimerError::LockError)?;
        timers.clear();
        Ok(())
    }
}

impl Default for TimerManager {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for TimerManager {
    fn drop(&mut self) {
        if self.running.load(Ordering::SeqCst) {
            let _ = self.shutdown();
        }
    }
}

// ============================================================================
// Global timer instance (similar to C static variables)
// ============================================================================

use std::sync::OnceLock;

static GLOBAL_TIMER: OnceLock<Mutex<TimerManager>> = OnceLock::new();

/// Initialize the global timer
///
/// Corresponds to `timer_init()` in timer.c
pub fn timer_init() -> Result<()> {
    GLOBAL_TIMER
        .set(Mutex::new(TimerManager::new()))
        .map_err(|_| TimerError::AlreadyRunning)?;
    log::info!("Global timer initialized");
    Ok(())
}

/// Register a timer with the global timer manager
///
/// Corresponds to `timer_register()` in timer.c
pub fn timer_register<F>(interval: Duration, handler: F) -> Result<()>
where
    F: Fn() + Send + Sync + 'static,
{
    let manager = GLOBAL_TIMER
        .get()
        .ok_or(TimerError::NotRunning)?
        .lock()
        .map_err(|_| TimerError::LockError)?;
    manager.register(interval, handler)
}

/// Start the global timer
///
/// Corresponds to `timer_run()` in timer.c
pub fn timer_run() -> Result<()> {
    let mut manager = GLOBAL_TIMER
        .get()
        .ok_or(TimerError::NotRunning)?
        .lock()
        .map_err(|_| TimerError::LockError)?;
    manager.run()
}

/// Shutdown the global timer
///
/// Corresponds to `timer_shutdown()` in timer.c
pub fn timer_shutdown() -> Result<()> {
    let mut manager = GLOBAL_TIMER
        .get()
        .ok_or(TimerError::NotRunning)?
        .lock()
        .map_err(|_| TimerError::LockError)?;
    manager.shutdown()
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::AtomicU32;

    #[test]
    fn test_timer_manager_creation() {
        let manager = TimerManager::new();
        assert!(!manager.is_running());
        assert_eq!(manager.timer_count().unwrap(), 0);
    }

    #[test]
    fn test_timer_registration() {
        let manager = TimerManager::new();
        
        manager
            .register(Duration::from_millis(100), || {
                println!("Timer 1 fired");
            })
            .unwrap();

        manager
            .register(Duration::from_millis(200), || {
                println!("Timer 2 fired");
            })
            .unwrap();

        assert_eq!(manager.timer_count().unwrap(), 2);
    }

    #[test]
    fn test_timer_execution() {
        let mut manager = TimerManager::with_tick_interval(Duration::from_millis(1));
        let counter = Arc::new(AtomicU32::new(0));
        let counter_clone = Arc::clone(&counter);

        manager
            .register(Duration::from_millis(10), move || {
                counter_clone.fetch_add(1, Ordering::SeqCst);
            })
            .unwrap();

        manager.run().unwrap();
        
        // Wait for some timer executions
        thread::sleep(Duration::from_millis(50));
        
        manager.shutdown().unwrap();

        // Should have fired at least a few times
        let count = counter.load(Ordering::SeqCst);
        assert!(count >= 3, "Expected at least 3 executions, got {}", count);
    }

    #[test]
    fn test_timer_clear() {
        let manager = TimerManager::new();
        
        manager
            .register(Duration::from_millis(100), || {})
            .unwrap();
        
        assert_eq!(manager.timer_count().unwrap(), 1);
        
        manager.clear().unwrap();
        
        assert_eq!(manager.timer_count().unwrap(), 0);
    }
}
