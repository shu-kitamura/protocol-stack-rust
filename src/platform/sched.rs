//! Scheduler module for the protocol stack
//!
//! This module provides task scheduling functionality corresponding to
//! microps/platform/linux/sched.c
//!
//! スケジューラはネットワークプロトコルスタックで以下の用途に使用されます：
//! - タスクのスリープ/ウェイクアップ管理
//! - 割り込みによるタスクの中断
//! - 条件変数を使用した同期

use std::sync::{Condvar, Mutex};
use std::time::Duration;

/// Error type for scheduler operations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SchedError {
    /// Task is still in use (wait count > 0)
    TaskInUse,
    /// Lock operation failed
    LockError,
    /// Operation was interrupted
    Interrupted,
    /// Timeout occurred
    Timeout,
    /// Initialization failed
    InitFailed,
}

impl std::fmt::Display for SchedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SchedError::TaskInUse => write!(f, "Task is still in use"),
            SchedError::LockError => write!(f, "Lock operation failed"),
            SchedError::Interrupted => write!(f, "Operation was interrupted"),
            SchedError::Timeout => write!(f, "Operation timed out"),
            SchedError::InitFailed => write!(f, "Scheduler initialization failed"),
        }
    }
}

impl std::error::Error for SchedError {}

pub type Result<T> = std::result::Result<T, SchedError>;

/// Internal state of a scheduler task
struct SchedTaskInner {
    /// Whether the task has been interrupted
    interrupted: bool,
    /// Wait count - number of threads waiting on this task
    wc: u32,
}

/// A scheduler task that can sleep and be woken up
///
/// Corresponds to `struct sched_task` in sched.c
///
/// This structure provides a mechanism for tasks to sleep until either:
/// - They are explicitly woken up by another task
/// - A timeout occurs
/// - They are interrupted by a signal
pub struct SchedTask {
    /// Condition variable for sleeping/waking
    cond: Condvar,
    /// Internal state protected by mutex
    inner: Mutex<SchedTaskInner>,
}

impl SchedTask {
    /// Create a new scheduler task
    ///
    /// Corresponds to `sched_task_init()` in sched.c
    pub fn new() -> Self {
        Self {
            cond: Condvar::new(),
            inner: Mutex::new(SchedTaskInner {
                interrupted: false,
                wc: 0,
            }),
        }
    }

    /// Check if this task can be destroyed
    ///
    /// Returns an error if the task is still in use (wait count > 0)
    ///
    /// Corresponds to `sched_task_destroy()` in sched.c
    pub fn can_destroy(&self) -> Result<()> {
        let inner = self.inner.lock().map_err(|_| SchedError::LockError)?;
        if inner.wc > 0 {
            return Err(SchedError::TaskInUse);
        }
        Ok(())
    }

    /// Sleep until woken up, interrupted, or optionally until timeout
    ///
    /// Corresponds to `sched_task_sleep()` in sched.c
    ///
    /// Unlike the C version which takes an external lock, this version uses
    /// the internal mutex of the SchedTask. This is a more Rust-idiomatic
    /// approach that avoids lifetime issues.
    ///
    /// # Arguments
    /// * `timeout` - Optional timeout duration
    ///
    /// # Returns
    /// * `Ok(())` - The task was woken up normally
    /// * `Err(SchedError::Interrupted)` - The task was interrupted
    /// * `Err(SchedError::Timeout)` - The timeout expired
    pub fn sleep(&self, timeout: Option<Duration>) -> Result<()> {
        let mut inner = self.inner.lock().map_err(|_| SchedError::LockError)?;
        
        // Check if already interrupted
        if inner.interrupted {
            return Err(SchedError::Interrupted);
        }

        // Increment wait count
        inner.wc += 1;

        // Add to global task list
        TASKS.add(self);

        // Wait on condition variable
        let result = if let Some(timeout_duration) = timeout {
            let (new_inner, wait_result) = self
                .cond
                .wait_timeout(inner, timeout_duration)
                .map_err(|_| SchedError::LockError)?;
            inner = new_inner;
            
            if wait_result.timed_out() && !inner.interrupted {
                // Remove from global task list and decrement wait count
                TASKS.remove(self);
                inner.wc -= 1;
                return Err(SchedError::Timeout);
            }
            Ok(())
        } else {
            inner = self.cond.wait(inner).map_err(|_| SchedError::LockError)?;
            Ok(())
        };

        // Remove from global task list
        TASKS.remove(self);

        // Decrement wait count
        inner.wc -= 1;

        // Check if interrupted
        if inner.interrupted {
            if inner.wc == 0 {
                inner.interrupted = false;
            }
            return Err(SchedError::Interrupted);
        }

        result
    }

    /// Sleep with an external lock
    ///
    /// This version is closer to the C API and takes a reference to an external
    /// Mutex that will be unlocked while sleeping.
    ///
    /// # Arguments
    /// * `external_lock` - A reference to an external Mutex to unlock while sleeping
    /// * `timeout` - Optional timeout duration
    ///
    /// # Returns
    /// * `Ok(())` - The task was woken up normally
    /// * `Err(SchedError::Interrupted)` - The task was interrupted
    /// * `Err(SchedError::Timeout)` - The timeout expired
    pub fn sleep_with_lock<T>(&self, external_lock: &Mutex<T>, timeout: Option<Duration>) -> Result<()> {
        // First check if already interrupted
        {
            let inner = self.inner.lock().map_err(|_| SchedError::LockError)?;
            if inner.interrupted {
                return Err(SchedError::Interrupted);
            }
        }

        // Increment wait count
        {
            let mut inner = self.inner.lock().map_err(|_| SchedError::LockError)?;
            inner.wc += 1;
        }

        // Add to global task list
        TASKS.add(self);

        // Acquire the external lock and wait on the condition variable
        let mut guard = external_lock.lock().map_err(|_| SchedError::LockError)?;
        
        let timed_out = if let Some(timeout_duration) = timeout {
            let (new_guard, wait_result) = self
                .cond
                .wait_timeout(guard, timeout_duration)
                .map_err(|_| SchedError::LockError)?;
            guard = new_guard;
            wait_result.timed_out()
        } else {
            guard = self.cond.wait(guard).map_err(|_| SchedError::LockError)?;
            false
        };
        
        drop(guard);

        // Remove from global task list
        TASKS.remove(self);

        // Decrement wait count and check interrupted status
        let mut inner = self.inner.lock().map_err(|_| SchedError::LockError)?;
        inner.wc -= 1;

        if inner.interrupted {
            if inner.wc == 0 {
                inner.interrupted = false;
            }
            return Err(SchedError::Interrupted);
        }

        if timed_out {
            return Err(SchedError::Timeout);
        }

        Ok(())
    }

    /// Wake up all threads waiting on this task
    ///
    /// Corresponds to `sched_task_wakeup()` in sched.c
    pub fn wakeup(&self) {
        self.cond.notify_all();
    }

    /// Mark this task as interrupted and wake up all waiters
    ///
    /// Used by the IRQ handler to interrupt sleeping tasks
    fn interrupt(&self) -> Result<()> {
        let mut inner = self.inner.lock().map_err(|_| SchedError::LockError)?;
        if !inner.interrupted {
            inner.interrupted = true;
            drop(inner);
            self.cond.notify_all();
        }
        Ok(())
    }
}

impl Default for SchedTask {
    fn default() -> Self {
        Self::new()
    }
}

// Note: SchedTask contains Condvar and Mutex which are !Send and !Sync by default
// We need to explicitly implement these traits because we know our usage is safe
unsafe impl Send for SchedTask {}
unsafe impl Sync for SchedTask {}

/// Global task list for tracking sleeping tasks
///
/// Corresponds to static `tasks` variable in sched.c
struct TaskList {
    tasks: Mutex<Vec<*const SchedTask>>,
}

impl TaskList {
    const fn new() -> Self {
        Self {
            tasks: Mutex::new(Vec::new()),
        }
    }

    fn add(&self, task: *const SchedTask) {
        if let Ok(mut tasks) = self.tasks.lock() {
            tasks.push(task);
        }
    }

    fn remove(&self, task: *const SchedTask) {
        if let Ok(mut tasks) = self.tasks.lock() {
            tasks.retain(|&t| t != task);
        }
    }

    /// Interrupt all sleeping tasks
    ///
    /// Called by the IRQ handler
    fn interrupt_all(&self) {
        if let Ok(tasks) = self.tasks.lock() {
            for &task_ptr in tasks.iter() {
                // SAFETY: The task pointer is valid because we only add valid pointers
                // and remove them when the task is done sleeping
                unsafe {
                    if let Some(task) = task_ptr.as_ref() {
                        let _ = task.interrupt();
                    }
                }
            }
        }
    }
}

// SAFETY: TaskList only stores raw pointers which are accessed under a lock
unsafe impl Send for TaskList {}
unsafe impl Sync for TaskList {}

/// Global static task list
static TASKS: TaskList = TaskList::new();

/// IRQ handler for the scheduler
///
/// Corresponds to `sched_irq_handler()` in sched.c
/// This function interrupts all sleeping tasks when a signal is received.
pub fn sched_irq_handler(_irq: u32, _arg: Option<&()>) {
    TASKS.interrupt_all();
}

/// Initialize the scheduler
///
/// Corresponds to `sched_init()` in sched.c
///
/// In the C version, this registers an IRQ handler. In Rust, the IRQ
/// registration would be done separately through the interrupt module.
pub fn sched_init() -> Result<()> {
    // In C version: intr_register(INTR_IRQ_USER, sched_irq_handler, 0, NULL)
    // The interrupt registration should be done separately
    log::info!("Scheduler initialized");
    Ok(())
}

/// Run the scheduler
///
/// Corresponds to `sched_run()` in sched.c
pub fn sched_run() -> Result<()> {
    // Do nothing - same as C version
    Ok(())
}

/// Shutdown the scheduler
///
/// Corresponds to `sched_shutdown()` in sched.c
pub fn sched_shutdown() -> Result<()> {
    // Do nothing - same as C version
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::thread;
    use std::time::{Duration, Instant};

    #[test]
    fn test_sched_task_new() {
        let task = SchedTask::new();
        assert!(task.can_destroy().is_ok());
    }

    #[test]
    fn test_sched_task_wakeup() {
        let task = Arc::new(SchedTask::new());

        let task_clone = Arc::clone(&task);

        let handle = thread::spawn(move || {
            // This will block until wakeup is called
            let result = task_clone.sleep(Some(Duration::from_secs(5)));
            // Should be Ok (woken up before timeout)
            assert!(result.is_ok());
        });

        // Give the thread time to start sleeping
        thread::sleep(Duration::from_millis(100));

        // Wake up the sleeping thread
        task.wakeup();

        // Wait for the thread to finish
        handle.join().unwrap();
    }

    #[test]
    fn test_sched_task_timeout() {
        let task = Arc::new(SchedTask::new());

        let task_clone = Arc::clone(&task);

        let handle = thread::spawn(move || {
            let start = Instant::now();
            let result = task_clone.sleep(Some(Duration::from_millis(100)));
            let elapsed = start.elapsed();

            // Should timeout
            assert!(matches!(result, Err(SchedError::Timeout)));
            // Should have waited approximately 100ms
            assert!(elapsed >= Duration::from_millis(90));
            assert!(elapsed < Duration::from_millis(200));
        });

        handle.join().unwrap();
    }

    #[test]
    fn test_sched_task_with_external_lock() {
        let task = Arc::new(SchedTask::new());
        let data = Arc::new(Mutex::new(0u32));

        let task_clone = Arc::clone(&task);
        let data_clone = Arc::clone(&data);

        let handle = thread::spawn(move || {
            // This will block until wakeup is called
            let result = task_clone.sleep_with_lock(&data_clone, Some(Duration::from_secs(5)));
            // Should be Ok (woken up before timeout)
            assert!(result.is_ok());
        });

        // Give the thread time to start sleeping
        thread::sleep(Duration::from_millis(100));

        // Wake up the sleeping thread
        task.wakeup();

        // Wait for the thread to finish
        handle.join().unwrap();
    }

    #[test]
    fn test_sched_init_run_shutdown() {
        assert!(sched_init().is_ok());
        assert!(sched_run().is_ok());
        assert!(sched_shutdown().is_ok());
    }
}
