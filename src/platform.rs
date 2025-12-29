//! Platform abstraction layer for Linux
//!
//! This module provides platform-specific functionality corresponding to
//! microps/platform/linux/platform.c

use std::sync::{Mutex, MutexGuard};

use rand::Rng;

/// Error type for platform operations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PlatformError {
    InitializationFailed,
    LockError,
    AlreadyInitialized,
    NotInitialized,
}

impl std::fmt::Display for PlatformError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PlatformError::InitializationFailed => write!(f, "Platform initialization failed"),
            PlatformError::LockError => write!(f, "Lock operation failed"),
            PlatformError::AlreadyInitialized => write!(f, "Platform already initialized"),
            PlatformError::NotInitialized => write!(f, "Platform not initialized"),
        }
    }
}

impl std::error::Error for PlatformError {}

pub type Result<T> = std::result::Result<T, PlatformError>;


/// Initialize the platform
pub fn platform_init() -> Result<()> {
    // 自動初期化されるため、何もしない()
    Ok(())
}

/// Run the platform main loop
pub fn platform_run() -> Result<()> {
    Ok(())
}

/// Shutdown the platform
pub fn platform_shutdown() -> Result<()> {
    Ok(())
}

/*
 * Lock abstraction
 *
 * In C version: typedef pthread_mutex_t lock_t;
 * In Rust: We use std::sync::Mutex<T>
 */

/// A wrapper around Mutex that provides an API similar to the C version
///
/// Note: In Rust, Mutex is generic over the protected data type,
/// which provides better safety than raw pthread_mutex_t.
#[derive(Debug)]
pub struct Lock<T> {
    inner: Mutex<T>,
}

impl<T> Lock<T> {
    /// Create a new lock with the given initial value
    ///
    /// Corresponds to `lock_init()` in platform.c
    pub const fn new(value: T) -> Self {
        Self {
            inner: Mutex::new(value),
        }
    }

    /// Acquire the lock and return a guard
    ///
    /// Corresponds to `lock_acquire()` in platform.c
    /// Returns a guard that automatically releases the lock when dropped.
    pub fn acquire(&self) -> Result<MutexGuard<'_, T>> {
        self.inner.lock().map_err(|_| PlatformError::LockError)
    }

    /// Try to acquire the lock without blocking
    pub fn try_acquire(&self) -> Result<MutexGuard<'_, T>> {
        self.inner.try_lock().map_err(|_| PlatformError::LockError)
    }

    // Note: lock_release() is handled automatically by dropping the MutexGuard
}

impl<T: Default> Default for Lock<T> {
    fn default() -> Self {
        Self::new(T::default())
    }
}

/// Generate a random 16-bit unsigned integer
pub fn random16() -> u16 {
    rand::rng().random::<u16>()
}
