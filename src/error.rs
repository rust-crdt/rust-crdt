use std::{fmt, error, result};

/// CRDT Result alias to reduce redundency in function return types
pub type Result<T> = result::Result<T, Error>;

/// Possible CRDT error codes
#[derive(Debug, PartialEq)]
pub enum Error {
    /// A conflicting change to a CRDT is witnessed by a dot that already exists.
    /// We don't always check for this error class as it can be fairly expensive.
    /// Instead, users must design their system in a way that will make these
    /// dot collisions unlikely.
    ConflictingDot
}

impl error::Error for Error {
    fn description(&self) -> &str {
        match self {
            Error::ConflictingDot =>
                "Dot's are used exactly once for the lifetime of a CRDT"
        }
    }
    fn cause(&self) -> Option<&error::Error> {
        match self {
            Error::ConflictingDot => None,
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::ConflictingDot => {
                use std::error::Error;
                write!(f, "{}", self.description())
            }
        }
    }
}
