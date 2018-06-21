use std::{self, fmt};

/// CRDT Result alias to reduce redundency in function return types
pub type Result<T> = std::result::Result<T, Error>;

/// Possible CRDT error codes
#[derive(Debug, PartialEq)]
pub enum Error {
    /// This error will happen when mutations to a CRDT are witnessed by a
    /// dot that already exists
    ConflictingDot
}

impl std::error::Error for Error {
    fn description(&self) -> &str {
        match self {
            Error::ConflictingDot =>
                "Dot's are expected to be used exactly once for the lifetime of a CRDT"
        }
    }
    fn cause(&self) -> Option<&std::error::Error> {
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
