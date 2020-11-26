use std::{error, fmt, result};

/// CRDT Result alias to reduce redundency in function return types
pub(crate) type Result<T> = result::Result<T, Error>;

/// Possible CRDT error codes
#[derive(Debug, PartialEq)]
pub enum Error {
    /// A conflicting change to a CRDT is witnessed by a dot that already exists.
    ///
    /// We don't always check for this error case as it can be fairly expensive.
    /// Instead, users must design their system in a way that will make these
    /// dot collisions unlikely / impossible.
    ConflictingMarker,
}

impl error::Error for Error {
    fn description(&self) -> &str {
        match self {
            Error::ConflictingMarker => "Dot's are used exactly once for the lifetime of a CRDT",
        }
    }

    fn cause(&self) -> Option<&dyn error::Error> {
        match self {
            Error::ConflictingMarker => None,
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::ConflictingMarker => write!(f, "Conflicting Marker"),
        }
    }
}
