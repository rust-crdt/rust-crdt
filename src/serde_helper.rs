use serde::{de::DeserializeOwned, Serialize};

pub trait SerDe: Serialize + DeserializeOwned {}
impl<T: Serialize + DeserializeOwned> SerDe for T {}

pub(crate) mod btreemap_as_vec {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    use std::collections::BTreeMap;

    pub(crate) fn serialize<S, K, V>(v: &BTreeMap<K, V>, s: S) -> Result<S::Ok, S::Error>
    where
        K: Serialize,
        V: Serialize,
        S: Serializer,
    {
        let vec = Vec::from_iter(v.iter());
        vec.serialize(s)
    }

    pub(crate) fn deserialize<'de, D, K, V>(deserializer: D) -> Result<BTreeMap<K, V>, D::Error>
    where
        D: Deserializer<'de>,
        K: Deserialize<'de> + Ord,
        V: Deserialize<'de>,
    {
        let vec: Vec<(K, V)> = Vec::deserialize(deserializer)?;
        Ok(vec.into_iter().collect())
    }
}
