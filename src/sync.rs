use std::{
    collections::BTreeMap,
    fmt::Debug,
    ops::{Deref, DerefMut},
};

use crossbeam_skiplist::SkipMap;
use serde::{ser::SerializeMap, Deserialize, Serialize};

use crate::{Identifier, OrdDot};

pub struct SyncMap<K, V>(SkipMap<K, V>);

impl<K, V> SyncMap<K, V> {
    pub fn new() -> Self {
        Self(SkipMap::new())
    }
}

impl<K, V> Debug for SyncMap<K, V>
where
    SkipMap<K, V>: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl<K, V> Default for SyncMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Deref for SyncMap<K, V> {
    type Target = SkipMap<K, V>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<K, V> DerefMut for SyncMap<K, V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<K: Ord + Serialize, V: Serialize> Serialize for SyncMap<K, V> {
    fn serialize<S: serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        let mut m = s.serialize_map(Some(self.0.len()))?;
        for e in self.0.iter() {
            m.serialize_entry(e.value(), e.value())?;
        }
        m.end()
    }
}

impl<'de, K, V> Deserialize<'de> for SyncMap<K, V>
where
    K: Ord + Deserialize<'de> + Send + 'static,
    V: Deserialize<'de> + Send + 'static,
{
    fn deserialize<D>(d: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let m = BTreeMap::<K, V>::deserialize(d)?;
        Ok(Self::from(m))
    }
}

impl<K: Ord + Send + 'static, V: Send + 'static> From<BTreeMap<K, V>> for SyncMap<K, V> {
    fn from(m: BTreeMap<K, V>) -> Self {
        let map = SkipMap::new();
        for (k, v) in m {
            map.insert(k, v);
        }
        Self(map)
    }
}

impl<K, V> Clone for SyncMap<K, V>
where
    K: Clone + Ord + Send + 'static,
    V: Clone + Send + 'static,
{
    fn clone(&self) -> Self {
        let map = SkipMap::new();
        for e in self.iter() {
            map.insert(e.key().clone(), e.value().clone());
        }
        Self(map)
    }
}

impl<K, V> PartialEq for SyncMap<K, V>
where
    K: Ord,
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len()
            && self.iter().all(|x| {
                if let Some(y) = other.get(x.key()) {
                    x.value() == y.value()
                } else {
                    false
                }
            })
    }
}

impl<K, V> FromIterator<(K, V)> for SyncMap<K, V>
where
    K: Ord + Send + 'static,
    V: Send + 'static,
{
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let map = SkipMap::new();
        for (k, v) in iter {
            map.insert(k, v);
        }
        Self(map)
    }
}

impl<K, V> Eq for SyncMap<K, V>
where
    K: Ord,
    V: Eq,
{
}

impl<K, V> IntoIterator for SyncMap<K, V>
where
    K: Ord + 'static,
    V: 'static,
{
    type IntoIter = crossbeam_skiplist::map::IntoIter<K, V>;
    type Item = (K, V);

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

/// A wrapper around a crossbeam-skiplist map entry that can be used to access
/// the underlying data.
pub struct ListEntry<'a, A: Ord, T>(crossbeam_skiplist::map::Entry<'a, Identifier<OrdDot<A>>, T>);

impl<'a, A: Ord, T> From<crossbeam_skiplist::map::Entry<'a, Identifier<OrdDot<A>>, T>>
    for ListEntry<'a, A, T>
{
    fn from(e: crossbeam_skiplist::map::Entry<'a, Identifier<OrdDot<A>>, T>) -> Self {
        Self(e)
    }
}
impl<'a, A: Ord, T> Deref for ListEntry<'a, A, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.0.value()
    }
}
