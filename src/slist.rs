//! # Synced List

use core::{fmt, iter::FromIterator};

use crossbeam_skiplist::{map::Entry, SkipMap};
use num::BigRational;
use serde::{Deserialize, Serialize};

use crate::{CmRDT, Dot, Identifier, OrdDot, SVClock, SyncedCmRDT};

/// As described in the module documentation:
///
/// A List is a CRDT for storing sequences of data (Strings, ordered lists).
/// It provides an efficient view of the stored sequence, with fast index,
/// insertion and deletion operations.
#[derive(Debug)]
pub struct SList<T, A: Ord> {
    seq: SkipMap<Identifier<OrdDot<A>>, T>,
    clock: SVClock<A>,
}

/// Operations that can be performed on a List
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Op<T, A: Ord> {
    /// Insert an element
    Insert {
        /// The Identifier to insert at
        id: Identifier<OrdDot<A>>,
        /// Element to insert
        val: T,
    },
    /// Delete an element
    Delete {
        /// The Identifier of the insertion we're removing
        id: Identifier<OrdDot<A>>,
        /// id of site that issued delete
        dot: Dot<A>,
    },
}

impl<T, A: Ord + Clone + Eq> Op<T, A> {
    /// Returns the Identifier this operation is concerning.
    pub fn id(&self) -> &Identifier<OrdDot<A>> {
        match self {
            Op::Insert { id, .. } | Op::Delete { id, .. } => id,
        }
    }

    /// Return the Dot originating the operation.
    pub fn dot(&self) -> Dot<A> {
        match self {
            Op::Insert { id, .. } => id.value().clone().into(),
            Op::Delete { dot, .. } => dot.clone(),
        }
    }
}

impl<T, A: Ord> Default for SList<T, A> {
    fn default() -> Self {
        Self {
            seq: Default::default(),
            clock: Default::default(),
        }
    }
}

impl<T, A: Ord> SList<T, A> {
    /// Get the length of the List.
    pub fn len(&self) -> usize {
        self.seq.len()
    }

    /// Check if the List is empty.
    pub fn is_empty(&self) -> bool {
        self.seq.is_empty()
    }

    /// Get each elements identifier and value from the List.
    pub fn iter_entries(&self) -> impl Iterator<Item = Entry<'_, Identifier<OrdDot<A>>, T>> {
        self.seq.iter()
    }

    /// Get the first Entry of the sequence represented by the List.
    pub fn first_entry(&self) -> Option<Entry<'_, Identifier<OrdDot<A>>, T>> {
        self.seq.iter().next()
    }

    /// Get the last Entry of the sequence represented by the List.
    pub fn last_entry(&self) -> Option<Entry<'_, Identifier<OrdDot<A>>, T>> {
        self.seq.iter().rev().next()
    }
}

impl<T, A: Ord + Clone> SList<T, A> {
    /// Create an empty List
    pub fn new() -> Self {
        Self::default()
    }

    /// Generate an op to insert the given element with given id.
    pub fn insert_id(&self, id: impl Into<BigRational>, val: T, actor: A) -> Op<T, A> {
        let dot = self.clock.inc(actor);
        let id = Identifier::new(id, dot.into());
        Op::Insert { id, val }
    }

    /// Create an op to insert an element at the end of the sequence.
    pub fn append(&self, c: T, actor: A) -> Op<T, A> {
        let ix = self.seq.len();
        self.insert_index(ix, c, actor)
    }

    /// Create an op to delete the element at the given index.
    ///
    /// Returns None if `ix` is out of bounds, i.e. `ix > self.len()`.
    pub fn delete_index(&self, ix: usize, actor: A) -> Option<Op<T, A>> {
        self.seq.iter().nth(ix).map(|id| {
            let id = id.key().clone();
            let dot = self.clock.inc(actor);
            Op::Delete { id, dot }
        })
    }

    /// Generate an op to insert the given element at the given index.
    /// If `ix` is greater than the length of the List then it is appended to
    /// the end.
    pub fn insert_index(&self, mut ix: usize, val: T, actor: A) -> Op<T, A> {
        ix = ix.min(self.seq.len());
        // TODO: replace this logic with BTreeMap::range()
        let (prev, next) = match ix.checked_sub(1) {
            Some(indices_to_drop) => {
                let mut indices = self
                    .seq
                    .iter()
                    .skip(indices_to_drop)
                    .map(|id| id.key().clone());
                (indices.next(), indices.next())
            }
            None => {
                // Inserting at the front of the list
                let mut indices = self.seq.iter().map(|id| id.key().clone());
                (None, indices.next())
            }
        };

        let dot = self.clock.inc(actor);
        let id = Identifier::between(prev.as_ref(), next.as_ref(), dot.into());
        Op::Insert { id, val }
    }

    /// Generate an op to insert the given element at the given index with
    /// random offset being added to the id. If `ix` is greater than the
    /// length of the List then it is appended to the end.
    #[cfg(feature = "num_rand")]
    pub fn insert_index_with_randomness(&self, mut ix: usize, val: T, actor: A) -> Op<T, A> {
        ix = ix.min(self.seq.len());
        // TODO: replace this logic with BTreeMap::range()
        let (prev, next) = match ix.checked_sub(1) {
            Some(indices_to_drop) => {
                let mut indices = self
                    .seq
                    .iter()
                    .skip(indices_to_drop)
                    .map(|id| id.key().clone());
                (indices.next(), indices.next())
            }
            None => {
                // Inserting at the front of the list
                let mut indices = self.seq.iter().map(|id| id.key().clone());
                (None, indices.next())
            }
        };

        let dot = self.clock.inc(actor);
        let id = Identifier::between_with_randomness(prev.as_ref(), next.as_ref(), dot.into());
        Op::Insert { id, val }
    }

    /// Read the List into a container of your choice
    ///
    /// ```rust
    /// use crdts::{CmRDT, List};
    ///
    /// let mut list = List::new();
    /// list.apply(list.append('a', 'A'));
    /// list.apply(list.append('b', 'A'));
    /// list.apply(list.append('c', 'A'));
    /// assert_eq!(list.read::<String>(), "abc");
    /// ```
    pub fn read<'a, C: FromIterator<T>>(&'a self) -> C
    where
        T: Clone,
    {
        self.seq.iter().map(|id| id.value().clone()).collect()
    }

    /// Read the List into a container of your choice, consuming it.
    ///
    /// ```rust
    /// use crdts::{CmRDT, List};
    ///
    /// let mut list = List::new();
    /// list.apply(list.append(1, 'A'));
    /// list.apply(list.append(2, 'A'));
    /// list.apply(list.append(3, 'A'));
    /// assert_eq!(list.read_into::<Vec<_>>(), vec![1, 2, 3]);
    /// ```
    pub fn read_into<C: FromIterator<T>>(self) -> C {
        self.seq.into_iter().map(|(_, v)| v).collect()
    }
}

impl<T: Clone, A: Ord> SList<T, A> {
    /// Get the elements represented by the List.
    pub fn iter(&self) -> impl Iterator<Item = T> + '_ {
        self.seq.iter().map(|id| id.value().clone())
    }

    /// Get an element at a position in the sequence represented by the List.
    pub fn position(&self, ix: usize) -> Option<T> {
        self.iter().nth(ix).clone()
    }

    /// Finds an element by its Identifier.
    pub fn get(&self, id: &Identifier<OrdDot<A>>) -> Option<T> {
        self.seq.get(id).map(|x| x.value().clone())
    }

    /// Get first element of the sequence represented by the List.
    pub fn first(&self) -> Option<T> {
        self.first_entry().map(|e| e.value().clone())
    }

    /// Get last element of the sequence represented by the List.
    pub fn last(&self) -> Option<T> {
        self.last_entry().map(|e| e.value().clone())
    }

    /// Insert value with at the given identifier in the List
    fn insert(&self, id: Identifier<OrdDot<A>>, val: T) {
        // Inserts only have an impact if the identifier is not in the tree
        self.seq.get_or_insert(id, val);
    }

    /// Remove the element with the given identifier from the List
    fn delete(&self, id: &Identifier<OrdDot<A>>) -> Option<Entry<Identifier<OrdDot<A>>, T>>
    where
        Identifier<OrdDot<A>>: Send,
        T: Send + 'static,
        A: 'static,
    {
        // Deletes only have an effect if the identifier is already in the tree
        self.seq.remove(id)
    }
}

impl<T, A> CmRDT for SList<T, A>
where
    T: Clone + Send + 'static,
    Identifier<OrdDot<A>>: Send,
    A: Ord + Clone + Send + fmt::Debug + 'static,
{
    type Op = Op<T, A>;
    type Validation = crate::DotRange<A>;

    fn validate_op(&self, op: &Self::Op) -> Result<(), Self::Validation> {
        self.clock.validate_op(&op.dot())
    }

    /// Apply an operation to an List instance.
    ///
    /// If the operation is an insert and the identifier is **already** present
    /// in the List instance the result is a no-op
    ///
    /// If the operation is a delete and the identifier is **not** present in
    /// the List instance the result is a no-op
    fn apply(&mut self, op: Self::Op) {
        (&*self).synced_apply(op)
    }
}

impl<T, A> SyncedCmRDT for SList<T, A>
where
    T: Clone + Send + 'static,
    Identifier<OrdDot<A>>: Send,
    A: Ord + Clone + Send + fmt::Debug + 'static,
{
    fn synced_apply(&self, op: Self::Op) {
        let op_dot = op.dot();

        if op_dot.counter <= self.clock.get(&op_dot.actor) {
            return;
        }

        self.clock.synced_apply(op_dot);
        match op {
            Op::Insert { id, val } => self.insert(id, val),
            Op::Delete { id, .. } => {
                self.delete(&id);
            }
        }
    }
}
