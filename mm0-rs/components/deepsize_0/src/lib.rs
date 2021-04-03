//! A utility for recursively measuring the size of an object
//!
//! This is an adaptation of the [`deepsize`](https://docs.rs/deepsize) crate,
//! Copyright (c) 2019 Aeledfyr, which is MIT licensed (see the LICENSE file
//! in this directory).

extern crate self as deepsize_0;

use std::mem::{size_of, size_of_val};
use std::sync::Arc;
use std::rc::Rc;
use std::collections::HashSet;
use deepsize_derive::DeepSizeOf;


/// A trait for measuring the size of an object and its children
///
/// In many cases this is just `std::mem::size_of::<T>()`, but if
/// the struct contains a `Vec`, `String`, `Box`, or other allocated object or
/// reference, then it is the size of the struct, plus the size of the contents
/// of the object.
pub trait DeepSizeOf {
    /// Returns an estimation of a total size of memory owned by the
    /// object, including heap-managed storage.
    ///
    /// This is an estimation and not a precise result, because it
    /// doesn't account for allocator's overhead.
    fn deep_size_of(&self) -> usize {
        self.deep_size_of_with(&mut Context::default())
    }

    /// Returns an estimation of a total size of memory owned by the
    /// object, including heap-managed storage.
    fn deep_size_of_with(&self, context: &mut Context) -> usize {
        size_of_val(self) + self.deep_size_of_children(context)
    }

    /// Returns an estimation of the heap-managed storage of this object.
    /// This does not include the size of the object itself.
    ///
    /// This is an estimation and not a precise result, because it
    /// doesn't account for allocator's overhead.
    ///
    /// This is an internal function (this shouldn't be called directly),
    /// and requires a [`Context`](Context) to track visited references.
    /// Implementations of this function should only call `deep_size_of_children`,
    /// and not `deep_size_of` so that they reference tracking is not reset.
    ///
    /// In all other cases, `deep_size_of` should be called instead of this function.
    ///
    /// If a struct and all of its children do not allocate or have references,
    /// this method should return `0`, as it cannot have any heap allocated
    /// children.  There is a shortcut macro for this implementation, [`known_size_of`](known_size_of),
    /// used like `known_deep_size!(0, (), u32, u64);` which generates the impls.
    ///
    /// The most common way to use this method, and how the derive works,
    /// is to call this method on each of the structs members and sum the
    /// results, which works as long as all members of the struct implmeent
    /// `DeepSizeOf`.
    ///
    /// To implement this for a collection type, you should sum the deep sizes of
    /// the items of the collection and then add the size of the allocation of the
    /// collection itself.  This can become much more complicated if the collection
    /// has multiple seperate allocations.
    ///
    /// Here is an example from the implementation of `DeepSizeOf` for `Vec<T>`
    /// ```rust, ignore
    /// # use deepsize::{DeepSizeOf, Context};
    /// impl<T> DeepSizeOf for std::vec::Vec<T> where T: DeepSizeOf {
    ///     fn deep_size_of_children(&self, context: &mut Context) -> usize {
    ///         // Size of heap allocations for each child
    ///         self.iter().map(|child| child.deep_size_of_children(context)).sum()
    ///          + self.capacity() * std::mem::size_of::<T>()  // Size of Vec's heap allocation
    ///     }
    /// }
    /// ```
    fn deep_size_of_children(&self, context: &mut Context) -> usize;
}

/// The context of which references have already been seen.
///
/// Keeps track of the `Arc`s, `Rc`s, and references
/// that have been visited, so that `Arc`s and other references
/// aren't double counted.
///
/// This must be passed between `deep_size_of_children` calls when
/// recursing, so that references are not double-counted.
#[derive(Debug, Default)]
pub struct Context {
    /// A set of all `Arcs` that have already been counted
    arcs: HashSet<usize>,
    /// A set of all `Rcs` that have already been counted
    rcs: HashSet<usize>,
}

impl Context {
    /// Adds an `Arc` to the list of visited `Arc`s
    fn add_arc<T: ?Sized>(&mut self, arc: &Arc<T>) {
        // Somewhat unsafe way of getting a pointer to the inner `ArcInner`
        // object without changing the count
        let pointer: usize = unsafe { *<*const _>::cast(arc) };
        self.arcs.insert(pointer);
    }
    /// Checks if an `Arc` is in the list visited `Arc`s
    fn contains_arc<T: ?Sized>(&self, arc: &Arc<T>) -> bool {
        let pointer: usize = unsafe { *<*const _>::cast(arc) };
        self.arcs.contains(&pointer)
    }

    /// Adds an `Rc` to the list of visited `Rc`s
    fn add_rc<T: ?Sized>(&mut self, rc: &Rc<T>) {
        // Somewhat unsafe way of getting a pointer to the inner `RcBox`
        // object without changing the count
        let pointer: usize = unsafe { *<*const _>::cast(rc) };
        self.rcs.insert(pointer);
    }
    /// Checks if an `Rc` is in the list visited `Rc`s
    fn contains_rc<T: ?Sized>(&self, rc: &Rc<T>) -> bool {
        let pointer: usize = unsafe { *<*const _>::cast(rc) };
        self.rcs.contains(&pointer)
    }

    fn deep_size_of_arc<T: ?Sized>(&mut self, arc: &Arc<T>, f: impl FnOnce(&T, &mut Self) -> usize) -> usize {
        if self.contains_arc(arc) {
            0
        } else {
            self.add_arc(arc);
            f(&*arc, self)
        }
    }

    fn deep_size_of_rc<T: ?Sized>(&mut self, rc: &Rc<T>, f: impl FnOnce(&T, &mut Self) -> usize) -> usize {
        if self.contains_rc(rc) {
            0
        } else {
            self.add_rc(rc);
            f(&*rc, self)
        }
    }
}

impl<T: DeepSizeOf> DeepSizeOf for Vec<T> {
    fn deep_size_of_children(&self, context: &mut Context) -> usize {
        // Deep size of children
        self.iter().map(|child| child.deep_size_of_children(context)).sum::<usize>()
         + self.capacity() * size_of::<T>()
        // Size of unused capacity
    }
}

impl<T: DeepSizeOf> DeepSizeOf for std::collections::VecDeque<T> {
    fn deep_size_of_children(&self, context: &mut Context) -> usize {
        // Deep size of children
        self.iter().map(|child| child.deep_size_of_children(context)).sum::<usize>()
         + self.capacity() * size_of::<T>()  // Size of Vec's heap allocation
    }
}

impl<K: DeepSizeOf, V: DeepSizeOf, S> DeepSizeOf for std::collections::HashMap<K, V, S> {
    // FIXME
    // How much more overhead is there to a hashmap? The docs say it is
    // essentially just a Vec<Option<(u64, K, V)>>
    // Update this to work for hashbrown::HashMap
    fn deep_size_of_children(&self, context: &mut Context) -> usize {
        self.iter()
            .fold(0, |sum, (key, val)| {
                sum + key.deep_size_of_children(context)
                    + val.deep_size_of_children(context)
            })
         + self.capacity() * size_of::<Option<(u64, K, V)>>()
        // Size of container capacity
    }
}

impl<T: DeepSizeOf, S> DeepSizeOf for std::collections::HashSet<T, S> {
    fn deep_size_of_children(&self, context: &mut Context) -> usize {
        self.iter()
            .fold(0, |sum, item| sum + item.deep_size_of_children(context))
            + self.capacity() * size_of::<Option<(u64, T, ())>>()
        // Size container storage
    }
}

impl<K: Ord + DeepSizeOf, V: DeepSizeOf> DeepSizeOf for std::collections::BTreeMap<K, V> {
    fn deep_size_of_children(&self, context: &mut Context) -> usize {
        // A btree node has 2B-1 (K,V) pairs and (usize, u32) overhead,
        // and an internal btree node additionally has 2B usize overhead.
        // A node can contain between B-1 and 2B-1 elements, so we assume
        // it has the midpoint 3/2 B - 1.
        const B: usize = 6;
        const MIN: usize = 2 * B - 1;
        const MAX: usize = B - 1;
        let node_overhead = size_of::<(usize, u32, [(K, V); MAX], [usize; B])>();
        let internal: usize = self.iter().map(|(key, val)|
            key.deep_size_of_children(context) +
            val.deep_size_of_children(context)).sum();
        #[allow(clippy::integer_division)]
        { internal + self.len() * node_overhead * 2 / (MAX + MIN) }
    }
}

impl<T: DeepSizeOf + ?Sized> DeepSizeOf for Box<T> {
    fn deep_size_of_children(&self, context: &mut Context) -> usize {
        // May cause inacuracies, measures size of the value, but not the allocation size
        let val: &T = &*self;
        size_of_val(val) + val.deep_size_of_children(context)
    }
}


impl<T: DeepSizeOf + ?Sized> DeepSizeOf for Arc<T> {
    fn deep_size_of_children(&self, context: &mut Context) -> usize {
        context.deep_size_of_arc(self, |val, context| val.deep_size_of_with(context))
    }
}

impl<T: DeepSizeOf + ?Sized> DeepSizeOf for Rc<T> {
    fn deep_size_of_children(&self, context: &mut Context) -> usize {
        context.deep_size_of_rc(self, |val, context| val.deep_size_of_with(context))
    }
}

impl<T: DeepSizeOf> DeepSizeOf for [T] {
    fn deep_size_of_children(&self, context: &mut Context) -> usize {
        self.iter().map(|child| child.deep_size_of_children(context)).sum()
    }
}
impl<O: DeepSizeOf, T: ?Sized> DeepSizeOf for owning_ref::OwningRef<O, T> {
    fn deep_size_of_children(&self, context: &mut Context) -> usize {
        self.as_owner().deep_size_of_children(context)
    }
}


/// A macro to generate an impl for types with no inner allocation.
#[macro_export]
macro_rules! deep_size_0 {
    ($($({$($gen:tt)*})? $type:ty),+) => {
        $($crate::deep_size_0!(@IMPL $({$($gen)*})? $type);)+
    };
    (@IMPL $type:ty) => {
        $crate::deep_size_0!(@GO {} $type);
    };
    (@IMPL {$($gen:tt)*} $type:ty) => {
        $crate::deep_size_0!(@GO {$($gen)*} $type);
    };
    (@GO {!Copy $($($gen:tt)+)?} $type:ty) => {
        impl$(<$($gen)+>)? $crate::DeepSizeOf for $type {
            #[inline(always)]
            fn deep_size_of_children(&self, _: &mut $crate::Context) -> usize { 0 }
        }
    };
    (@GO {$($($gen:tt)+)?} $type:ty) => {
        const _: fn() = || {
            fn assert_copy<T: ?Sized + Copy>() {}
            fn go$(<$($gen)+>)?() {assert_copy::<$type>()}
        };
        $crate::deep_size_0!(@GO {!Copy $($($gen)+)?} $type);
    };
}

use std::sync::atomic;
deep_size_0!(
    u8, u16, u32, u64, usize, i8, i16, i32, i64, isize,
    bool, char, f32, f64, (), {!Copy} str,
    {!Copy} atomic::AtomicBool, {!Copy} atomic::AtomicIsize, {!Copy} atomic::AtomicUsize,
    {T: ?Sized} &T,
    {!Copy T} std::cell::Cell<T>,
    {!Copy T} std::rc::Weak<T>,
    {!Copy T} std::mem::MaybeUninit<T>,
    {T: ?Sized} core::marker::PhantomData<T>,
    {!Copy} dyn std::error::Error + Send + Sync,
    {!Copy T} futures::channel::oneshot::Sender<T>
);

impl DeepSizeOf for String {
    fn deep_size_of_children(&self, _: &mut Context) -> usize { self.capacity() }
}

impl<T: DeepSizeOf> DeepSizeOf for Option<T> {
    fn deep_size_of_children(&self, context: &mut Context) -> usize {
        match self {
            Some(t) => t.deep_size_of_children(context),
            None => 0,
        }
    }
}

impl<R: DeepSizeOf, E: DeepSizeOf> DeepSizeOf for core::result::Result<R, E> {
    fn deep_size_of_children(&self, context: &mut Context) -> usize {
        match self {
            Ok(r)  => r.deep_size_of_children(context),
            Err(e) => e.deep_size_of_children(context),
        }
    }
}

macro_rules! deep_size_array {
    ($($num:tt)*) => {
        $(
            impl<T: DeepSizeOf> DeepSizeOf for [T; $num] {
                fn deep_size_of_children(&self, context: &mut Context) -> usize {
                    self.as_ref().deep_size_of_children(context)
                }
            }
        )*
    };
}

deep_size_array!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32);

macro_rules! deep_size_tuple {
    (@TUPLE $($n:tt $T:ident)+) => {
        impl<$($T: DeepSizeOf,)+> DeepSizeOf for ($($T,)+) {
            fn deep_size_of_children(&self, context: &mut Context) -> usize {
                0 $( + self.$n.deep_size_of_children(context))+
            }
        }
    };
    (($($args:tt)*)) => {};
    (($($args:tt)*) $n0:tt $T0:ident $($rest:tt)*) => {
        deep_size_tuple!(@TUPLE $($args)* $n0 $T0);
        deep_size_tuple!(($($args)* $n0 $T0) $($rest)*);
    };
}

deep_size_tuple!(() 0 A 1 B 2 C 3 D 4 E 5 F 6 G 7 H 8 I 9 J);

impl DeepSizeOf for std::path::PathBuf {
    fn deep_size_of_children(&self, _: &mut Context) -> usize { self.capacity() }
}

impl DeepSizeOf for num::BigUint {
    fn deep_size_of_children(&self, _: &mut Context) -> usize {
        unsafe { &*<*const _>::cast::<Vec<u32>>(self) }.capacity()
    }
}

impl DeepSizeOf for num::BigInt {
    fn deep_size_of_children(&self, context: &mut Context) -> usize {
        self.magnitude().deep_size_of_children(context)
    }
}

impl DeepSizeOf for lsp_types::Url {
    fn deep_size_of_children(&self, _: &mut Context) -> usize {
        // this is an underestimate, but Url doesn't expose its capacity
        self.as_str().len()
    }
}

impl<T: DeepSizeOf> DeepSizeOf for std::cell::RefCell<T> {
    fn deep_size_of_children(&self, context: &mut Context) -> usize {
        if let Ok(g) = self.try_borrow() {
            (*g).deep_size_of_with(context)
        } else {0}
    }
}

impl<T: DeepSizeOf> DeepSizeOf for std::sync::Mutex<T> {
    fn deep_size_of_children(&self, context: &mut Context) -> usize {
        if let Ok(g) = self.try_lock() {
            (*g).deep_size_of_with(context)
        } else {0}
    }
}

impl<T: DeepSizeOf> DeepSizeOf for futures::lock::Mutex<T> {
    fn deep_size_of_children(&self, context: &mut Context) -> usize {
        if let Some(g) = self.try_lock() {
            (*g).deep_size_of_with(context)
        } else {0}
    }
}

impl<T: DeepSizeOf> DeepSizeOf for typed_arena::Arena<T> {
    fn deep_size_of_children(&self, context: &mut Context) -> usize {
        #[derive(DeepSizeOf)]
        struct Arena<T> {
            _chunks: std::cell::RefCell<ChunkList<T>>,
        }
        #[derive(DeepSizeOf)]
        struct ChunkList<T> {
            _current: Vec<T>,
            _rest: Vec<Vec<T>>,
        }
        #[allow(clippy::transmute_ptr_to_ptr)]
        let this: &Arena<T> = unsafe {std::mem::transmute(self)};
        this.deep_size_of_children(context)
    }
}

impl DeepSizeOf for memmap::Mmap {
    fn deep_size_of_children(&self, _: &mut Context) -> usize { size_of_val(&**self) }
}