use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::{cell, mem, result, thread, vec};
use std::arch::asm;
use std::collections::{HashMap, HashSet};
use std::collections::linked_list::LinkedList;
use std::hash::{Hash, Hasher};
use std::ptr::null_mut;
use typed_arena::Arena;

struct CovariantLifetime<'id>(PhantomData<&'id ()>);
struct InvariantLifetime<'id>(PhantomData<*mut &'id ()>);
struct ContravariantLifetime<'id>(PhantomData<fn(&'id ()) -> ()>);

pub struct GgToken<'id> {
    _marker: InvariantLifetime<'id>,
}

pub struct Node<T, G> {
    links: HashMap<*mut Node<T, G>, G>,
    value: T,
}

pub struct GenerationalGraph<'id, T, G> {
    nodes: Arena<Node<T, G>>,
    _marker: CovariantLifetime<'id>,
}

pub struct NodeRef<'a, 'id, 'b, T, G> {
    ptr: *mut Node<T, G>,
    _marker1: CovariantLifetime<'a>,
    _marker2: InvariantLifetime<'id>,
    _marker3: ContravariantLifetime<'b>,
}

pub struct LinkHandle<'a, 'c, T, G> {
    source: *mut Node<T, G>,
    dest: *mut Node<T, G>,
    _marker1: InvariantLifetime<'a>,
    _marker2: InvariantLifetime<'c>,
}

pub struct NodeVisit<T, G> {
    ptr: *mut Node<T, G>,
}

impl<T, G> NodeVisit<T, G> {
    fn links(&self) -> &HashMap<&NodeVisit<T, G>, G> {
        unsafe {
            mem::transmute(&(*self.ptr).links)
        }
    }
}

impl<T, G> Hash for NodeVisit<T, G> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_usize(self.ptr as usize)
    }
}

impl<'id, T, G> GenerationalGraph<'id, T, G> {
    // implementazione della new di un network. La chiusura serve per brandizzare il network e tutti i nodi generati da esso
    // e per impedire che essi possano essere utilizzati in metodi di altri network direttamente, il token di autorizzazione
    // invece serve a controllare l'accesso mutabile o immutabile perchè come possiamo notare lo smart pointer richiede un riferimento
    // immutabile per eseguire modifiche mutabili cosa che senza token violerebbe le regole di Rust Safe.
    pub fn new(f: impl for<'a> FnOnce(GenerationalGraph<'a, T, G>, GgToken<'a>) -> ()) {
        f(GenerationalGraph {
            nodes: Arena::new(),
            _marker: CovariantLifetime(PhantomData),
        },
          GgToken {
              _marker: InvariantLifetime(PhantomData),
          })
    }

    // crea un nuovo nodo e ritorna un riferimento mutabile al nodo (riferimento inteso come struttura che permette Deref mutabile)
    pub fn add<'a>(&'a self, val: T, token: &mut GgToken<'id>) -> NodeRef<'a, 'id, 'a, T, G> {
        let node = self.nodes.alloc(
            Node {
                value: val,
                links: HashMap::new(),
            });

        NodeRef {
            ptr: node as *mut Node<T, G>,
            _marker1: CovariantLifetime(PhantomData),
            _marker2: InvariantLifetime(PhantomData),
            _marker3: ContravariantLifetime(PhantomData),
        }
    }

    pub fn visit<R>(&self, root: &NodeRef<'_, '_, '_, T, G> , each: fn(&NodeVisit<T, G>) -> R) {
        unsafe {
            each(mem::transmute(root));
        }
    }

    pub fn visit_multiple<R>(&self, roots: Vec<&NodeRef<'_, '_, '_, T, G>> , each: fn(Vec<&NodeVisit<T, G>>) -> R) {
        unsafe {
            each(mem::transmute(roots));
        }
    }
}

impl<'a, 'id, 'b, T, G> Deref for NodeRef<'a, 'id, 'b, T, G> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &(*self.ptr).value }
    }
}

impl<'a, 'id, 'b, T, G> DerefMut for NodeRef<'a, 'id, 'b, T, G> {
    
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut (*self.ptr).value }
    }
}

impl<'a, 'id, 'b, T, G> NodeRef<'a, 'id, 'b, T, G> {
    pub fn link(&mut self, other: &NodeRef<'a, 'id, '_, T, G>, cost: G) {
        unsafe { (*self.ptr).links.insert(other.ptr, cost); }
    }

    pub fn link_outer(&mut self, other: &NodeRef<'a, '_, '_, T, G>, cost: G) {
        unsafe { (*self.ptr).links.insert(other.ptr, cost); }
    }

    pub fn link_inner<'c>(&mut self, other: &NodeRef<'c, '_, 'a, T, G>, cost: G) -> LinkHandle<'a, 'c, T, G> {
        unsafe {
            (*self.ptr).links.insert(other.ptr, cost);

            LinkHandle {
                source: self.ptr,
                dest: other.ptr,
                _marker1: InvariantLifetime(PhantomData),
                _marker2: InvariantLifetime(PhantomData),
            }
        }
    }

    pub fn unlink(&mut self, other: &NodeRef<'_, '_, '_, T, G>) {
        unsafe { (*self.ptr).links.remove(&other.ptr); }
    }

    pub fn weight_of<'w>(&'w self, dest: usize) -> Option<&'w G> {
        unsafe {
            (*self.ptr).links.get(&(dest as *mut Node<T, G>))
        }
    }

    pub fn weight_of_mut<'w>(&'w mut self, dest: usize) -> Option<&'w mut G> {
        unsafe {
            (*self.ptr).links.get_mut(&(dest as *mut Node<T, G>))
        }
    }

    pub fn link_self(&mut self, cost: G) {
        unsafe {
            (*self.ptr).links.insert(self.ptr, cost);
        }
    }

    pub fn unlink_self(&mut self) {
        unsafe {
            (*self.ptr).links.remove(&self.ptr);
        }
    }
}

impl<'a, 'c, T, G> Drop for LinkHandle<'a, 'c, T, G> {
    fn drop(&mut self) {
        unsafe {
            (*self.source).links.remove(&self.dest);
        }
    }
}

unsafe impl Send for GgToken<'_> {}
unsafe impl Sync for GgToken<'_> {}

unsafe impl<T: Sync, G: Sync> Sync for GenerationalGraph<'_, T, G> {}
unsafe impl<T: Sync, G: Sync> Sync for NodeRef<'_, '_, '_, T, G> {}

fn main() {
    GenerationalGraph::new(|graph1, mut token1| {
        let mut x1 = graph1.add(1, &mut token1);
        let mut x2 = graph1.add(1, &mut token1);
        x1.link(&x2, 2);

        graph1.visit(&x1, |root| {});

        GenerationalGraph::new(|graph2, mut token2| {
            let mut y1 = graph2.add(1, &mut token2);
            y1.link_outer(&x1, 1);
            let handle = x1.link_inner(&y1, 1);

            // ...
        });
    });
}
