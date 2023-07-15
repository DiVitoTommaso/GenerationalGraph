use std::cell::{RefCell, UnsafeCell};
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::{cell, result, thread, vec};
use std::arch::asm;
use std::collections::{HashMap, HashSet};
use std::collections::linked_list::LinkedList;
use std::env::args;
use std::io::Take;
use std::ptr::null_mut;
use std::rc::Rc;
use std::sync::{Arc, Mutex};
use std::thread::spawn;
use ghost_cell::{GhostCell, GhostToken};
use typed_arena::Arena;

// Definizione di lifetime di vario tipo per la validazione dei raw pointer contenuti nelle strutture ritornate e per il branding dei nodi
pub struct CovariantLifetime<'id>(PhantomData<&'id ()>);

pub struct InvariantLifetime<'id>(PhantomData<*mut &'id ()>);

pub struct ContravariantLifetime<'id>(PhantomData<fn(&'id ()) -> ()>);

// Definizione di un token di autorizzazione per regolare il controllo degli accessi ai grafi
pub struct GgToken<'id> {
    _marker: InvariantLifetime<'id>,
}

// Nodo di un Grafo contenente il valore che possiede e un set/lista di puntatori a altri nodi per rappresentare gli archi
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

impl<'id, T, G> GenerationalGraph<'id, T, G> {
    
    pub fn new(f: impl for<'a> FnOnce(GenerationalGraph<'a, T, G>, GgToken<'a>) -> ()) {
        f(GenerationalGraph {
            nodes: Arena::new(),
            _marker: CovariantLifetime(PhantomData),
        },
          GgToken {
              _marker: InvariantLifetime(PhantomData),
          })
    }

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
    
    pub fn link(&mut self, other: &NodeRef<'_, 'id, '_, T, G>, cost: G) {
        unsafe { (*self.ptr).links.insert(other.ptr, cost); }
    }

    pub fn unlink(&mut self, other: &NodeRef<'_, 'id, '_, T, G>) {
        unsafe { (*self.ptr).links.remove(&other.ptr); }
    }

    pub fn link_outer(&mut self, other: &NodeRef<'a, '_, '_, T, G>, cost: G) {
        unsafe { (*self.ptr).links.insert(other.ptr, cost); }
    }

    pub fn unlink_outer(&mut self, other: &NodeRef<'a, '_, '_, T, G>) {
        unsafe { (*self.ptr).links.remove(&other.ptr); }
    }

    pub fn link_inner(&mut self, other: &NodeRef<'_, '_, 'a, T, G>, cost: G,
                      with_link: impl FnOnce(&mut NodeRef<'a, 'id, 'b, T, G>) -> ()) {
        unsafe {
            (*self.ptr).links.insert(other.ptr, cost);
            with_link(self);
            (*self.ptr).links.remove(&other.ptr);
        }
    }

    pub fn link_inners(&mut self, others: Vec<&NodeRef<'_, '_, 'a, T, G>>, costs: Vec<G>,
                       with_link: impl FnOnce(&mut NodeRef<'a, 'id, 'b, T, G>) -> ()) {
        unsafe {
            if others.len() != costs.len() {
                return;
            }

            let mut costs_vec = costs;
            for index in 0..others.len() {
                (*self.ptr).links.insert(others.get_unchecked(index).ptr, costs_vec.remove(0));
            }
            with_link(self);
            for index in 0..others.len() {
                (*self.ptr).links.remove(&others.get_unchecked(index).ptr);
            }
        }
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

    pub fn bfs<R>(&self,
                  init: impl Fn() -> R,
                  each: impl Fn(&T, &mut R) -> ()) -> R {
        let mut frontier = LinkedList::from([self.ptr]);
        let mut visited = HashSet::new();
        let mut supp = init();

        unsafe {
            while !frontier.is_empty() {
                let ptr = frontier.pop_front().unwrap();

                if !visited.contains(&ptr) {
                    each(&(*ptr).value, &mut supp);
                    visited.replace(ptr);
                    for (node, weight) in (*ptr).links.iter() {
                        frontier.push_back(*node)
                    }
                }
            }
        }
        supp
    }

    pub fn node_id(&self) -> usize {
        (self.ptr as usize)
    }

    pub fn links_ids(&self) -> Vec<usize> {
        unsafe {
            let mut tmp = Vec::with_capacity((*self.ptr).links.len());
            for (node, _) in (*self.ptr).links.iter() {
                tmp.push((*node) as usize)
            }
            tmp
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

unsafe impl<'id, T, G> Send for GenerationalGraph<'id, T, G> {}

unsafe impl<'id, T, G> Sync for GenerationalGraph<'id, T, G> {}

unsafe impl<'a, 'id, 'b, T, G> Send for NodeRef<'a, 'id, 'b, T, G> {}

unsafe impl<'a, 'id, 'b, T, G> Sync for NodeRef<'a, 'id, 'b, T, G> {}

unsafe impl<'id> Send for GgToken<'id> {}

unsafe impl<'id> Sync for GgToken<'id> {}

fn visit(frontier: &mut LinkedList<usize>,
    visited: &mut HashSet<usize>,
    map: &HashMap<usize, &NodeRef<i32, i32>>,
    node_id: usize, each: impl FnOnce(&i32) -> ()) {

    // Cerchiamo tramite l'indetificatore se il nodo passato come
    // parametro è presente nella mappa. Se è presente visita il
    // nodo e inserisci i suoi archi in frontiera, altrimenti ritorna.
    match map.get(&node_id) {
        None => {
            return;
        }
        Some(node) => {
            // Controlla che il nodo non sia già stato visitato.
            if !visited.contains(&node.node_id()) {
                // Codice personalizzato.
                each(&(***node));
                // Aggiungi il nodo insieme a quelli già visitati.
                visited.replace(node.node_id());
                // Inserisci in frontiera i nodi adiacenti (archi).
                for link_id in node.links_ids() {
                    frontier.push_back(link_id);
                }
            }
        }
    }
}

fn main() {
    // Esempio di utilizzo della funzione visit
    GenerationalGraph::new(|graph1, mut token1| {
        let x1 = graph1.add(1, &mut token1);
        GenerationalGraph::new(|graph2, mut token2| {
            let mut y1 = graph2.add(2, &mut token2);
            y1.link_outer(&x1, 2);

            let mut map1 = HashMap::new();
            map1.insert(x1.node_id(), &x1);
            let mut map2 = HashMap::new();
            map2.insert(y1.node_id(), &y1);

            let mut curr = None;
            let mut frontier = LinkedList::from([y1.node_id()]);
            let mut visited = HashSet::new();

            // esegui la bfs
            while true {
                curr = frontier.pop_front();
                match curr {
                    None => break,
                    Some(node) => {
                        visit(&mut frontier, &mut visited,
                              &map1, node, |val| {
                                println!("Node Val={}", val);
                            });
                        visit(&mut frontier, &mut visited,
                              &map2, node, |val| {
                                println!("Node Val={}", val);
                            });
                    }
                }
            }
        });
    });
}
