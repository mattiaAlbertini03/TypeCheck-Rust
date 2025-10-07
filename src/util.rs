use indexmap::{IndexMap, IndexSet};
use rustc_hash::FxHasher;
use std::hash::{BuildHasherDefault, Hash, Hasher};
use std::marker::PhantomData;
use crate::declar::{RecRule, Declar, RecRulePtr};
use crate::expr::{ExprPtr, Expr};
use crate::universe::{UniversePtr, UparamsPtr, Universe, Universe::Zero};
use crate::name::{NamePtr, Name, Name::Anonymous};

pub type FxIndexSet<A> = IndexSet<A, BuildHasherDefault<FxHasher>>;
pub type FxIndexMap<K, V> = IndexMap<K, V, BuildHasherDefault<FxHasher>>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ptr<A> {
    pub idx: usize,
    pub ph: PhantomData<A>,
}

impl<A> Ptr<A> {
    pub fn from(idx: usize) -> Self {
        Self { idx, ph: PhantomData }
    }

    pub fn get_hash(&self) -> u64 {
        self.idx as u64
    }
}

impl<A> Hash for Ptr<A> {
    fn hash<H: Hasher>(&self, state: &mut H) { state.write_u64(self.get_hash()) }
}

pub fn new_fx_index_set<A>() -> FxIndexSet<A> { FxIndexSet::with_hasher(Default::default()) }
pub fn new_fx_index_map<K, V>() -> FxIndexMap<K, V> { FxIndexMap::with_hasher(Default::default()) }

#[macro_export]
macro_rules! hash64 {
    ( $( $x:expr ),* ) => {
        {
            use std::hash::{ Hash, Hasher };
            let mut hasher = rustc_hash::FxHasher::default();
            $(
                ($x).hash(&mut hasher);
            )*
            hasher.finish()
        }
    };
}

macro_rules! reader {
    ($fn_name:ident, $field:ident, $ptr:ty, $ret:ty) => {
        pub fn $fn_name(&self, p: $ptr) -> $ret {
            self.$field.get_index(p.idx as usize).cloned().unwrap()
        }
    };
}

macro_rules! reader_map {
    ($fn_name:ident, $field:ident, $ptr:ty, $ret:ty) => {
        pub fn $fn_name(&self, val: $ptr) -> $ret {
            self.$field.get(&val).cloned().unwrap()
        }
    };
}

macro_rules! alloc {
    ($fn_name:ident, $field:ident, $ptr:ty, $ret:ty) => {
        pub fn $fn_name(&mut self, n: $ptr) -> $ret {
            Ptr::from(self.$field.insert_full(n).0)
        }
    };
}

pub struct ExportFile<'p> {
    pub names: FxIndexSet<Name<'p>>,
    pub universes: FxIndexSet<Universe<'p>>,
    pub exprs: FxIndexSet<Expr<'p>>,
    pub rec_rules: FxIndexSet<RecRule<'p>>,
    pub uparams: FxIndexSet<Vec<UniversePtr<'p>>>,
    pub declars: FxIndexMap<NamePtr<'p>, Declar<'p>>,
    pub infers: FxIndexMap<ExprPtr<'p>, ExprPtr<'p>>,
    pub whnfs: FxIndexMap<ExprPtr<'p>, ExprPtr<'p>>,
}

impl<'t> ExportFile<'t> {
    pub fn new() -> Self {
        let mut out = Self {
            names: new_fx_index_set(),
            universes: new_fx_index_set(),
            exprs: new_fx_index_set(),
            rec_rules: new_fx_index_set(),
            uparams: new_fx_index_set(),

            declars: new_fx_index_map(),
            infers: new_fx_index_map(),
            whnfs: new_fx_index_map(),
        };
        out.names.insert(Anonymous);
        out.universes.insert(Zero);
        out
    }

    reader!(read_rec_rule, rec_rules, RecRulePtr<'t>, RecRule<'t>);
    reader!(read_name, names, NamePtr<'t>, Name<'t>);
    reader!(read_expr, exprs, ExprPtr<'t>, Expr<'t>);
    reader!(read_universe, universes, UniversePtr<'t>, Universe<'t>);
    reader!(read_uparams, uparams, UparamsPtr<'t>, Vec<UniversePtr<'t>>);
    
    pub fn read_expr_pair(&self, a: ExprPtr<'t>, b: ExprPtr<'t>) -> (Expr<'t>, Expr<'t>) {
        (self.read_expr(a), self.read_expr(b))
    }

    reader_map!(read_declar, declars, NamePtr<'t>, Declar<'t>);
    reader_map!(read_infer, infers, ExprPtr<'t>, ExprPtr<'t>);
    reader_map!(read_whnf, whnfs, ExprPtr<'t>, ExprPtr<'t>);
    
    alloc!(alloc_name, names, Name<'t>, NamePtr<'t>);
    alloc!(alloc_expr, exprs, Expr<'t>, ExprPtr<'t>);
    alloc!(alloc_universe, universes, Universe<'t>, UniversePtr<'t>);
    alloc!(alloc_uparams, uparams, Vec<UniversePtr<'t>>, UparamsPtr<'t>);
    alloc!(alloc_rec_rule, rec_rules, RecRule<'t>, RecRulePtr<'t>);
}
