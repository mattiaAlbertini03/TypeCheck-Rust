use std::hash::{ Hash, Hasher };
use crate::expr::ExprPtr;
use crate::name::NamePtr;
use crate::universe::UparamsPtr;
use crate::util::{Ptr, ExportFile};
use crate::hash64;
use Declar::*;

pub const REC_RULE_HASH: u64 = 40;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RecRule<'a> {
    pub ctor_name: NamePtr<'a>,
    pub num_fields: u32,
    pub val: ExprPtr<'a>,
    pub hash: u64,
}

impl<'a> Hash for RecRule<'a> {
    fn hash<H: Hasher>(&self, state: &mut H) { state.write_u64(self.hash) }
}

pub type RecRulePtr<'a> = Ptr<&'a RecRule<'a>>;

impl<'t> ExportFile<'t> {
    pub fn rec_rule(&mut self, ctor_name: NamePtr<'t>, num_fields: u32, val : ExprPtr<'t>) -> RecRulePtr<'t> {
        let hash = hash64!(REC_RULE_HASH, ctor_name, num_fields, val);
        self.alloc_rec_rule( RecRule { ctor_name, num_fields, val , hash})
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Declar<'a> {
    Axiom { name: NamePtr<'a>, uparams: UparamsPtr<'a>, ty: ExprPtr<'a> },
    Quot { name: NamePtr<'a>, uparams: UparamsPtr<'a>, ty: ExprPtr<'a> },
    Opaq { name: NamePtr<'a>, uparams: UparamsPtr<'a>, ty: ExprPtr<'a>, val: ExprPtr<'a> },
    Theorem { name: NamePtr<'a>, uparams: UparamsPtr<'a>, ty: ExprPtr<'a>, val: ExprPtr<'a> },
    Definition { name: NamePtr<'a>, uparams: UparamsPtr<'a>, ty: ExprPtr<'a>, val: ExprPtr<'a>},
    Inductive{ name: NamePtr<'a>, uparams: UparamsPtr<'a>, ty: ExprPtr<'a>, num_indices: u32, all_ctor_names: Vec<NamePtr<'a>>},
    Constructor{ name: NamePtr<'a>, uparams: UparamsPtr<'a>, ty: ExprPtr<'a>, num_params: u32, num_fields: u32, parent: NamePtr<'a>},
    Recursor{ name: NamePtr<'a>, uparams: UparamsPtr<'a>, ty: ExprPtr<'a>, all_inductive_names: Vec<NamePtr<'a>>, num_params: u32, num_indices: u32, 
                num_motives: u32, num_minors: u32, rec_rules: Vec<RecRulePtr<'a>>},
}

macro_rules! getter {
    ($fn_name:ident, $field:ident, $ret:ty) => {
        pub fn $fn_name(&self) -> $ret {
            match self {
                Axiom { $field, .. } | Quot { $field, .. } | Theorem { $field, .. }
                | Definition { $field, .. } | Opaq { $field, .. } | Inductive { $field, .. }
                | Constructor { $field, .. } | Recursor { $field, .. } => *$field,
            }
        }
    };
}

impl<'a> Declar<'a> {
    getter!(ty, ty, ExprPtr<'a>);
    getter!(uparams, uparams, UparamsPtr<'a>);
    getter!(name, name, NamePtr<'a>);

    pub fn val(&self) -> Option<ExprPtr<'a>> {
        match self {
            Theorem { val, .. } | Definition { val, .. } | Opaq { val, .. } => Some(*val),
            _ => None,
        }
    }
}

