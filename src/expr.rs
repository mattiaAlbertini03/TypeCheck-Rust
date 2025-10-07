use std::sync::Mutex;
use std::hash::{Hash, Hasher};
use crate::util::{Ptr, ExportFile};
use crate::hash64;
use crate::universe::{UparamsPtr, UniversePtr};
use crate::name::NamePtr;
use Expr::*;


static COUNTER_FREEVAR: Mutex<u32> = Mutex::new(0);

pub const VAR_HASH: u64 = 20;
pub const SORT_HASH: u64 = 21;
pub const CONST_HASH: u64 = 22;
pub const APP_HASH: u64 = 23;
pub const LAMBDA_HASH: u64 = 24;
pub const PI_HASH: u64 =  25;
pub const LET_HASH: u64 = 26;
pub const PROJ_HASH: u64 = 27;
pub const NAT_LIT_HASH: u64 = 28;
pub const STR_LIT_HASH: u64 = 29;

pub const FREE_VAR_HASH: u64 = 30;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr<'a> {
    Var { hash: u64, dbj_idx: u32, },
    FreeVar {hash: u64, idx: u32, ty: ExprPtr<'a>, },
    Sort { hash: u64, universe: UniversePtr<'a>, },
    Const { hash: u64, name: NamePtr<'a>, universes: UparamsPtr<'a>, },
    App { hash: u64, fun: ExprPtr<'a>, arg: ExprPtr<'a>,  },
    Lambda { hash: u64, name: NamePtr<'a>,  ty: ExprPtr<'a>, body: ExprPtr<'a>,  },
    Pi { hash: u64, name: NamePtr<'a>,  ty: ExprPtr<'a>, body: ExprPtr<'a>,  },
    Let { hash: u64, name: NamePtr<'a>, ty: ExprPtr<'a>, val: ExprPtr<'a>, body: ExprPtr<'a>,  },
    Proj { hash: u64, name: NamePtr<'a>, idx: u32, structure: ExprPtr<'a>,  },
    NatLit { hash: u64, val: u128, },
    StrLit { hash: u64, val: String, },
}

impl<'a> Expr<'a> {
    pub fn get_hash(&self) -> u64 {
        match self {
            Var { hash, .. } | FreeVar { hash, .. } | Sort { hash, .. } | Const { hash, .. }
            | App { hash, .. } | Pi { hash, .. } | Lambda { hash, .. } | Let { hash, .. } 
            | StrLit { hash, .. } | NatLit { hash, .. } | Proj { hash, .. } => *hash,
        }
    }
}

impl<'a> Hash for Expr<'a> {
    fn hash<H: Hasher>(&self, state: &mut H) { state.write_u64(self.get_hash()) }
}

pub type ExprPtr<'a> = Ptr<&'a Expr<'a>>;

impl<'t> ExportFile<'t> {
    
    pub fn var(&mut self, dbj_idx: u32) -> ExprPtr<'t> {
        let hash = hash64!(VAR_HASH, dbj_idx);
        self.alloc_expr(Var { dbj_idx, hash })
    }
    pub fn free_var(&mut self, ty: ExprPtr<'t>) -> ExprPtr<'t> {
        let mut c = COUNTER_FREEVAR.lock().unwrap();
        let idx = *c;
        *c += 1;
        let hash = hash64!(FREE_VAR_HASH, idx, ty);
        self.alloc_expr(FreeVar { idx, ty, hash })
    }

    pub fn sort(&mut self, universe: UniversePtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(SORT_HASH, universe);
        self.alloc_expr(Sort { universe, hash })
    }

    pub fn mk_const(&mut self, name: NamePtr<'t>, universes: UparamsPtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(CONST_HASH, name, universes);
        self.alloc_expr(Const { name, universes, hash })
    }

    pub fn app(&mut self, fun: ExprPtr<'t>, arg: ExprPtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(APP_HASH, fun, arg);
        self.alloc_expr(App { fun, arg, hash })
    }

    pub fn lambda( &mut self, name: NamePtr<'t>, ty: ExprPtr<'t>, body: ExprPtr<'t> ) -> ExprPtr<'t> {
        let hash = hash64!(LAMBDA_HASH, name, ty, body);
        self.alloc_expr(Lambda { name, ty, body, hash })
    }

    pub fn pi(&mut self, name: NamePtr<'t>, ty: ExprPtr<'t>, body: ExprPtr<'t>, ) -> ExprPtr<'t> {
        let hash = hash64!(PI_HASH, name, ty, body);
        self.alloc_expr(Pi { name, ty, body, hash })
    }

    pub fn mk_let( &mut self, name: NamePtr<'t>, ty: ExprPtr<'t>, val: ExprPtr<'t>, body: ExprPtr<'t> ) -> ExprPtr<'t> {
        let hash = hash64!(LET_HASH, name, ty, val, body);
        self.alloc_expr(Let { name, ty, val, body, hash })
    }

    pub fn proj(&mut self, name: NamePtr<'t>, idx: u32, structure: ExprPtr<'t>) -> ExprPtr<'t> {
        let hash = hash64!(PROJ_HASH, name, idx, structure);
        self.alloc_expr(Proj { name, idx, structure, hash })
    }

    pub fn nat_lit(&mut self, val: u128) -> ExprPtr<'t> {
        let hash = hash64!(NAT_LIT_HASH, val);
        self.alloc_expr(NatLit { val, hash })
    }
    
    pub fn str_lit(&mut self, val: String) -> ExprPtr<'t> {
        let hash = hash64!(STR_LIT_HASH, val);
        self.alloc_expr(StrLit { val, hash })
    }
    
    pub fn subst_expr_universes(&mut self, e: ExprPtr<'t>, ups_dec: UparamsPtr<'t>, ups_const: UparamsPtr<'t>) -> ExprPtr<'t> {
        match self.read_expr(e) {
            
            Var { .. } | NatLit { .. } | StrLit { .. } => e,
            
            FreeVar { .. } => panic!("subst di universi su una freeVar"),
            
            Sort { universe, .. } => {
                let universe = self.subst_universe(universe, ups_dec, ups_const);
                self.sort(universe)
            }
            
            Const { name, universes, .. } => {
                let universes = self.subst_universes(universes, ups_dec, ups_const);
                self.mk_const(name, universes)
            }
            
            App { fun, arg, .. } => {
                let fun = self.subst_expr_universes(fun, ups_dec, ups_const);
                let arg = self.subst_expr_universes(arg, ups_dec, ups_const);
                self.app(fun, arg)
            }
            
            Pi { name,  ty, body, .. } => {
                let ty = self.subst_expr_universes(ty, ups_dec, ups_const);
                let body = self.subst_expr_universes(body, ups_dec, ups_const);
                self.pi(name,  ty, body)
            }
            
            Lambda { name,  ty, body, .. } => {
                let ty = self.subst_expr_universes(ty, ups_dec, ups_const);
                let body = self.subst_expr_universes(body, ups_dec, ups_const);
                self.lambda(name,  ty, body)
            }
            
            Let { name, ty, val, body, .. } => {
                let ty = self.subst_expr_universes(ty, ups_dec, ups_const);
                let val = self.subst_expr_universes(val, ups_dec, ups_const);
                let body = self.subst_expr_universes(body, ups_dec, ups_const);
                self.mk_let(name, ty, val, body)
            }
            
            Proj { name, idx, structure, .. } => {
                let structure = self.subst_expr_universes(structure, ups_dec, ups_const);
                self.proj(name, idx, structure)
            }
        }
    }
    
    pub fn abstr(&mut self, e: ExprPtr<'t>, val: ExprPtr<'t>, deph: u32) -> ExprPtr<'t> {
        match self.read_expr(e) {
            FreeVar { .. } => {
                if e == val {
                    return self.var(deph)
                }
                return e
            }
            
            Var { dbj_idx, .. } => {
                if dbj_idx >= deph {
                    return self.var(dbj_idx+1);
                } else {
                    return e;
                }
            }
            
            NatLit{..} | StrLit{..} | Sort { .. } | Const { .. } => e, 
            
            App { fun, arg, .. } =>{
                let f = self.abstr(fun, val, deph);
                let a = self.abstr(arg, val, deph);
                self.app(f, a)
            }
            Lambda { name, ty, body, ..  } => {
                let t = self.abstr(ty, val, deph);
                let b = self.abstr(body, val, deph + 1);
                self.lambda(name, t, b)
            }
            Pi { name, ty, body, ..  } => {
                let t = self.abstr(ty, val, deph);
                let b = self.abstr(body, val, deph + 1);
                self.pi(name, t, b)
            }
            Let { name, ty, val: val_let, body, ..  } => {
                let t = self.abstr(ty, val, deph);
                let v = self.abstr(val_let, val, deph);
                let b = self.abstr(body, val, deph + 1);
                self.mk_let(name, t, v, b)
            }
            Proj { name, idx, structure, ..  } => {
                let s = self.abstr(structure, val, deph);
                self.proj(name, idx, s)
            }
        }
    }
    
    pub fn inst(&mut self, e: ExprPtr<'t>, val: ExprPtr<'t>, deph: u32) -> ExprPtr<'t> {
        match self.read_expr(e) {
            Var { dbj_idx, .. } => {
                if dbj_idx == deph {
                    return val; 
                } else if dbj_idx > deph {
                    return self.var(dbj_idx-1);
                } else {
                    return e;
                }
            }
            NatLit{..} | StrLit{..} | FreeVar { .. } | Sort { .. } | Const { .. } => e, 
            App { fun, arg, .. } =>{
                let f = self.inst(fun, val, deph);
                let a = self.inst(arg, val, deph);
                self.app(f, a)
            }
            Lambda { name, ty, body, ..  } => {
                let t = self.inst(ty, val, deph);
                let b = self.inst(body, val, deph + 1);
                self.lambda(name, t, b)
            }
            Pi { name, ty, body, ..  } => {
                let t = self.inst(ty, val, deph);
                let b = self.inst(body, val, deph + 1);
                self.pi(name, t, b)
            }
            Let { name, ty, val: val_let, body, ..  } => {
                let t = self.inst(ty, val, deph);
                let v = self.inst(val_let, val, deph);
                let b = self.inst(body, val, deph + 1);
                self.mk_let(name, t, v, b)
            }
            Proj { name, idx, structure, ..  } => {
                let s = self.inst(structure, val, deph);
                self.proj(name, idx, s)
            }
        }
    }
}

