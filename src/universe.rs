use std::hash::{Hash, Hasher};
use crate::util::{Ptr, ExportFile};
use crate::name::NamePtr;
use crate::hash64;
use Universe::*;

pub const ZERO_HASH: u64 = 10;
pub const SUCC_HASH: u64 = 11;
pub const MAX_HASH: u64 = 12;
pub const IMAX_HASH: u64 = 13;
pub const PARAM_HASH: u64 = 14;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Universe<'a> {
    Zero,
    Succ { pred :UniversePtr<'a>, hash: u64 },
    Max { v1: UniversePtr<'a>, v2: UniversePtr<'a>, hash: u64 },
    IMax { v1: UniversePtr<'a>, v2: UniversePtr<'a>, hash: u64 },
    Param { name:NamePtr<'a>, hash: u64},
}

impl<'a> Universe<'a> {
    fn get_hash(&self) -> u64 {
        match self {
            Zero => ZERO_HASH,
            Succ {hash, .. } | Max {hash, .. } 
            | IMax {hash, .. } | Param {hash, .. } => *hash,
        }
    }
}

impl<'a> Hash for Universe<'a> {
    fn hash<H: Hasher>(&self, state: &mut H) { state.write_u64(self.get_hash()) }
}

pub type UniversePtr<'a> = Ptr<&'a Universe<'a>>;

pub type UparamsPtr<'a> = Ptr<&'a Vec<UniversePtr<'a>>>;

impl<'t> ExportFile<'t> {
    
    pub fn zero(&self) -> UniversePtr<'t> { Ptr::from(0) }
    
    pub fn succ(&mut self, pred: UniversePtr<'t>) -> UniversePtr<'t> {
        let hash = hash64!(SUCC_HASH, pred);
        self.alloc_universe(Succ{pred, hash})
    }

    pub fn max(&mut self, v1: UniversePtr<'t>, v2: UniversePtr<'t>) -> UniversePtr<'t> {
        let hash = hash64!(MAX_HASH, v1, v2);
        self.alloc_universe(Max{v1, v2, hash})
    }
    
    pub fn imax(&mut self, v1: UniversePtr<'t>, v2: UniversePtr<'t>) -> UniversePtr<'t> {
        let hash = hash64!(IMAX_HASH, v1, v2);
        self.alloc_universe(IMax{v1, v2, hash})
    }
    
    pub fn param(&mut self, name: NamePtr<'t>) -> UniversePtr<'t> {
        let hash = hash64!(PARAM_HASH, name);
        self.alloc_universe(Param{name, hash})
    }

    fn riduci(&mut self, l: UniversePtr<'t>, r: UniversePtr<'t>, da_max: bool) -> UniversePtr<'t> {
        match (self.read_universe(l), self.read_universe(r)) {
            (Zero, _) => r,
            (_, Zero) => l,
            (Succ{pred : p1, ..}, Succ{pred : p2, ..}) => {
                let prec = self.riduci(p1, p2, false);
                self.succ(prec)
            }
            (Max{..},_) |(IMax{..},_) | (_, Max{..}) | (_, IMax{..}) => {
                let r = self.semplifica(r);
                let l = self.semplifica(l);
                if da_max { self.max(l,r) }
                else { self.riduci(l, r, true) }
            }
            (Param{..},_)  => {
                let r = self.semplifica(r);
                self.max(l, r)
            }
            (_,Param{..}) => {
                let l = self.semplifica(l);
                self.max(l, r)
            }
        }
    }

    pub fn semplifica(&mut self, ptr: UniversePtr<'t>) -> UniversePtr<'t> {
        match self.read_universe(ptr) {
            Zero | Param{..} => ptr,
            Succ{pred, ..} => {
                let val = self.semplifica(pred);
                self.succ(val)
            }
            Max{v1, v2, ..} => {
                let l = self.semplifica(v1);
                let r = self.semplifica(v2);
                self.riduci(l, r, false)
            }
            IMax{v1, v2, ..} => {
                let l = self.semplifica(v1);
                let r = self.semplifica(v2);
                if self.leq(r, self.zero(), 0) {
                    self.zero()
                } else {
                    self.riduci(l, r, false)
                }
            }
        }
    }
    
    pub fn contiene_param(&self, universe: UniversePtr<'t>, params: UparamsPtr<'t>) -> bool {
        match self.read_universe(universe) {
            Zero => true,
            Succ {pred, ..} => self.contiene_param(pred, params),
            Max {v1, v2, ..} | IMax{v1, v2, ..} => self.contiene_param(v1, params) && self.contiene_param(v2, params),
            Param{..} => self.read_uparams(params).iter().copied().any(|x| x == universe),
        }
    }

    pub fn eq_many(&mut self, xs: UparamsPtr<'t>, ys: UparamsPtr<'t>) -> bool {
        let xs = self.read_uparams(xs).clone();
        let ys = self.read_uparams(ys).clone();
        if xs.len() != ys.len() {
            return false
        }
        if xs.is_empty() {
            return true
        }
        xs.iter().copied().zip(ys.iter().copied()).all(|(x, y)| self.leq(x, y, 0) && self.leq(y, x, 0))
    }
    
    pub fn leq(&mut self, l: UniversePtr<'t>, r: UniversePtr<'t>, deph_r: isize) -> bool {
        let l = self.semplifica(l);
        let r = self.semplifica(r);
        let out = match (self.read_universe(l), self.read_universe(r)) {
            (Zero, _) if deph_r >= 0 => true,
            (_, Zero) if deph_r < 0 => false,
            (Zero, Zero) => deph_r >= 0,
            
            (Param{..}, Zero) => false,
            (Zero, Param{..}) => deph_r >= 0,
            (Param {name : n1, ..}, Param{name : n2, ..}) => n1 == n2 && deph_r >= 0,

            (Succ{pred : s1, ..}, Succ {pred : s2, ..} ) => self.leq(s1, s2, deph_r),
            (Succ{pred, ..}, _) => self.leq(pred, r, deph_r - 1),
            (_, Succ {pred, ..}) => self.leq(l, pred, deph_r + 1),
            
            (IMax{v2, .. }, _) if self.leq(v2, self.zero(), 0) => self.leq(self.zero(), r, deph_r),
            (_, IMax{v2, .. }) if self.leq(v2, self.zero(), 0) => self.leq(l, self.zero(), deph_r),

            (IMax{v1, v2, ..}, IMax{v1: s1, v2 : s2, ..}) |
            (Max{v1, v2, ..}, Max{v1: s1, v2: s2, ..}) if ( v1 == s1 && v2 == s2 ) || ( v1 == s2 && v2 == s1 ) => deph_r >= 0,
            

            (IMax{v2, .. }, _) | (_, IMax{v2, .. }) if matches!(self.read_universe(v2), Param{..})  => {
                let zero = self.alloc_uparams(vec![self.zero()]);
                let succ_v = self.succ(v2);
                let succ = self.alloc_uparams(vec![succ_v]);
                let param = self.alloc_uparams(vec![v2]);
                
                let lz = self.subst_universe(l, param, zero);
                let rz = self.subst_universe(r, param, zero);
                let ls = self.subst_universe(l, param, succ);
                let rs = self.subst_universe(r, param, succ);
                return self.leq(lz, rz, deph_r) && self.leq(ls, rs, deph_r);

            }
            
            (Max{v1, v2, ..}, _) | (IMax{v1, v2, ..}, _) => self.leq(v1, r, deph_r) && self.leq(v2, r, deph_r),
            (_, Max{v1, v2, ..}) | (_, IMax{v1, v2, ..}) => self.leq(l, v1, deph_r) || self.leq(l, v2, deph_r),
        };
        out
    }

    pub fn subst_universes(&mut self, uparams: UparamsPtr<'t>, ups_dec: UparamsPtr<'t>, ups_const: UparamsPtr<'t>) -> UparamsPtr<'t> {
        let out = self.read_uparams(uparams).iter().copied().map(|l| self.subst_universe(l, ups_dec, ups_const)).collect::<Vec<_>>();
        self.alloc_uparams(out)
    }

    pub fn subst_universe(&mut self, universe: UniversePtr<'t>, ups_dec: UparamsPtr<'t>, ups_const: UparamsPtr<'t>) -> UniversePtr<'t> {
        match self.read_universe(universe) {
            Zero => self.zero(),
            Succ {pred, ..} => {
                let val = self.subst_universe(pred, ups_dec, ups_const);
                self.succ(val)
            }
            Max{v1, v2, .. }=> {
                let l = self.subst_universe(v1, ups_dec, ups_const);
                let r = self.subst_universe(v2, ups_dec, ups_const);
                self.max(l, r)
            }
            IMax{v1, v2, ..} => {
                let l = self.subst_universe(v1, ups_dec, ups_const);
                let r = self.subst_universe(v2, ups_dec, ups_const);
                self.imax(l, r)
            }
            Param{..} => {
                let (ups_dec, ups_const) = (self.read_uparams(ups_dec), self.read_uparams(ups_const));
                for (k, v) in ups_dec.iter().copied().zip(ups_const.iter().copied()) {
                    if universe == k {
                        return v
                    }
                }
                universe
            }
        }
    }

}
