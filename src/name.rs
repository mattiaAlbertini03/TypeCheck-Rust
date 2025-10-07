use std::hash::{Hash, Hasher};
use crate::util::{ Ptr, ExportFile};
use crate::hash64;
use Name::*;

pub const ANON_HASH: u64 = 0;
pub const STR_HASH:  u64 = 1;
pub const NUM_HASH:  u64 = 2;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Name<'a> {
    Anonymous,
    Str {pfx: NamePtr<'a>, value: String, hash: u64},
    Num {pfx: NamePtr<'a>, value: u32, hash: u64},
}

impl<'a> Name<'a> {
    fn get_hash(&self) -> u64 {
        match self {
            Anonymous => ANON_HASH,
            Str{ hash, .. } | Num{hash, ..} => *hash,
        }
    }
}

impl<'a> Hash for Name<'a> {
    fn hash<H: Hasher>(&self, state: &mut H) { state.write_u64(self.get_hash()) }
}

pub type NamePtr<'a> = Ptr<&'a Name<'a>>;

impl<'a> ExportFile<'a> {
    
    pub fn anonymous(&self) -> NamePtr<'a> { Ptr::from(0) }
    
    pub fn mk_str(&mut self, pfx: NamePtr<'a>, value: String) -> NamePtr<'a> {
        let hash = hash64!(STR_HASH, pfx, value);
        self.alloc_name(Str{pfx, value, hash})
    }
    pub fn num(&mut self, pfx: NamePtr<'a>, value: u32) -> NamePtr<'a> {
        let hash = hash64!(NUM_HASH, pfx, value);
        self.alloc_name(Num{pfx, value, hash})
    }
}

