use std::error::Error;
use std::path::Path;
use std::fs::OpenOptions;
use std::io::{BufReader, BufRead};
use std::slice::Iter;
use std::sync::Mutex;
use crate::declar::{ Declar::*, RecRulePtr};
use crate::util::{ ExportFile, Ptr};
use crate::hash64;
use crate::expr::ExprPtr;
use crate::name::NamePtr;
use crate::universe::{UparamsPtr, UniversePtr, PARAM_HASH, Universe::Param};

static COUNTER: Mutex<u32> = Mutex::new(1);

pub fn read_export_file<'a>(pathbuf: &Path) -> Result<ExportFile<'a>, Box<dyn Error>> {
    match OpenOptions::new().read(true).truncate(false).open(pathbuf) {
        Ok(file) => read_file(BufReader::new(file)), 
        Err(e) => panic!("Errore nell'apertura dell'export file: {:?}", e),
    }
}

pub fn read_file<'p, R: BufRead>( mut buf_reader: R, ) -> Result<ExportFile<'p>, Box<dyn Error>> {
    let mut f = ExportFile::new();
    let mut buffer = String::new();
    buf_reader.read_line(&mut buffer)?;
    if buffer.trim_end() != "2.0.0" {
        panic!("versione non valida ({:?}).", buffer.trim_end());
    }
    loop {
        *COUNTER.lock().unwrap() += 1;
        buffer.clear();
        match buf_reader.read_line(&mut buffer)? {
            0 => break,
            _ => {
                let linea : Vec<&str> = buffer.trim_end().split(' ').filter(|s| !s.is_empty()).collect();
                let mut iter: Iter<&str> = linea.iter();
                let token = iter.next().ok_or_else(|| Box::<dyn Error>::from(format!("Non ci devono essere linee vuote :{}", *COUNTER.lock().unwrap())))?;
                
                match *token {
                    "#AX" => f.parse_axiom(&mut iter),
                    "#DEF" => f.parse_def(&mut iter),
                    "#OPAQ" => f.parse_opaq(&mut iter),
                    "#THM" => f.parse_theorem(&mut iter),
                    "#QUOT" => f.parse_quot(&mut iter),
                    "#IND" => f.parse_inductive(&mut iter),
                    "#CTOR" => f.parse_constructor(&mut iter),
                    "#REC" => f.parse_recursor(&mut iter),
                    // otherwise, (Name, Universe, Expr)
                    idx => f.parse_altro(idx.parse::<u32>()?, &mut iter)?,
                }
                assert!(iter.next().is_none());
            }
        }
    }
    Ok(f)
}

impl<'a> ExportFile<'a>{
    fn parse_axiom(&mut self, ws: &mut Iter<&str>) {
        let name = self.parse_name(ws);
        let ty = self.parse_expr(ws);
        let uparams = self.parse_uparams(ws);
        let axiom = Axiom { name, ty, uparams };
        self.declars.insert(name, axiom);
    }

    fn parse_def(&mut self, ws: &mut Iter<&str>) {
        let name = self.parse_name(ws);
        let ty = self.parse_expr(ws);
        let val = self.parse_expr(ws);
        self.parse_hint(ws);
        let uparams = self.parse_uparams(ws);
        let definition = Definition { name, ty, uparams, val };
        self.declars.insert(name, definition);
    }

    fn parse_opaq(&mut self, ws: &mut Iter<&str>) {
        let name = self.parse_name(ws);
        let ty = self.parse_expr(ws);
        let val = self.parse_expr(ws);
        let uparams = self.parse_uparams(ws);
        let opaq = Opaq { name, ty, uparams, val };
        self.declars.insert(name, opaq);
    }

    fn parse_theorem(&mut self, ws: &mut Iter<&str>) {
        let name = self.parse_name(ws);
        let ty = self.parse_expr(ws);
        let val = self.parse_expr(ws);
        let uparams = self.parse_uparams(ws);
        let theorem = Theorem { name, ty, uparams, val };
        self.declars.insert(name, theorem);
    }

    fn parse_quot(&mut self, ws: &mut Iter<&str>) {
        let name = self.parse_name(ws);
        let ty = self.parse_expr(ws);
        let uparams = self.parse_uparams(ws);
        let quot = Quot { name, ty, uparams };
        self.declars.insert(name, quot);
    }
    
    fn parse_inductive(&mut self, ws: &mut Iter<&str>) {
        let name = self.parse_name(ws);
        let ty = self.parse_expr(ws);
        self.parse_bool(ws);
        self.parse_bool(ws);
        self.parse_u32(ws);
        self.parse_u32(ws);
        let num_indices = self.parse_u32(ws);
        let num_inductives = self.parse_u32(ws);
        self.parse_names(ws, num_inductives);
        let num_ctors = self.parse_u32(ws);
        let all_ctor_names = self.parse_names(ws, num_ctors);
        let uparams = self.parse_uparams(ws);
        let inductive = Inductive{ name, ty, uparams, num_indices, all_ctor_names};
        self.declars.insert(name, inductive);

    }

    fn parse_constructor(&mut self, ws: &mut Iter<&str>) {
        let name = self.parse_name(ws);
        let ty = self.parse_expr(ws);
        let parent = self.parse_name(ws);
        assert!(self.declars.get(&parent).filter(|x| matches!(x, Inductive{..})).is_some(), 
                "Inductive non esistente, riga:{}",*COUNTER.lock().unwrap());
        self.parse_u32(ws);
        let num_params = self.parse_u32(ws);
        let num_fields = self.parse_u32(ws);
        let uparams = self.parse_uparams(ws);
        let ctor = Constructor{ name, ty, uparams, num_params, num_fields, parent };
        self.declars.insert(name, ctor);
    }

    fn parse_recursor(&mut self, ws: &mut Iter<&str>) {
        let name = self.parse_name(ws);
        let ty = self.parse_expr(ws);
        let num_inductives = self.parse_u32(ws);
        let all_inductives = self.parse_names(ws, num_inductives);
        for i in 0..num_inductives as usize { 
            assert!(self.declars.get(&all_inductives[i]).filter(|x| matches!(x, Inductive{..})).is_some(), 
                "Inductive non esistente, riga:{}",*COUNTER.lock().unwrap());
        }
        self.parse_u32(ws);
        self.parse_u32(ws);
        self.parse_u32(ws);
        self.parse_u32(ws);
        let num_rec_rules = self.parse_u32(ws);
        self.parse_rrs(ws, num_rec_rules);
        self.parse_bool(ws);
        let uparams = self.parse_uparams(ws);
        let recursor = Recursor{ name, ty, uparams, };
        self.declars.insert(name, recursor);
    }

    fn parse_altro(&mut self, idx: u32, ws: &mut Iter<&str>) -> Result<(), Box<dyn Error>> {
        let oper = ws.next().expect("Parse primitive");
        match *oper {
            "#RR" => self.parse_rr(idx, ws),
            "#NS" => self.parse_ns(idx, ws),
            "#NI" => self.parse_ni(idx, ws),
            "#US" => self.parse_us(idx, ws),
            "#UM" => self.parse_um(idx, ws),
            "#UIM" => self.parse_uim(idx, ws),
            "#UP" => self.parse_up(idx, ws),
            "#EV" => self.parse_ev(idx, ws),
            "#ES" => self.parse_es(idx, ws),
            "#EC" => self.parse_ec(idx, ws),
            "#EA" => self.parse_ea(idx, ws),
            "#EL" => self.parse_el(idx, ws),
            "#EP" => self.parse_ep(idx, ws),
            "#EZ" => self.parse_ez(idx, ws),
            "#EJ" => self.parse_ej(idx, ws),
            "#ELN" => self.parse_eln(idx, ws),
            "#ELS" => self.parse_els(idx, ws),
            _ => return Err(Box::<dyn Error>::from(format!("Riga {} non riconosciuta", *COUNTER.lock().unwrap()))),
        }
        Ok(())
    }

    fn parse_rr(&mut self, idx: u32, linea: &mut Iter<&str>) {
        let ctor_name = self.parse_name(linea);
        assert!(self.declars.get(&ctor_name).filter(|i| matches!(i, Constructor{..})).is_some(), 
                "Constructor non esistente, riga:{}",*COUNTER.lock().unwrap());
        let num_param = self.parse_u32(linea);
        let val = self.parse_expr(linea);
        assert_eq!(idx as usize, self.rec_rules.len());
        self.rec_rule(ctor_name, num_param, val);
    }
    
    fn parse_rrs(&mut self, ws: &mut Iter<&str>, limit: u32) -> Vec<RecRulePtr<'a>> {
        let mut rr_ptrs = Vec::new();
        for _ in 0..limit {
            let x = self.parse_rec_rule(ws);
            rr_ptrs.push(x);
        }
        rr_ptrs
    }

    fn parse_ns(&mut self, idx: u32, ws: &mut Iter<&str>) {
        let pfx = self.parse_name(ws);
        let sfx = self.parse_str(ws);
        assert_eq!(idx as usize, self.names.len());
        self.mk_str(pfx, sfx);
    }

    fn parse_ni(&mut self, idx: u32, ws: &mut Iter<&str>) {
        let pfx = self.parse_name(ws);
        let sfx = self.parse_u64(ws);
        assert_eq!(idx as usize, self.names.len());
        self.num(pfx, sfx);
    }
    
    fn parse_us(&mut self, idx: u32, ws: &mut Iter<&str>) {
        let l = self.parse_universe(ws);
        assert_eq!(idx as usize, self.universes.len());
        self.succ(l);
    }
    
    fn parse_um(&mut self, idx: u32, ws: &mut Iter<&str>) {
        let l = self.parse_universe(ws);
        let r = self.parse_universe(ws);
        assert_eq!(idx as usize, self.universes.len());
        self.max(l, r);
    }

    fn parse_uim(&mut self, idx: u32, ws: &mut Iter<&str>) {
        let l = self.parse_universe(ws);
        let r = self.parse_universe(ws);
        assert_eq!(idx as usize, self.universes.len());
        self.imax(l,r);

    }

    fn parse_up(&mut self, idx: u32, ws: &mut Iter<&str>) {
        let n = self.parse_name(ws);
        assert_eq!(idx as usize, self.universes.len());
        self.param(n);
    }

    fn parse_ev(&mut self, idx: u32, ws: &mut Iter<&str>) {
        let dbj_idx = self.parse_u32(ws);
        assert_eq!(idx as usize, self.exprs.len());
        self.var(dbj_idx);
    }

    fn parse_es(&mut self, idx: u32, ws: &mut Iter<&str>) {
        let universe = self.parse_universe(ws);
        assert_eq!(idx as usize, self.exprs.len());
        self.sort(universe);
    }

    fn parse_ec(&mut self, idx: u32, ws: &mut Iter<&str>) {
        let name = self.parse_name(ws);
        let universes = self.parse_universes(ws);
        assert_eq!(idx as usize, self.exprs.len());
        self.mk_const(name, universes);
    }

    fn parse_ea(&mut self, idx: u32, ws: &mut Iter<&str>) {
        let fun = self.parse_expr(ws);
        let arg = self.parse_expr(ws);
        assert_eq!(idx as usize, self.exprs.len());
        self.app(fun, arg);
    }

    fn parse_el(&mut self, idx: u32, ws: &mut Iter<&str>) {
        self.parse_info(ws);
        let name = self.parse_name(ws);
        let tipo = self.parse_expr(ws);
        let body = self.parse_expr(ws);
        assert_eq!(idx as usize, self.exprs.len());
        self.lambda(name, tipo, body);
    }

    fn parse_ep(&mut self, idx: u32, ws: &mut Iter<&str>) {
        self.parse_info(ws);
        let name = self.parse_name(ws);
        let tipo = self.parse_expr(ws);
        let body = self.parse_expr(ws);
        assert_eq!(idx as usize, self.exprs.len());
        self.pi(name, tipo, body);
    }

    fn parse_ez(&mut self, idx: u32, ws: &mut Iter<&str>) {
        let name = self.parse_name(ws);
        let tipo = self.parse_expr(ws);
        let val = self.parse_expr(ws);
        let body = self.parse_expr(ws);
        assert_eq!(idx as usize, self.exprs.len());
        self.mk_let(name, tipo, val, body);
    }

    fn parse_ej(&mut self, idx: u32, ws: &mut Iter<&str>) {
        let name = self.parse_name(ws);
        let n_idx = self.parse_u32(ws);
        let structure = self.parse_expr(ws);
        assert_eq!(idx as usize, self.exprs.len());
        self.proj(name, n_idx, structure);
    }
    
    fn parse_eln(&mut self, idx: u32, ws: &mut Iter<&str>) {
        let ptr = self.parse_u128(ws);
        assert_eq!(idx as usize, self.exprs.len());
        self.nat_lit(ptr);
    }

    fn parse_els(&mut self, idx: u32, ws: &mut Iter<&str>) {
        let ptr = self.parse_hex_string(ws);
        assert_eq!(idx as usize, self.exprs.len());
        self.str_lit(ptr);
    }


    fn parse_rec_rule(&mut self, ws: &mut Iter<&str>) -> RecRulePtr<'a> {
        let idx = self.parse_u32(ws);
        assert!(self.rec_rules.get_index(idx as usize).is_some());
        Ptr::from(idx as usize)
    }

    fn parse_name(&mut self, ws: &mut Iter<&str>) -> NamePtr<'a> {
        let idx = self.parse_u32(ws);
        assert!(self.names.get_index(idx as usize).is_some());
        Ptr::from(idx as usize)
    }
    
    fn parse_names(&mut self, ws: &mut Iter<&str>, limit: u32) -> Vec<NamePtr<'a>> {
        let mut name_ptrs = Vec::new();
        for _ in 0..limit {
            let x = self.parse_name(ws);
            name_ptrs.push(x);
        }
        name_ptrs
    }
    
    fn parse_universe(&mut self, ws: &mut Iter<&str>) -> UniversePtr<'a> {
        let idx = self.parse_u32(ws);
        assert!(self.universes.get_index(idx as usize).is_some());
        Ptr::from(idx as usize)
    }
    
    fn parse_universes(&mut self, ws: &mut Iter<&str>) -> UparamsPtr<'a> {
        let mut universes = Vec::new();
        while ws.len() > 0 {
            let x = self.parse_universe(ws);
            universes.push(x)
        }
        self.alloc_uparams(universes)    
    }

    fn parse_expr(&mut self, ws: &mut Iter<&str>) -> ExprPtr<'a> {
        let idx = self.parse_u32(ws);
        assert!(self.exprs.get_index(idx as usize).is_some());
        Ptr::from(idx as usize)
    }
    
    fn parse_u32(&mut self, ws: &mut Iter<&str>) -> u32 {
        ws.next().expect(&format!("Valore non trovato, linea {}",*COUNTER.lock().unwrap())).parse::<u32>().expect(&format!("Valore diverso da un u32, linea {}", *COUNTER.lock().unwrap()))
    }
    
    fn parse_u128(&mut self, ws: &mut Iter<&str>) -> u128 {
        ws.next().expect(&format!("Valore non trovato, linea {}",*COUNTER.lock().unwrap())).parse::<u128>().expect(&format!("Valore diverso da un u64, linea {}", *COUNTER.lock().unwrap()))
    }
    
    fn parse_u64(&mut self, ws: &mut Iter<&str>) -> u64 {
        ws.next().expect(&format!("Valore non trovato, linea {}",*COUNTER.lock().unwrap())).parse::<u64>().expect(&format!("Valore diverso da un u64, linea {}", *COUNTER.lock().unwrap()))
    }
    
    fn parse_bool(&mut self, ws: &mut Iter<&str>) -> bool {
        let s = ws.next().expect(&format!("valore non trovato, linea {}", *COUNTER.lock().unwrap()));
        match *s{
            "0" => false,
            "1" => true,
            owise => panic!("Manca un valore (0 | 1 ), trovato {:?} linea = {}",owise, *COUNTER.lock().unwrap()),
        }
    }

    fn parse_info(&mut self, ws: &mut Iter<&str>) {
        let s = ws.next().expect(&format!("Manca un valore (#BD | #BI | #BC | #BS), linea {}", *COUNTER.lock().unwrap()));
        match *s {
            "#BD" | "#BI" | "#BC" | "#BS" => {}
            _ => panic!("valore {:?} non valido in linea {}", s, *COUNTER.lock().unwrap()),
        }
    }

    fn parse_hint(&mut self, ws: &mut Iter<&str>)  {
        let h = ws.next().expect(&format!("Valore non trovato, linea {}",*COUNTER.lock().unwrap()));
        match *h {
            "O" | "A" => {}
            "R" => { self.parse_u32(ws); }
             owise => panic!("Manca un valore (O | A | R), trovato {:?} linea = {}", owise, *COUNTER.lock().unwrap()),
        }
    }

    fn parse_str(&mut self, ws: &mut Iter<&str>) -> String {
        let s = ws.next().unwrap();
        s.to_string()
    }

    pub fn parse_hex_string(&mut self, ws: &mut Iter<&str>) -> String {
        ws.map(|hex| { u8::from_str_radix(hex, 16).unwrap() as char }).collect()
    }

    fn parse_param(&mut self, ws: &mut Iter<&str>) -> UniversePtr<'a> {
        let name = self.parse_name(ws);
        let hash = hash64!(PARAM_HASH, name);
        let val = Param {name , hash };
        let idx = self.universes.get_index_of(&val).unwrap();
        Ptr::from(idx as usize)
    }

    fn parse_uparams(&mut self, ws: &mut Iter<&str>) -> UparamsPtr<'a> {
        let mut universes = Vec::new();
        while ws.len() > 0 {
            let universe_ptr = self.parse_param(ws);
            if universes.contains(&universe_ptr){
                panic!("Parametro universale già inserito, linea {}", *COUNTER.lock().unwrap());
            }
            universes.push(universe_ptr)
        }
        self.alloc_uparams(universes)
    }
}
