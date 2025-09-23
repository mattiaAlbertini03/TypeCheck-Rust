use crate::declar::Declar::*;
use crate::name::NamePtr;
use crate::expr::{Expr::*, ExprPtr};
use crate::universe::{UniversePtr, UparamsPtr};
use crate::util::ExportFile;

impl<'t> ExportFile<'t> {
    
    pub fn check_all_declars(&mut self) { 
        for d in self.declars.clone().into_values() {
            self.check_info(d.uparams(), d.ty(), d.val(), d.name());
        }
        println!("\nNessun errore nelle dichiarazioni");
    }

    pub fn check_info(&mut self, uparams: UparamsPtr<'t>, ty: ExprPtr<'t>, val: Option<ExprPtr<'t>>, name: NamePtr<'t>) {
        
        let em = self.read_uparams(uparams);
        if !em.is_empty() {
            self.controllo_parametri(ty, uparams);
        }
        self.is_sort(ty);
        if val.is_some() {
            let val = val.unwrap();
            if !em.is_empty() {
                self.controllo_parametri(val, uparams);
            }
            let v = self.infer(val);

            if !self.def_eq(ty, v){
                println!("Errore nella dichiarazione {:?}: tipo della definizione non coincide. ty={:?}, val_type={:?}", name.idx, self.read_expr(ty), self.read_expr(v));
            }
        }

    }

    pub fn controllo_parametri(&mut self, ty: ExprPtr<'t>, ups : UparamsPtr<'t>) {
        match self.read_expr(ty){
            FreeVar {..} | NatLit { .. } | StrLit { .. } | Var { .. } => {}
            Sort { universe, .. } => { 
                assert!(self.contiene_param(universe, ups), "controllo_parametri: Sort non contiene parametri richiesti: {:?}", self.read_universe(universe));
            }
            Const { universes, .. } => { 
                for u in self.read_uparams(universes).iter().copied() {
                    assert!(self.contiene_param(u, ups), "controllo_parametri: Const con universo esterno non accettato {:?}", self.read_universe(u));
                }
            }
            App { fun, arg, .. } => {
                self.controllo_parametri(fun, ups);
                self.controllo_parametri(arg, ups);
            }
            Pi { ty, body, .. } => {
                self.controllo_parametri(ty, ups);
                self.controllo_parametri(body, ups);
            }
            Lambda { ty, body, .. } => {
                self.controllo_parametri(ty, ups);
                self.controllo_parametri(body, ups);
            }
            Let { ty, val, body, .. } => {
                self.controllo_parametri(ty, ups);
                self.controllo_parametri(val, ups);
                self.controllo_parametri(body, ups);
            }
            Proj { structure, .. } => {
                self.controllo_parametri(structure, ups);
            }
        }
    }

    pub fn infer(&mut self, e: ExprPtr<'t>) -> ExprPtr<'t> {
        if self.infers.contains_key(&e) {
            return self.read_infer(e)
        }
        let out = match self.read_expr(e) {
            Var { .. } => panic!("infer sulla var, {:?}", self.read_expr(e)),

            FreeVar { ty, .. } => ty,

            NatLit { .. } => {
                let name = self.mk_str(self.anonymous(), "Nat".to_string());
                let vuoto = self.alloc_uparams(vec![]);
                self.mk_const(name, vuoto )
            }
            StrLit { .. } => {
                let name = self.mk_str(self.anonymous(), "String".to_string());
                let vuoto = self.alloc_uparams(vec![]);
                self.mk_const(name, vuoto )
            }
            Sort { universe, .. } => {
                let s = self.succ(universe);
                self.sort(s)
            }
            Const {name, universes, ..} => {
                let dec =  self.read_declar(name);
                if dec.uparams() == universes {
                    return dec.ty()
                }
                self.subst_expr_universes(dec.ty(), dec.uparams(), universes)
            }
            Let { ty, val, body, .. } =>  {
                self.is_sort(ty);
                let v = self.infer(val);
                assert!(self.def_eq(ty, v), "Errore nella let: ty={:?}, val={:?}", self.read_expr(ty), self.read_expr(v));
                let inst = self.inst(body, val, 0);
                self.infer(inst)
            }

            Pi {ty, body, ..} => {
                let l = self.is_sort(ty);
                let free = self.free_var(ty);
                let b = self.inst(body, free, 0);
                let r = self.is_sort(b);
                let imax = self.imax(l, r);
                self.sort(imax)
            }
            Lambda {name, ty, body, ..} => {
                self.is_sort(ty);
                let free = self.free_var(ty);
                let inst = self.inst(body, free, 0);  
                let inf = self.infer(inst);
                let abstr = self.abstr(inf, free, 0);
                self.pi(name, ty, abstr)
            } 
            App {fun, arg, ..} => {
                let infer = self.infer(fun);
                let whnf_fun = self.whnf(infer);
                match self.read_expr(whnf_fun) {
                    Pi {ty, body, ..} => {
                        let a = self.infer(arg);
                        assert!(self.def_eq(ty, a),  "Errore nel App(Pi)) \n ty={:?},\n a={:?}", self.read_expr(ty), self.read_expr(a));
                        self.inst(body, arg, 0)
                    }
                    _ => panic!("Non è stato trovato un Pi dentro App"),
                }
            }
            
            Proj {name, idx, structure, ..} => {
                let s = self.infer(structure);
                let mut s = self.whnf(s);
                let mut args = Vec::new();
                while let App { fun, arg, .. } = self.read_expr(s) {
                    args.push(arg);
                    s = fun;
                }
                args.reverse();
                if let Const {name : name_c, universes, .. } = self.read_expr(s) {
                    assert_eq!(name, name_c);
                    if let Inductive {all_ctor_names, num_indices, .. } = self.read_declar(name) {
                        assert_eq!(all_ctor_names.len(), 1, "proj usato su un elemento che non è una struttura");
                        assert_eq!(num_indices, 0, "proj usato su un elemento che non è una struttura");
                        if let ctor @ Constructor{num_params, .. } = self.read_declar(all_ctor_names[0]){
                            let mut ctor_ty = self.subst_expr_universes(ctor.ty(), ctor.uparams(), universes);
                            for arg in args.iter().take(num_params as usize) {
                                ctor_ty = self.whnf(ctor_ty);
                                match self.read_expr(ctor_ty) {
                                    Pi { body, .. } => ctor_ty = self.inst(body, *arg, 0),
                                    _ => panic!("Proj: Non è stato trovato un pi per il param"),
                                }
                            }
                            for i in 0..idx {
                                ctor_ty = self.whnf(ctor_ty);
                                match self.read_expr(ctor_ty) {
                                    Pi { body, .. } => {
                                        let p = self.proj(name, i, structure);
                                        ctor_ty = self.inst(body, p, 0);
                                    }
                                    _ => panic!("Proj: Non è stato trovato un pi per l'idx"),
                                }
                            }
                            ctor_ty = self.whnf(ctor_ty);
                            match self.read_expr(ctor_ty) {
                                Pi { ty, .. } => return ty,
                                _ => panic!("proj: Non trovato un Pi da ritornare"),
                            }
                        }
                        panic!("proj: constructor non trovato");
                    }
                    panic!("proj inductive non trovato");
                }
                panic!("non trovata una const");
            }
        };
        self.infers.insert(e, out);
        out
    }

    pub fn whnf(&mut self, v: ExprPtr<'t>) -> ExprPtr<'t> {
        if self.whnfs.contains_key(&v) {
            return self.read_whnf(v)
        }
        let mut e = v;
        let out = loop {
            match self.read_expr(e) {
                Let { val, body, .. } => {
                    e = self.inst(body, val, 0);
                }
                
                Const {name, universes, ..} => {
                    let d = self.read_declar(name);
                    if let Some(v) = d.val() {
                        e = self.subst_expr_universes(v, d.uparams(), universes);
                    } else {
                        break e;
                    }
                }
                
                Proj { idx, structure, .. } => {
                    let mut x = self.whnf(structure);
                    let mut args = Vec::new();
                    while let App { fun, arg, .. } = self.read_expr(x) {
                        args.push(arg);
                        x = fun;
                    }        
                    args.reverse();
                    if let Const { name, .. } = self.read_expr(x) {
                        if let Constructor { num_params, .. } = self.read_declar(name) {
                            assert!(args.len() > (idx + num_params) as usize);
                            e = args[(idx + num_params) as usize];
                        } 
                    } else {
                        break e;
                    }
                }

                App { .. } => {
                    let mut args = Vec::new();
                    while let App { fun, arg, .. } = self.read_expr(e) {
                        args.push(arg);
                        e = fun;
                    }
                    let mut args_apply = Vec::new();
                    while let (Lambda {body, .. }, Some(pop)) = (self.read_expr(e), args.pop()) {
                        e = body;
                        args_apply.push(pop);
                    }
                    for a in args_apply {
                        e = self.inst(e, a, 0);
                    }
                    args.reverse();
                    for a in args {
                        e = self.app(e, a);
                    }
                    break e;
                }
                
                _ => break e,
            }
        };
        self.whnfs.insert(v, out);
        out
    }

   pub fn is_sort(&mut self, mut e: ExprPtr<'t>) -> UniversePtr<'t> {
       loop {
            let expr = self.infer(e);
            let expr = self.whnf(expr);
            match self.read_expr(expr) {
                Sort {universe, ..} => return universe,
                
                FreeVar {ty, ..} => e = ty,
                
                Const { name, universes, .. } => {
                    let d = self.read_declar(name);
                    e = self.subst_expr_universes(d.ty(), d.uparams(), universes);
                }
                
                NatLit {..} | StrLit {..} => panic!("valore non Sort, {:?}", self.read_expr(expr)),
            
                _ => e = expr,
            }
       }
    }

    pub fn def_eq(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        println!("def_EQ \n ty={:?},\n a={:?}", self.read_expr(x), self.read_expr(y));

        if x == y {
            return true;
        }

        match self.read_expr_pair(x, y){

            ( Var { .. }, Var { .. } ) => panic!("trovato Var durante il def_eq"),

            ( FreeVar {idx: idx_x, .. }, FreeVar {idx: idx_y, ..} ) => return idx_x == idx_y,
            
            ( Sort {universe : u_x, .. }, Sort {universe : u_y, ..} ) => return self.leq(u_x, u_y, 0) && self.leq(u_y, u_x, 0),
            
            ( Const {name: n1, universes: u1, ..}, Const {name: n2, universes: u2, ..}) if n1 == n2 => return self.leq_many(u1, u2),
            
            ( Const {..}, Const {..}) => {
                if self.unit_like(x,y) || self.unit_like(y, x) {
                    return true
                }
            }
            
            ( App {fun: f1, arg: a1, ..}, App {fun: f2, arg: a2, ..}) => {
                if self.def_eq(f1, f2) {
                    return self.def_eq(a1, a2 )
                }
            }

            ( Lambda {ty: ty1, body: b1, ..}, Lambda {ty: ty2, body: b2, ..}) | ( Pi {ty: ty1, body: b1, ..}, Pi {ty: ty2, body: b2, ..}) => {
                if self.def_eq(ty1, ty2) {
                    let free = self.free_var(ty1);
                    let a = self.inst(b1, free, 0);
                    let b = self.inst(b2, free, 0);
                    return self.def_eq(a, b)
                }
            }
            
            ( Let {val: v1, body: b1, ..}, Let {val: v2, body: b2, ..} ) => {
                if self.def_eq(v1, v2) {
                    let x1 = self.inst(b1, v1, 0);
                    let y1 = self.inst(b2, v2, 0);
                    return self.def_eq(x1, y1)
                }
            }
            
            ( Proj { name: n1, idx: i1, structure: s1, .. }, Proj { name: n2, idx: i2, structure: s2, .. }) => {
                return n1 == n2 && i1 == i2 && self.def_eq(s1, s2);
            }
        

            ( Lambda {..}, _ ) => {
                let i_y = self.infer(y);
                let whnf_y = self.whnf(i_y);
                if let Pi {name, ty, .. } = self.read_expr(whnf_y) {
                    let var = self.var(0);
                    let lambda = self.lambda(name, ty, var);
                    let app = self.app(lambda, y);
                    return self.def_eq(x, app)
                }
            }
            
            ( _, Lambda {..} ) => {
                let i_x = self.infer(x);
                let whnf_x = self.whnf(i_x);
                if let Pi {name, ty, .. } = self.read_expr(whnf_x) {
                    let var = self.var(0);
                    let lambda = self.lambda(name, ty, var);
                    let app = self.app(lambda, x);
                    return self.def_eq(app, y)
                }
            }
            
            (App {..}, _) => {
                if self.def_eq_struct(y,x) {
                    return true
                }
            }
            
            (_, App {..} ) => {
                if self.def_eq_struct(x,y) {
                    return true
                }
            }
        
            _ => {}
        }

        let infer_x = self.infer(x);
        let infer_y = self.infer(y);
        if self.is_sort(infer_x) == self.zero() {
            if self.is_sort(infer_y) == self.zero() {
                return self.def_eq(infer_x, infer_y)
            }
        }

        let whnf_x = self.whnf(x);
        let whnf_y = self.whnf(y);

        if whnf_x != x || whnf_y != y {
            return self.def_eq(whnf_x, whnf_y);
        }
        
        false
    }

    pub fn unit_like(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        if let Const{name: n1, universes, ..} = self.read_expr(x){
            if let Inductive{all_ctor_names, num_indices, .. } = self.read_declar(n1){
                if all_ctor_names.len() == 1 && num_indices == 0 {
                    let infer_x = self.infer(x);
                    let infer_y = self.infer(y);
                    if self.def_eq(infer_x, infer_y) {
                        if let Constructor{uparams, ..} = self.read_declar(all_ctor_names[0]) {
                            let u1 = self.read_uparams(universes);
                            let u2 = self.read_uparams(uparams);
                            if u1.len() == u2.len() {
                                return true
                            }
                        }
                    }
                }
            }
        }
        false
    }
   
    pub fn def_eq_struct(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        let mut args = Vec::new();
        let mut s = y;
        while let App { fun, arg, .. } = self.read_expr(s) {
            args.push(arg);
            s = fun;
        }
        args.reverse();
        if let Const {name, .. } = self.read_expr(s) {
            if let Constructor{num_params, num_fields, parent, .. } = self.read_declar(name){
                if let Inductive {all_ctor_names, num_indices,.. } = self.read_declar(parent) {
                    if all_ctor_names.len() == 1 && num_indices == 0 {
                        let num = (num_params + num_fields) as usize;
                        if args.len() == num {
                            let inf_x = self.infer(x);
                            let inf_y = self.infer(y);
                            if self.def_eq(inf_x, inf_y) {    
                                for i in 0..num_fields as usize {
                                    let proj = self.proj(parent, num_params + i as u32, x);
                                    if !self.def_eq(proj, args[i + num_params as usize]) {
                                        return false
                                    }
                                }
                                return true
                            }
                        }
                    }
                }
            }
        }
        false
    }
}
