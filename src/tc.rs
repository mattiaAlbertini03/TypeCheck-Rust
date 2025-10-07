use crate::declar::*;
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
        self.infer_sort_of(ty);
        if val.is_some() {
            let val = val.unwrap();
            if !em.is_empty() {
                self.controllo_parametri(val, uparams);
            }
            let v = self.infer(val);

            assert!(self.def_eq(ty, v), "Errore nella dichiarazione {:?}: tipo della definizione non coincide. ty={:?}, val_type={:?}", 
                         name.idx, self.read_expr(ty), self.read_expr(v));
        }
        println!("Dichiarazione {:?} scritta corretamente", name.idx);
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

    pub fn unfold_app(&mut self, x: ExprPtr<'t>) -> (ExprPtr<'t>, Vec<ExprPtr<'t>>) {
        let mut e = x;
        let mut args = Vec::new();
        while let App { fun, arg, .. } = self.read_expr(e) {
            args.push(arg);
            e = fun;
        }
        args.reverse();
        (e, args)
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
                self.infer_sort_of(ty);
                let v = self.infer(val);
                assert!(self.def_eq(ty, v), "Errore nella let: ty={:?}, val={:?}", self.read_expr(ty), self.read_expr(v));
                let inst = self.inst(body, val, 0);
                self.infer(inst)
            }

            Pi {ty, body, ..} => {
                let l = self.infer_sort_of(ty);
                let free = self.free_var(ty);
                let b = self.inst(body, free, 0);
                let r = self.infer_sort_of(b);
                let imax = self.imax(l, r);
                self.sort(imax)
            }
            
            Lambda {name, ty, body, ..} => {
                self.infer_sort_of(ty);
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
                        assert!(self.def_eq(ty, a), "Errore nel App(Pi)) \n ty={:?},\n a={:?}", self.read_expr(ty), self.read_expr(a));
                        self.inst(body, arg, 0)
                    }
                    _ => panic!("Non è stato trovato un Pi dentro App\n {:?}", self.read_expr(e)),
                }
            }
            
            Proj {name, idx, structure, ..} => {
                let s = self.infer(structure);
                let s = self.whnf(s);
                let (s, args) = self.unfold_app(s);
                if let Const {name : name_c, universes, .. } = self.read_expr(s) {
                    assert_eq!(name, name_c);
                    if let Inductive {all_ctor_names, num_indices, .. } = self.read_declar(name) {
                        if all_ctor_names.len() == 1 && num_indices == 0 {
                            if let Constructor{ty, uparams, num_params, .. } = self.read_declar(all_ctor_names[0]){
                                let mut ctor_ty = self.subst_expr_universes(ty, uparams, universes);
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
                        panic!("Non è una structure");
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
        let mut args = Vec::new();
        let mut e = v;
        let mut out = loop {
            match self.read_expr(e) {
                
                Let { val, body, .. } => e = self.inst(body, val, 0),
                 
                Const {name, ..} if matches!(self.read_declar(name), Recursor{..})=>{
                    if let Recursor{ all_inductive_names, num_params, num_indices, num_motives, num_minors, rec_rules, .. } = self.read_declar(name){
                        let tot_wtout_indices =  num_params + num_motives + num_minors;
                        let tot_wt_indices = tot_wtout_indices + num_indices;
                        
                        args.reverse();
                        let value = args[tot_wt_indices as usize]; 
                        
                        let whnf_v = self.whnf(value);
                        let (whnf_v, args_app) = self.unfold_app(whnf_v); 
                        
                        let mut no_find = true;
                        if let Const{name, ..} = self.read_expr(whnf_v){
                            if let Constructor{name, ..} = self.read_declar(name) {
                                no_find = false;
                                let mut no_rule = true;
                                for rule in rec_rules{
                                    let RecRule{ctor_name, num_fields, val, ..} = self.read_rec_rule(rule);
                                    if name == ctor_name {
                                        no_rule = false;
                                        let mut app = val;
                                        for arg in args.iter().take(tot_wtout_indices as usize) {
                                            app= self.app(app, *arg);
                                        }
                                        args.drain(0..tot_wtout_indices as usize);
                                        args.reverse();
                                        
                                        for arg in args_app.iter().take(num_fields as usize) {
                                            app= self.app(app, *arg);
                                        }
                                        
                                        e = self.whnf(app);
                                    }
                                }
                                if no_rule {
                                    panic!("Non esiste una regola di riduzione per il Constructor di questa Recursor");
                                }
                            } 
                        }
                        
                        if no_find {
                            no_find = true;
                            if all_inductive_names.len() == 1 {
                                if let Inductive {all_ctor_names, num_indices, .. } = self.read_declar(name) {
                                    if all_ctor_names.len() == 1 && num_indices == 0 {
                                        if let Constructor{num_params, num_fields, .. } = self.read_declar(all_ctor_names[0]){
                                            no_find = false;
                                            let mut app = whnf_v;
                                            for arg in args.iter().take(tot_wtout_indices as usize) {
                                                app= self.app(app, *arg);
                                            }
                                            args.drain(0..tot_wtout_indices as usize);
                                            args.reverse();

                                            if num_params != 0{
                                                for i in 0..num_fields {
                                                    let proj = self.proj(name, i, whnf_v);
                                                    app = self.app(app, proj);
                                                }
                                            }
                                            e = self.whnf(app);
                                        }
                                    }
                                }
                            }
                        }
                        if no_find {
                            args.reverse();
                            break e;
                        }
                    } else{
                        panic!("Elemento Recursor non Recursor");
                    }
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
                    let x = self.whnf(structure);
                    let (x, args_proj) = self.unfold_app(x);

                    if let Const { name, .. } = self.read_expr(x) {
                        if let Constructor { num_params, .. } = self.read_declar(name) {
                            e = args_proj[(idx + num_params) as usize];
                        } else {
                            break e;
                        }
                    } else {
                        break e;
                    }
                }

                App { fun, arg, .. } => {
                    args.push(arg);
                    e = fun;
                }

                Lambda { body, .. } => {
                    if let Some(pop) = args.pop() {
                        e = self.inst(body, pop, 0); 
                    } else {
                        break e; 
                    }
                }
                
                _ => break e,
           }
        };
        
        args.reverse();
        for a in args {
            out = self.app(out, a);
        }
        
        self.whnfs.insert(v, out);
        out
    }

    pub fn infer_sort_of(&mut self, e: ExprPtr<'t>) -> UniversePtr<'t> {
        let expr = self.infer(e);
        let expr = self.whnf(expr);
        match self.read_expr(expr) {
            Sort {universe, ..} => return universe,
            _=> panic!("valore non Sort, {:?}", self.read_expr(expr)),
        }
    }

    pub fn def_eq(&mut self, x: ExprPtr<'t>, y: ExprPtr<'t>) -> bool {
        
        if x == y {
            return true;
        }
        
        let x = self.whnf(x);
        let y = self.whnf(y); 

        let out = match self.read_expr_pair(x, y){
            
            ( Var { .. }, Var { .. } ) => panic!("trovato Var durante il def_eq"),

            ( FreeVar {idx: idx_x, .. }, FreeVar {idx: idx_y, ..} ) => idx_x == idx_y,
            
            ( Sort {universe : u_x, .. }, Sort {universe : u_y, ..} ) => self.leq(u_x, u_y, 0) && self.leq(u_y, u_x, 0),
            
            ( Const {name: n1, universes: u1, ..}, Const {name: n2, universes: u2, ..}) => n1 == n2 && self.eq_many(u1, u2),
                                                                                                                
            ( App {fun: f1, arg: a1, ..}, App {fun: f2, arg: a2, ..}) => self.def_eq(f1, f2) && self.def_eq(a1, a2 ), 

            ( Lambda {ty: ty1, body: b1, ..}, Lambda {ty: ty2, body: b2, ..}) | ( Pi {ty: ty1, body: b1, ..}, Pi {ty: ty2, body: b2, ..}) => {
                if self.def_eq(ty1, ty2) {
                    let free = self.free_var(ty1);
                    let a = self.inst(b1, free, 0);
                    let b = self.inst(b2, free, 0);
                    return self.def_eq(a, b)
                }
                false
            }
        

            ( Lambda {ty: ty_l, ..}, _ ) => {
                let infer_y = self.infer(y);
                if let Pi{ty: ty_p, ..} = self.read_expr(infer_y){
                    if self.def_eq(ty_l, ty_p) {
                        let free = self.free_var(ty_l);
                        let lambda = self.inst(x, free, 0);
                        let app = self.app(y, free);
                        return self.def_eq(lambda, app);
                    }
                }
                false
            }
            
            ( _, Lambda {ty: ty_l, ..} ) => {
                let infer_x = self.infer(x);
                if let Pi{ty: ty_p, ..} = self.read_expr(infer_x){
                    if self.def_eq(ty_l, ty_p) {
                        let free = self.free_var(ty_l);
                        let lambda = self.inst(y, free, 0);
                        let app = self.app(x, free);
                        return self.def_eq(lambda, app);
                    }
                }
                false
            }
            
            _ => false,
        };

        if out {
            return true
        }
       
        if self.def_eq_struct(x,y) {
            return true
        }

        if self.def_eq_struct(y, x) {
            return true
        }

        if self.unit_like(x,y) {
            return true
        }
        if self.unit_like(y, x) {
            return true
        }
        
        let infer_x = self.infer(x);
        let infer_y = self.infer(y);
        if self.infer_sort_of(infer_x) == self.zero() {
            if self.infer_sort_of(infer_y) == self.zero() {
                return self.def_eq(infer_x, infer_y)
            }
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
        let (s, args) = self.unfold_app(y);
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
