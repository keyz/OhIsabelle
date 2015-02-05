theory Ch3InClass
imports Main Chapter2
begin

type_synonym var = string

datatype exp =
    Const const
  | Prim primitive exp 
  | IfE exp exp exp
  | VarE var
  | LetE var exp exp

abbreviation consti :: "int \<Rightarrow> exp" where "consti n \<equiv> Const (IntC n)"
abbreviation constb :: "bool \<Rightarrow> exp" where "constb b \<equiv> Const (BoolC b)" 
  
type_synonym env = "(var \<times> const) list"

fun lookup :: "'a \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'b option" where
  "lookup k [] = None" |
  "lookup k ((k',v)#ls) = (if k = k' then Some v else lookup k ls)"

primrec interp :: "exp \<Rightarrow> env \<Rightarrow> result" where
  "interp (VarE x) \<rho> =
        (case (lookup x \<rho>) of 
          None \<Rightarrow> Error 
        | Some c \<Rightarrow> Res c)" |
  "interp (LetE x e1 e2) \<rho> = 
        (case interp e1 \<rho> of 
          Res c \<Rightarrow> interp e2 ((x,c)#\<rho>)
        | Error \<Rightarrow> Error)" |
  "interp (Const c) \<rho> = Res c" |
  "interp (Prim p e) \<rho> =
        (case interp e \<rho> of 
          Res c \<Rightarrow> eval_prim p c
        | Error \<Rightarrow> Error)" |
  "interp (IfE e1 e2 e3) \<rho> =
        (case interp e1 \<rho> of
          Res (BoolC True) \<Rightarrow> interp e2 \<rho>
        | Res (BoolC False) \<Rightarrow> interp e3 \<rho>
        | _ \<Rightarrow> Error)" 

definition eval :: "exp \<Rightarrow> result" where "eval e = interp e []"
declare eval_def[simp]

theorem "eval (LetE x (Const (IntC 0)) (LetE x (Const (IntC 1)) (VarE x)))
         = Res (IntC 1)" by simp

type_synonym ty_env = "(var \<times> ty) list"

inductive well_typed :: "ty_env \<Rightarrow> exp \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ : _" [60,60,60] 59) where
  wt_const[intro!]: "\<lbrakk> const_type c = T \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Const c : T" |
  wt_prim[intro!]: "\<lbrakk> \<Gamma> \<turnstile> e : T1; prim_type p = (T1, T2) \<rbrakk> 
                    \<Longrightarrow> \<Gamma> \<turnstile> Prim p e : T2" |
  wt_if[intro!]: "\<lbrakk> \<Gamma> \<turnstile> e1 : BoolT; \<Gamma> \<turnstile> e2 : T; \<Gamma> \<turnstile> e3 : T \<rbrakk> 
                    \<Longrightarrow> \<Gamma> \<turnstile> IfE e1 e2 e3 : T" |
  wt_var[intro!]: "\<lbrakk> lookup x \<Gamma> = Some T \<rbrakk>
    \<Longrightarrow> \<Gamma> \<turnstile> VarE x : T" |
  wt_let[intro!]: "\<lbrakk> \<Gamma> \<turnstile> e1 : T1; (x,T1)#\<Gamma> \<turnstile> e2 : T2 \<rbrakk>
    \<Longrightarrow> \<Gamma> \<turnstile> LetE x e1 e2 : T2"

inductive_cases
  inv_wt_const[elim!]: "\<Gamma> \<turnstile> Const c : T" and
  inv_wt_prim[elim!]: "\<Gamma> \<turnstile> Prim p e : T" and
  inv_wt_if[elim!]: "\<Gamma> \<turnstile> IfE e1 e2 e3 : T" and
  inv_wt_var[elim!]: "\<Gamma> \<turnstile> VarE x : T" and
  inv_wt_let[elim!]: "\<Gamma> \<turnstile> LetE x e1 e2 : T"

primrec subst :: "var \<Rightarrow> const \<Rightarrow> exp \<Rightarrow> exp" ("[_\<mapsto>_] _" [72,72,72] 71) where
  "[x\<mapsto>c] (Const c') = (Const c')" |
  "[x\<mapsto>c] (VarE y) = (if x = y then (Const c) else (VarE y))" |
  "[x\<mapsto>c] (Prim p e1) = Prim p ([x\<mapsto>c]e1)" |
  "[x\<mapsto>c] (IfE e1 e2 e3) = IfE ([x\<mapsto>c]e1) ([x\<mapsto>c]e2) ([x\<mapsto>c]e3)" |
  "[x\<mapsto>c] (LetE y e1 e2) = 
           (if x = y then LetE y ([x\<mapsto>c]e1) e2
            else LetE y ([x\<mapsto>c]e1) ([x\<mapsto>c]e2))"

inductive reduce :: "exp \<Rightarrow> exp \<Rightarrow> bool" (infix "\<longmapsto>" 70) where
  r_let[intro!]: "LetE x (Const c) e \<longmapsto> ([x\<mapsto>c]e)" |
  c_let[intro!]: "\<lbrakk> e1 \<longmapsto> e1' \<rbrakk> \<Longrightarrow> LetE x e1 e2 \<longmapsto> LetE x e1' e2" |
  r_prim[intro!]: "\<lbrakk> eval_prim p c = Res c' \<rbrakk>
                     \<Longrightarrow> Prim p (Const c) \<longmapsto> Const c'" |
  c_prim[intro!]: "\<lbrakk> e \<longmapsto> e' \<rbrakk> \<Longrightarrow> Prim p e \<longmapsto> Prim p e'" |
  r_if_true[intro!]: "IfE (constb True) e2 e3 \<longmapsto> e2" |
  r_if_false[intro!]: "IfE (constb False) e2 e3 \<longmapsto> e3" |
  c_if[intro!]: "\<lbrakk> e1 \<longmapsto> e1' \<rbrakk> \<Longrightarrow> IfE e1 e2 e3 \<longmapsto> IfE e1' e2 e3" 

inductive reduces :: "exp \<Rightarrow> exp \<Rightarrow> bool" (infix "\<longmapsto>*" 70) where
 red_nil[intro!]: "(e::exp) \<longmapsto>* e" |
 red_cons[intro!]: "\<lbrakk> (e1::exp) \<longmapsto> e2; e2 \<longmapsto>* e3 \<rbrakk> \<Longrightarrow> e1 \<longmapsto>* e3"

primrec exp2res :: "exp \<Rightarrow> result" where
  "exp2res (Const c) = Res c" |
  "exp2res (Prim p e) = Error" |
  "exp2res (IfE e1 e2 e3) = Error" |
  "exp2res (LetE x e1 e2) = Error" |
  "exp2res (VarE x) = Error" 

(* define eval *)

theorem progress: assumes wt: "\<Gamma> \<turnstile> e : T" and g: "\<Gamma> = []"
  shows "(\<exists> c. e = Const c) \<or> (\<exists> e'. e \<longmapsto> e')" (is "?P e")
using wt g
proof (induction \<Gamma> e T rule: well_typed.induct)
  case (wt_const c T \<Gamma>) thus "?P (Const c)" by simp
next
  case (wt_prim \<Gamma> e T1 p T2)
  from wt_prim have 1: "(\<exists>c. e = Ch3InClass.exp.Const c) \<or> (\<exists>a. e \<longmapsto> a)" by simp
  show "?P (Prim p e)"
  proof (rule disjI2)
    from 1 show "\<exists>e'. Ch3InClass.exp.Prim p e \<longmapsto> e'"
    proof
      assume "\<exists>c. e = Const c"
      from this obtain c where e: "e = Const c" by blast
      from wt_prim have 2: "prim_type p = (T1,T2)" by simp
      from wt_prim e have 3: "const_type c = T1" apply simp apply blast done
      from prim_type_safe 2 3 obtain c' where ep: "eval_prim p c = Res c'"
        and cpt: "const_type c' = T2" apply blast done
      from ep have 4: "Prim p (Const c) \<longmapsto> Const c'"  by blast
      with e show ?thesis by blast
    next
      assume "\<exists>a. e \<longmapsto> a"
      from this obtain e' where ered: "e \<longmapsto> e'" by blast
      from ered have "Prim p e \<longmapsto> Prim p e'" by blast
      thus ?thesis by blast
    qed
  qed
  oops
    

abbreviation remove_bind :: "var \<Rightarrow> ty_env \<Rightarrow> ty_env \<Rightarrow> bool" where
  "remove_bind z \<Gamma> \<Gamma>' \<equiv>
      \<forall>x T. x\<noteq>z \<and> lookup x \<Gamma> = Some T \<longrightarrow> lookup x \<Gamma>' = Some T"

abbreviation subseteq :: "ty_env \<Rightarrow> ty_env \<Rightarrow> bool" (infixl "\<preceq>" 80) where
  "\<Gamma> \<preceq> \<Gamma>' \<equiv> \<forall> x T. lookup x \<Gamma> = Some T \<longrightarrow> lookup x \<Gamma>' = Some T"

lemma env_weakening[rule_format]:
  "\<Gamma> \<turnstile> e : T \<Longrightarrow> \<forall> \<Gamma>'. \<Gamma> \<preceq> \<Gamma>' \<longrightarrow> \<Gamma>' \<turnstile> e : T" 
  by (induct rule: well_typed.induct) auto

lemma substitution_preserves_types[rule_format]:
  assumes wtm: "\<Gamma> \<turnstile> e : A" and lx: "lookup x \<Gamma> = Some B"
  and rg: "remove_bind x \<Gamma> \<Gamma>'" and cb: "const_type c = B"
  shows "\<Gamma>' \<turnstile> [x \<mapsto> c]e : A" 
  sorry

theorem preservation:
  fixes e::exp and T::ty
  assumes wt: "[] \<turnstile> e : T" and red: "e \<longmapsto> e'" shows "[] \<turnstile> e' : T"
sorry

end