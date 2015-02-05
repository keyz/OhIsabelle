theory Ch2InClass
imports Main
begin

datatype const = IntC int | BoolC bool

datatype primitive = Inc | Dec | Neg | IsZero | Not

datatype exp =
    Const const
  | Prim primitive exp 
  | IfE exp exp exp

abbreviation ci :: "int \<Rightarrow> exp" where "ci n \<equiv> Const (IntC n)"
abbreviation cb :: "bool \<Rightarrow> exp" where "cb b \<equiv> Const (BoolC b)"

abbreviation p0 :: exp where "p0 \<equiv> ci 42"
abbreviation p1 :: exp where "p1 \<equiv> Prim Inc (ci 41)"
abbreviation p2 :: exp where "p2 \<equiv> Prim IsZero (ci 0)"
abbreviation p3 :: exp where "p3 \<equiv> IfE p2 p1 (ci 0)"
abbreviation p4 :: exp where "p4 \<equiv> Prim IsZero (ci 1)"
abbreviation p5 :: exp where "p5 \<equiv> IfE p4 (ci 0) p1"
abbreviation p6 :: exp where "p6 \<equiv> Prim Not (cb False)"

datatype result = Res const | Error

fun eval_prim :: "primitive \<Rightarrow> const \<Rightarrow> result" where
  "eval_prim Inc (IntC n) = Res (IntC (n + 1))" |
  "eval_prim Dec (IntC n) = Res (IntC (n - 1))" |
  "eval_prim Neg (IntC n) = Res (IntC (-n))" |
  "eval_prim IsZero (IntC n) = Res (BoolC (n=0))" |
  "eval_prim Not (BoolC b) = Res (BoolC (\<not> b))" |
  "eval_prim _ _ = Error"

primrec eval :: "exp \<Rightarrow> result" where
  "eval (Const c) = Res c" |
  "eval (Prim p e) =
        (case eval e  of 
          Res c \<Rightarrow> eval_prim p c
        | Error \<Rightarrow> Error)" |
  "eval (IfE e1 e2 e3) =
        (case eval e1 of
          Res (BoolC True) \<Rightarrow> eval e2
        | Res (BoolC False) \<Rightarrow> eval e3
        | _ \<Rightarrow> Error)"

theorem "eval p0 = Res (IntC 42)" by simp
theorem "eval p1 = Res (IntC 42)" by simp
theorem "eval p2 = Res (BoolC True)" by simp
theorem "eval p3 = Res (IntC 42)" by simp
theorem "eval p4 = Res (BoolC False)" by simp
theorem "eval p5 = Res (IntC 42)" by simp
theorem "eval p6 = Res (BoolC True)" by simp

datatype ty = IntT | BoolT

primrec prim_type :: "primitive \<Rightarrow> ty \<times> ty" where
   "prim_type Inc = (IntT, IntT)" |
   "prim_type Dec = (IntT, IntT)" |
   "prim_type Neg = (IntT, IntT)" |
   "prim_type IsZero = (IntT, BoolT)" |
   "prim_type Not = (BoolT, BoolT)" 

primrec const_type :: "const \<Rightarrow> ty" where
  "const_type (IntC n) = IntT" |
  "const_type (BoolC b) = BoolT"

inductive well_typed :: "exp \<Rightarrow> ty \<Rightarrow> bool" ("\<turnstile> _ : _" [60,60] 59) where
  wt_const[intro!]: "\<lbrakk> const_type c = T \<rbrakk> \<Longrightarrow> \<turnstile> Const c : T" |
  wt_prim[intro!]: "\<lbrakk> \<turnstile> e : T1; prim_type p = (T1, T2) \<rbrakk>
    \<Longrightarrow> \<turnstile> Prim p e : T2" |
  wt_if[intro!]: "\<lbrakk> \<turnstile> e1 : BoolT; \<turnstile> e2 : T; \<turnstile> e3 : T \<rbrakk>
    \<Longrightarrow> \<turnstile> IfE e1 e2 e3 : T"

inductive_cases
  inv_wt_const[elim!]: "\<turnstile> Const c : T" and
  inv_wt_prim[elim!]: "\<turnstile> Prim p e : T" and
  inv_wt_if[elim!]: "\<turnstile> IfE e1 e2 e3 : T"

theorem "\<turnstile> p0 : IntT" by auto
theorem "\<turnstile> p1 : IntT" by auto
theorem "\<turnstile> p2 : BoolT" by auto
theorem "\<turnstile> p3 : IntT" by auto
theorem "\<turnstile> p4 : BoolT" by auto
theorem "\<turnstile> p5 : IntT" by auto
theorem "\<turnstile> p6 : BoolT" by auto

lemma prim_type_safe:
  assumes pt: "prim_type p = (T1,T2)" and wt: "const_type c = T1"
  shows "\<exists> c'. eval_prim p c = Res c' \<and> const_type c' = T2"
  using pt wt
  apply (case_tac p)
  apply (case_tac c, simp, simp)+
  done

theorem type_safety:
assumes wt: "\<turnstile> e : T" shows "\<exists> c. eval e = Res c \<and> const_type c = T" (is "?P e T")
using wt
proof (induction e T rule: well_typed.induct)
  case (wt_const c T)
  from wt_const show "?P (Const c) T" by simp
next
  case (wt_prim e T1 p T2)
  from wt_prim obtain c where ct: "const_type c = T1" and
    ec: "eval e = Res c" by blast
  from wt_prim have pt: "prim_type p = (T1,T2)" by simp
  from pt ct have "\<exists> c'. eval_prim p c = Res c' \<and> const_type c' = T2"
    by (rule prim_type_safe)
  from this obtain c' where ep: "eval_prim p c = Res c'"
    and ct2: "const_type c' = T2" by blast
  from ec ep have 1: "eval (Prim p e) = Res c'" by simp
  from 1 ct2 show "?P (Prim p e) T2" by blast
  oops


inductive reduce :: "exp \<Rightarrow> exp \<Rightarrow> bool" (infix "\<longmapsto>" 70) where
  r_prim[intro!]: "\<lbrakk> eval_prim p c = Res c' \<rbrakk>
    \<Longrightarrow> Prim p (Const c) \<longmapsto> Const c'" |
  c_prim[intro!]: "\<lbrakk> e \<longmapsto> e' \<rbrakk> \<Longrightarrow> Prim p e \<longmapsto> Prim p e'" |
  r_if_true[intro!]: "IfE (cb True) e2 e3 \<longmapsto> e2" |
  r_if_false[intro!]: "IfE (cb False) e2 e3 \<longmapsto> e3" |
  c_if[intro!]: "\<lbrakk> e1 \<longmapsto> e1' \<rbrakk> \<Longrightarrow> IfE e1 e2 e3 \<longmapsto> IfE e1' e2 e3"

theorem "Prim Inc (Prim Inc (ci 40)) \<longmapsto> Prim Inc (ci 41)" by auto
theorem "IfE (cb True) (ci 42) (ci 0) \<longmapsto> ci 42" by auto
theorem "IfE (Prim IsZero (ci 1)) (ci 0) (ci 42)
         \<longmapsto> IfE (cb False) (ci 0) (ci 42)" by auto

inductive reduces :: "exp \<Rightarrow> exp \<Rightarrow> bool" (infix "\<longmapsto>*" 70) where
 red_nil[intro!]: "e \<longmapsto>* e" |
 red_cons[intro!]: "\<lbrakk> e1 \<longmapsto> e2; e2 \<longmapsto>* e3 \<rbrakk> \<Longrightarrow> e1 \<longmapsto>* e3"

primrec exp2res :: "exp \<Rightarrow> result" where
  "exp2res (Const c) = Res c" |
  "exp2res (Prim p e) = Error" |
  "exp2res (IfE e1 e2 e3) = Error"

abbreviation reducible :: "exp \<Rightarrow> bool" where
  "reducible e \<equiv> \<exists> e'. e \<longmapsto> e'"
 
definition eval_red :: "exp \<Rightarrow> result \<Rightarrow> bool" where
  "eval_red e r \<equiv> \<exists> e'. e \<longmapsto>* e'
      \<and> \<not> reducible e' \<and> exp2res e' = r"

theorem "eval_red (Prim Inc (Prim Inc (ci 0))) (Res (IntC 2))" 
proof -
  have 1: "Prim Inc (Prim Inc (ci 0)) \<longmapsto> Prim Inc (ci 1)" by auto
  have 2: "Prim Inc (ci 1) \<longmapsto> ci 2" by auto
  from 1 2 have 3: "Prim Inc (Prim Inc (ci 0)) \<longmapsto>* ci 2" by blast
  have 4: "exp2res (ci 2) = Res (IntC 2)" by simp
  from 3 4 show ?thesis unfolding eval_red_def sorry
qed

lemma prim_cong: assumes re: "e \<longmapsto>* e'"
shows "Prim p e \<longmapsto>* Prim p e'"
using re by (induction rule: reduces.induct, blast, blast) 

lemma if_cong: assumes re: "e1 \<longmapsto>* e1'"
shows "IfE e1 e2 e3 \<longmapsto>* IfE e1' e2 e3"
using re by (induction rule: reduces.induct, blast, blast)

lemma reduces_trans:
fixes e1::exp and e2::exp and e3::exp
assumes r12: "e1 \<longmapsto>* e2" and r23: "e2 \<longmapsto>* e3" shows "e1 \<longmapsto>* e3"
using r12 r23
proof (induction arbitrary: e3 rule: reduces.induct)
  case (red_nil e e3) thus "e \<longmapsto>* e3" by blast
next
  case (red_cons e1 e2 e3 e3')
  hence "e1 \<longmapsto> e2" and "e2 \<longmapsto>* e3'" by auto
  thus "e1 \<longmapsto>* e3'" by blast
qed

lemma eval_reduces:
  fixes e::exp assumes ev: "eval e = Res c" 
  shows "e \<longmapsto>* Const c"
  using ev
proof (induction e arbitrary: c)
  case (Const c')
  from Const have c: "c' = c" by simp
  have 1: "Const c \<longmapsto>* Const c" by (rule red_nil)
  from c 1 show "Const c' \<longmapsto>* Const c" by simp
next
  case (Prim p e)
  from Prim have 1: "eval (Prim p e) = Res c" by simp
  from 1 obtain c' where ec: "eval e = Res c'"
      and ep: "eval_prim p c' = Res c"
    apply simp apply (case_tac "eval e") apply auto done
  from Prim have IH: "eval e = Res c' \<Longrightarrow> e \<longmapsto>* Const c'" by simp
  from ec IH have er: "e \<longmapsto>* Const c'" by simp
  from er have 1: "Prim p e \<longmapsto>* Prim p (Const c')" by (rule prim_cong)
  from ep have "Prim p (Const c') \<longmapsto> Const c" by blast
  hence 2: "Prim p (Const c') \<longmapsto>* Const c" by blast
  from 1 2 show "Prim p e \<longmapsto>* Const c" by (rule reduces_trans)
  oops



