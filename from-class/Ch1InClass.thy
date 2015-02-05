theory Ch1InClass
imports Main 
begin

primrec repeat :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "repeat f 0 x = x" |
  "repeat f (Suc n) x = repeat f n (f x)"

abbreviation rep :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  ("_^_ _" [90,90,90] 89) where
    "f^n x \<equiv> repeat f n x"

lemma repeat_add[rule_format]:
  "\<forall> x. f^(a + b) x = f^b (f^a x)" (is "?P a")
proof (induction a)
  case 0
  show "?P 0"
  proof
    fix x
    show "f^(0 + b) x = f^b (f^0 x)" by simp
  qed
next
  case (Suc a')
  from Suc have IH: "\<forall> y. f^(a' + b) y = f^b (f^a' y)" .
  show "?P (Suc a')"
  proof
    fix x
    have "f^((Suc a') + b) x = f^(Suc (a' + b)) x" by simp
    also have "... = f^(a' + b) (f x)" by simp
    also from IH have "... = f^b (f^a' (f x))" ..
    also have "... = f^b (f^Suc a' x)" by simp
    finally show "f^(Suc a' + b) x = f^b (f^Suc a' x)" .
  qed
qed

theorem repeat_cycle: "f^n x = x \<longrightarrow> f^(m * n) x = x" (is "?P m")
proof (induction m)
  case 0
  show "?P 0"
  proof
    assume fnx: "f^n x = x"
    show "f^(0 * n) x = x" by simp
  qed
next
  case (Suc m') -- "case where m = Suc m'"
  show "?P (Suc m')"
  proof
    assume fnx: "f^n x = x"
    from Suc fnx have IH: "f^(m' * n) x = x" ..
    have "f^((Suc m') * n) x = f^(n + (m' * n)) x" by simp
    also have "... = f^(m' * n) (f^n x)" by (rule repeat_add)
    also from fnx have "... = f^(m' * n) x" by simp
    also from IH have "... = x" .
    finally show "f^(Suc m' * n) x = x" .
  qed
qed

  
primrec multirember :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "multirember a [] = []" |
  "multirember a (b#ls) = (if a = b then multirember a ls
                           else b#(multirember a ls))"

value "multirember (1::nat) [1,2]"

lemma multirember_not_member: 
  "a \<notin> set (multirember a ls)" (is "?P ls")
proof (induction ls)
  case Nil
  show "?P []" by simp
next
  case (Cons x xs)
  show "?P (Cons x xs)"
  proof (cases "a = x")
    assume ax: "a = x"
    from ax 
    have 1: "multirember a (x#xs) = multirember a xs" by simp
    from Cons have IH: "a \<notin> set (multirember a xs)" .
    from 1 IH show "a \<notin> set (multirember a (x # xs))" by simp
  next
    assume ax: "a \<noteq> x"
    from ax
    have 2: "multirember a (x#xs) = x#(multirember a xs)" by simp
    from Cons ax have 3: "a \<notin> set (x#multirember a xs)" by simp
    from 2 3 show "a \<notin> set (multirember a (x # xs))" by simp
  qed
qed

datatype 'a tree = Leaf | Node "'a tree" 'a "'a tree"

primrec height :: "'a tree \<Rightarrow> nat" where
  "height Leaf = 0" |
  "height (Node L x R) = 1 + max (height L) (height R)"

primrec leaves :: "'a tree \<Rightarrow> nat" where
  "leaves Leaf = 1" |
  "leaves (Node L x R) = leaves L + leaves R"

(* Finished here on 1/15/2014 *) 

theorem height_less_leaves: "height t + 1 \<le> leaves t" 
proof (induction t)
  case Leaf
  show "height Leaf + 1 \<le> leaves Leaf" sorry
next
  case (Node T1 a T2)
  show "height (Node T1 a T2) + 1 \<le> leaves (Node T1 a T2)" sorry
qed

primrec keys :: "nat tree \<Rightarrow> nat set" where
  "keys Leaf = {}" |
  "keys (Node L x R) = keys L \<union> {x} \<union> keys R"

inductive_set BST :: "(nat tree) set" where
  bst_leaf[intro!]: "Leaf \<in> BST" |
  bst_node[intro!]: "\<lbrakk> \<forall> y \<in> keys L. y \<le> x; \<forall> z \<in> keys R. x \<le> z; 
                        L \<in> BST; R \<in> BST \<rbrakk>
                        \<Longrightarrow> (Node L x R) \<in> BST"

thm BST.induct

inductive_cases inv_bst_node[elim!]: "(Node L y R) \<in> BST"

thm inv_bst_node

(* hi there, this doesn't show up in latex *)
text{*
  this shows up in the latex output
*}

primrec bst_insert :: "nat \<Rightarrow> nat tree \<Rightarrow> nat tree" where
  "bst_insert x Leaf = Node Leaf x Leaf" |
  "bst_insert x (Node L y R) = 
     (if x < y then Node (bst_insert x L) y R
      else if y < x then Node L y (bst_insert x R)
      else Node L y R)"

thm tree.induct
thm BST.induct

theorem insert_bst: 
  assumes tbst: "T \<in> BST" shows "bst_insert x T \<in> BST" 
using tbst
proof (induction rule: BST.induct)
  case bst_leaf
  show "bst_insert x Leaf \<in> BST" by auto
next
  case (bst_node L x' R)
  from bst_node
  oops

end
