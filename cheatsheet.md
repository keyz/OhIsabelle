# Cheat Sheet
Notes taken from https://dl.dropboxusercontent.com/u/10275252/IntroPLTheory.pdf

Prove-it Table for Propositional Logic
------------------------------------
| ¬ P   | assume P and prove False  |
| P ∧ Q  | prove P and also prove Q  |
| P ∨ Q  | prove one of P or Q    |
| P ⟶ Q | assume P and then prove Q |
------------------------------------


Use-it Table for Propositional Logic
-------------------------------------
| from (¬ P) and P            | have Q |
| from P ∧ Q                 | have P |
| from P ∧ Q                 | have Q |
| from P ∨ Q, P ⟶ R, and Q ⟶ R | have R |
| from P ⟶ Q and P          | have Q |
-------------------------------------


Prove-it for First-order Logic
------------------------------------------
| ∀x. (P x) | fix x and prove (P x)          |
| ∃x. (P x) | prove (P y) for a particular y |
------------------------------------------


Use-it for First-order Logic
--------------------------------------------------------
| ∀x. (P x) | have (P w) for any choice of w               |
| ∃x. (P x) | have (P z) for a freshly obtained variable z |
--------------------------------------------------------


Templates for applying the introduction and elimination rules of first-order logic in Isabelle
--------------------------------------------------------
|  | Introduction | elimination |
|  | assume p: "P" and q: "Q" | assume 1: "P ∧ Q" 
|  |  |                           and 2: "P ∨ Q" |
|  |  |                           and 3: "P ⟶ Q" |
|  |  |                           and 4: "P" |
|  |  |                           and5:"∀n. ?T n" |
|  |  |                           and6:"∃n. ?T n" |
--------------------------------------------------------
| and | | |
--------------------------------------------------------


(*-- Prove-it --*)
assume p: "P" and q: "Q"

(* and *)
from p q have "P ∧ Q" ..

have "P ∧ Q"
proof
  from p show "P" .
next
  from q show "Q" .
qed

(* or *)
from p have "P ∨ Q" ..
from q have "P ∨ Q" ..

have "P ∨ Q"
proof (rule disjI1)
  from p show "P" .
qed

have "P ∨ Q"
proof (rule disjI2)
  from p show "Q" .
qed

(* implication *)
have "P ⟶ Q"
proof
  assume "P"
  from q show "Q" .
qed

(* for all *)
have "∀ n. ?S n"
proof
  fix n
  show "?S n" ..
qed

(* exists *)
have "?S 42" ..
hence "∃n. ?S n" ..

(*-- Use-it --*)
assume 1: "P ∧ Q"
  and 2: "P ∨ Q"
  and 3: "P ⟶ Q"
  and 4: "P"
  and 5: "∀n. ?T n"
  and 6: "∃n. ?T n"
  
(* and *)
from 1 have "P" ..
from 1 have "Q" ..

(* or *)
from 2 have "?R"
proof
  assume p: "P"
  from p show "?R" ..
next
  assume q: "Q"
  from q show "?R" ..
qed

(* implication *)
from 3 4 have "Q" ..

(* for all *)
from 5 have "?T 42" ..

(* exists *)
from 6 obtain n where "?T n" ..

