# Cheat Sheet
Notes taken from https://dl.dropboxusercontent.com/u/10275252/IntroPLTheory.pdf


<table>
  <tr>
    <th colspan="2">Prove-it Table for Propositional Logic</th>
  </tr>
  <tr>
    <td>¬ P</td>
    <td>assume P and prove False</td>
  </tr>
  <tr>
    <td>P ∧ Q</td>
    <td>prove P and also prove Q</td>
  </tr>
  <tr>
    <td>P ∨ Q</td>
    <td>prove one of P or Q</td>
  </tr>
  <tr>
    <td>P ⟶ Q</td>
    <td>assume P and then prove Q</td>
  </tr>
</table>

<table>
  <tr>
    <th colspan="2">Use-it Table for Propositional Logic</th>
  </tr>
  <tr>
    <td>from (¬ P) and P </td>
    <td>have Q</td>
  </tr>
  <tr>
    <td>from P ∧ Q </td>
    <td>have P</td>
  </tr>
  <tr>
    <td>from P ∧ Q</td>
    <td>have Q</td>
  </tr>
  <tr>
    <td>from P ∨ Q, P ⟶ R, and Q ⟶ R</td>
    <td>have R</td>
  </tr>
  <tr>
    <td>from P ⟶ Q and P</td>
    <td>have Q</td>
  </tr>
</table>

<table>
  <tr>
    <th colspan="2">Prove-it for First-order Logic</th>
  </tr>
  <tr>
    <td>∀x. (P x)</td>
    <td>fix x and prove (P x)</td>
  </tr>
  <tr>
    <td>∃x. (P x)</td>
    <td>prove (P y) for a particular y</td>
  </tr>
</table>

<table>
  <tr>
    <th colspan="2">Use-it for First-order Logic</th>
  </tr>
  <tr>
    <td>∀x. (P x)</td>
    <td>have (P w) for any choice of w</td>
  </tr>
  <tr>
    <td>∃x. (P x)</td>
    <td>have (P z) for a freshly obtained variable z</td>
  </tr>
</table>

<table>
  <tr>
    <th colspan="3">Templates for applying the introduction and elimination rules (HOL)</th>
  </tr>
  <tr>
    <th></th>
    <th>Introduction</th>
    <th>Elimination</th>
  </tr>
  <tr>
    <td>  </td>
    <td>assume p: "P" and q: "Q"</td>
    <td>assume 1: ”P ∧ Q” and 2: ”P ∨ Q” and 3: ”P −→ Q” and 4: ”P” and5:”∀ n.?Tn” and6:”∃ n.?Tn”</td>
  </tr>
  <tr>
    <td>and</td>
    <td>from p q have ”P ∧ Q” ..
have ”P ∧ Q” proof
from p show ”P” . next
from q show ”Q” . qed</td>
    <td>from 1 have ”P” .. from 1 have ”Q” ..</td>
  </tr>
  <tr>
    <td>or</td>
    <td>from p have ”P ∨ Q” .. from q have ”P ∨ Q” ..
have ”P ∨ Q” proof (rule disjI1)
from p show ”P” . qed
have ”P ∨ Q” proof (rule disjI2)
from q show ”Q” . qed</td>
    <td>from 2 have ”?R” proof
assume p: ”P”
from p show ”?R” .. next
assume q: ”Q”
from q show ”?R” .. qed</td>
  </tr>
  <tr>
    <td>implication</td>
    <td>have ”P −→ Q” proof
assume ”P”
from q show ”Q” . qed
</td>
    <td>from 3 4 have ”Q” ..</td>
  </tr>
  <tr>
    <td>for all</td>
    <td>have ”∀ n. ?S n” proof
fix n
show ”?S n” .. qed</td>
    <td>from 5 have ”?T 42” ..</td>
  </tr>
  <tr>
    <td>exists </td>
    <td>have ”?S 42” .. hence ”∃ n. ?S n” ..</td>
    <td>from 6 obtain n where ”?T n” ..</td>
  </tr>
</table>
