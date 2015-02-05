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
    <td><code>assume p: "P" and q: "Q"</code></td>
    <td><code>assume 1: "P ∧ Q" </code><br>
        <code>  and 2: "P ∨ Q" </code><br>
        <code>  and 3: "P ⟶ Q" </code><br>
        <code>  and 4: "P" </code><br>
        <code>  and 5: "∀n. ?Tn" </code><br>
        <code>  and 6: "∃n. ?Tn"</code></td>
  </tr>
  <tr>
    <td>and</td>
    <td><code>from p q have "P ∧ Q" .. </code></code><br>
        <code>  have "P ∧ Q" </code><br>
        <code>proof </code><br>
        <code>  from p show "P" . </code><br>
        <code>next </code><br>
        <code>  from q show "Q" . </code><br>
        <code>qed</code></td>
    <td><code>from 1 have "P" .. </code><br>
        <code>from 1 have "Q" ..</code></td>
  </tr>
  <tr>
    <td>or</td>
    <td><code>from p have "P ∨ Q" .. </code><br>
        <code>from q have "P ∨ Q" .. </code><br>

        <code>have "P ∨ Q" </code><br>
        <code>proof (rule disjI1) </code><br>
        <code>  from p show "P" . </code><br>
        <code>qed </code><br>

        <code>have "P ∨ Q" </code><br>
        <code>proof (rule disjI2) </code><br>
        <code>  from q show "Q" . </code><br>
        <code>qed</td>
    <td><code>from 2 have "?R" </code><br>
        <code>proof </code><br>
        <code>  assume p: "P" </code><br>
        <code>  from p show "?R" .. </code><br>
        <code>next </code><br>
        <code>  assume q: "Q" </code><br>
        <code>  from q show "?R" .. </code><br>
        <code>qed</td>
  </tr>
  <tr>
    <td>implication</td>
    <td><code>have "P ⟶ Q" </code><br>
        <code>proof </code><br>
        <code>  assume "P" </code><br>
        <code>  from q show "Q" . </code><br>
        <code>qed </code>
</td>
    <td><code>from 3 4 have "Q" ..<code></td>
  </tr>
  <tr>
    <td>for all</td>
    <td><code>have "∀n. ?S n" </code><br>
        <code>proof </code><br>
        <code>  fix n </code><br>
        <code>  show "?S n" .. </code><br>
        <code>qed</td>
    <td><code>from 5 have "?T 42" ..</code></td>
  </tr>
  <tr>
    <td>exists</td>
    <td><code>have "?S 42" .. </code><br>
        <code>hence "∃n. ?S n" ..</code></td>
    <td><code>from 6 obtain n where "?T n" ..</code></td>
  </tr>
</table>
