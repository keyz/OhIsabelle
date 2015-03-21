# Cheat Sheet
Notes taken from https://dl.dropboxusercontent.com/u/10275252/IntroPLTheory.pdf


----


<table>
  <tr>
    <th colspan="2">Introduction Rules for Propositional Logic</th>
  </tr>
  <tr>
    <td><code>¬ P</code></td>
    <td>assume <code>P</code> and prove <code>False</code></td>
  </tr>
  <tr>
    <td><code>P ∧ Q</code></td>
    <td>prove <code>P</code> and also prove <code>Q</code></td>
  </tr>
  <tr>
    <td><code>P ∨ Q</code></td>
    <td>prove one of <code>P</code> or <code>Q</code></td>
  </tr>
  <tr>
    <td><code>P ⟶ Q</code></td>
    <td>assume <code>P</code> and then prove <code>Q</code></td>
  </tr>
</table>

<table>
  <tr>
    <th colspan="2">Elimination Rules for Propositional Logic</th>
  </tr>
  <tr>
    <td>from <code>(¬ P)</code> and <code>P</code></td>
    <td>have <code>Q</code> (or whatever you want)</td>
  </tr>
  <tr>
    <td>from <code>P ∧ Q</code></td>
    <td>have <code>P</code></td>
  </tr>
  <tr>
    <td>from <code>P ∧ Q</code></td>
    <td>have <code>Q</code></td>
  </tr>
  <tr>
    <td>from <code>P ∨ Q</code>, <code>P ⟶ R</code>, and <code>Q ⟶ R</code></td>
    <td>have <code>R</code></td>
  </tr>
  <tr>
    <td>from <code>P ⟶ Q</code> and <code>P</code></td>
    <td>have <code>Q</code></td>
  </tr>
</table>

<table>
  <tr>
    <th colspan="2">Introduction Rules for First-order Logic</th>
  </tr>
  <tr>
    <td><code>∀x. (P x)</code></td>
    <td>fix <code>x</code> and prove <code>(P x)</code></td>
  </tr>
  <tr>
    <td><code>∃x. (P x)</code></td>
    <td>prove <code>(P y)</code> for a particular <code>y</code></td>
  </tr>
</table>

<table>
  <tr>
    <th colspan="2">Elimination Rules for First-order Logic</th>
  </tr>
  <tr>
    <td><code>∀x. (P x)</code></td>
    <td>have <code>(P w)</code> for any choice of <code>w</code></td>
  </tr>
  <tr>
    <td><code>∃x. (P x)</code></td>
    <td>have <code>(P z)</code> for a freshly obtained variable <code>z</code></td>
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
    <td><code>assume p: "P" and q: "Q" and np: "¬ P"</code></td>
    <td><code>assume 1: "P ∧ Q"</code><br>
        <code>  and 2: "P ∨ Q"</code><br>
        <code>  and 3: "P ⟶ Q"</code><br>
        <code>  and 4: "P"</code><br>
        <code>  and 5: "∀n. ?T n"</code><br>
        <code>  and 6: "∃n. ?T n"</code>
        <code>  and 7: "False"</code></td>
  </tr>
  <tr>
    <td align="center">and</td>
    <td><code>from p q have "P ∧ Q" ..</code><br>
        <br>
        <code>have "P ∧ Q"</code><br>
        <code>proof</code><br>
        <code>  from p show "P" .</code><br>
        <code>next</code><br>
        <code>  from q show "Q" .</code><br>
        <code>qed</code></td>
    <td><code>from 1 have "P" ..</code><br>
        <code>from 1 have "Q" ..</code></td>
  </tr>
  <tr>
    <td align="center">or</td>
    <td><code>from p have "P ∨ Q" ..</code><br>
        <br>
        <code>from q have "P ∨ Q" ..</code><br>
        <br>
        <code>have "P ∨ Q"</code><br>
        <code>proof (rule disjI1)</code><br>
        <code>  from p show "P" .</code><br>
        <code>qed</code><br>
        <br>
        <code>have "P ∨ Q"</code><br>
        <code>proof (rule disjI2)</code><br>
        <code>  from q show "Q" .</code><br>
        <code>qed</td>
    <td><code>from 2 have "?R"</code><br>
        <code>proof</code><br>
        <code>  assume p: "P"</code><br>
        <code>  from p show "?R" ..</code><br>
        <code>next</code><br>
        <code>  assume q: "Q"</code><br>
        <code>  from q show "?R" ..</code><br>
        <code>qed</td>
  </tr>
  <tr>
    <td align="center">implication</td>
    <td><code>have "P ⟶ Q"</code><br>
        <code>proof</code><br>
        <code>  assume "P"</code><br>
        <code>  from q show "Q" .</code><br>
        <code>qed</code>
</td>
    <td><code>from 3 4 have "Q" ..</code></td>
  </tr>
  <tr>
    <td align="center">False</td>
    <td><code>from np p have "False" ..</code></td>
    <td><code>from 7 have "?R" ..</code></td>
  </tr>
  <tr>
    <td align="center">for all</td>
    <td><code>have "∀n. ?S n"</code><br>
        <code>proof</code><br>
        <code>  fix n</code><br>
        <code>  show "?S n" ..</code><br>
        <code>qed</td>
    <td><code>from 5 have "?T 42" ..</code></td>
  </tr>
  <tr>
    <td align="center">exists</td>
    <td><code>have "?S 42" ..</code><br>
        <code>hence "∃n. ?S n" ..</code></td>
    <td><code>from 6 obtain n where "?T n" ..</code></td>
  </tr>
</table>
