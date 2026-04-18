# Strong Normalization of the Flat Admissible Fragment

This note accompanies the Coq development in `formal/coq/FlatAdmissibleSN.v`.
It supplies the paper-grade proof the mechanization discharges and records
the scope boundary with the full admissible fragment of Section 5 of the
Lex paper.

## Statement

Let $\FAdm$ denote the grammar

$$
t \ ::=\ x \ \mid\ c \ \mid\ a\;t \ \mid\ \letk{t_1}{t_2} \ \mid\ \mtch{t}{\overline{(c_i,\;e_i)}} \ \mid\ \defk{t}{\overline{(g_j,\;b_j)}} \ \mid\ \lambda\,t \ \mid\ t_1\;t_2
$$

over an infinite set of de Bruijn indices $x$, a set of constructor tags
$c$, and a set of accessor names $a$. A term $v$ is a *value* when
$v = c$ (constant) or $v = \lambda\,t$ (lambda). A lambda body $t$ is
*affine* at its bound index $0$ when $\mathrm{occ}(t,\,0) \leq 1$, i.e. the
bound index occurs at most once in $t$. Let the reduction relation $\to$
be defined by the rules

$$
\begin{array}{rcl}
(\zeta)\quad & \letk{c}{e} & \to\ e \\
(\mu_v)\quad & \mtch{c}{\overline{(c_i,\;e_i)}} & \to\ e_k \quad\text{when}\ c=c_k \\
(\delta_0)\quad & \defk{c}{\epsilon} & \to\ c \\
(\delta_k)\quad & \defk{c}{\mathbf{es}} & \to\ b_j \quad\text{when}\ (g_j,\,b_j) \in \mathbf{es} \\
(\beta)\quad & (\lambda\,t)\;v & \to\ t[v/0] \quad\text{when}\ v\ \text{is a value and}\ \mathrm{occ}(t,\,0) \leq 1 \\
(\xi_{\mathsf{let}})\quad & \letk{t_1}{t_2} & \to\ \letk{t_1'}{t_2} \quad\text{if}\ t_1\to t_1' \\
(\xi_{\mathsf{mat}})\quad & \mtch{t}{\mathbf{bs}} & \to\ \mtch{t'}{\mathbf{bs}} \quad\text{if}\ t\to t' \\
(\xi_{\mathsf{def}})\quad & \defk{t}{\mathbf{es}} & \to\ \defk{t'}{\mathbf{es}} \quad\text{if}\ t\to t' \\
(\xi_{\mathsf{app\text{-}l}})\quad & f\;a & \to\ f'\;a \quad\text{if}\ f\to f' \\
(\xi_{\mathsf{app\text{-}r}})\quad & v\;a & \to\ v\;a' \quad\text{if}\ a\to a'\ \text{and}\ v\ \text{a value}. \\
\end{array}
$$

**Theorem (Strong normalization of FAdm).**
For every $t \in \FAdm$, every reduction sequence from $t$ under $\to$
terminates.

## Measure

Define the size $|t|$ by

$$
\begin{array}{rcl}
|x|\ =\ |c| & = & 1 \\
|a\;t| & = & 1 + |t| \\
|\letk{t_1}{t_2}| & = & 1 + |t_1| + |t_2| \\
|\mtch{t}{\overline{(c_i,\;e_i)}}| & = & 1 + |t| + \sum_i |e_i| \\
|\defk{t}{\overline{(g_j,\;b_j)}}| & = & 1 + |t| + \sum_j (|g_j| + |b_j|) \\
|\lambda\,t| & = & 1 + |t| \\
|f\;a| & = & 1 + |f| + |a| \\
\end{array}
$$

Every subterm of $t$ contributes a strictly positive amount; in particular
$|t| \geq 1$ for every term.

## Occurrence count and substitution size lemma

Define $\mathrm{occ}(t,\,k)$, the number of free occurrences of the de
Bruijn index $k$ in $t$, and capture-naive substitution $t[u/k]$
(substitution is not capture-avoiding in the general sense; the β rule
fires only when $u$ is a closed value, so capture cannot arise). The
mechanization proves the identity

$$
|t[u/k]| + \mathrm{occ}(t,\,k) \;=\; |t| + \mathrm{occ}(t,\,k)\cdot|u|.
$$

As a corollary, under affineness $\mathrm{occ}(\mathrm{body},\,0) \leq 1$,

$$
|\mathrm{body}[v/0]| \;\leq\; |\mathrm{body}| + |v| - 1.
$$

## Case analysis

**Base cases.**

1. *$(\zeta)$: $\letk{c}{e} \to e$.*
   $|\letk{c}{e}| = 1 + 1 + |e|$, hence $|e| < |\letk{c}{e}|$.

2. *$(\mu_v)$: $\mtch{c}{\mathbf{bs}} \to e_k$ with $(c,e_k) \in \mathbf{bs}$.*
   The branch lookup returns a body that is a syntactic subterm of one of
   the arms, so $|e_k| \leq \sum_i |e_i|$, and
   $|\mtch{c}{\mathbf{bs}}| = 1 + 1 + \sum_i |e_i|$. Thus
   $|e_k| \leq \sum_i |e_i| < 1 + 1 + \sum_i |e_i|$.

3. *$(\delta_0)$: $\defk{c}{\epsilon} \to c$.*
   $|\defk{c}{\epsilon}| = 2$ and $|c| = 1$.

4. *$(\delta_k)$: $\defk{c}{\mathbf{es}} \to b_j$ with $(g_j, b_j) \in \mathbf{es}$.*
   $|b_j| \leq \sum_j (|g_j| + |b_j|)$ and
   $|\defk{c}{\mathbf{es}}| = 1 + 1 + \sum_j (|g_j| + |b_j|)$, so
   $|b_j| < |\defk{c}{\mathbf{es}}|$.

5. *$(\beta)$: $(\lambda\,t)\;v \to t[v/0]$ with $v$ a value and
   $\mathrm{occ}(t,\,0) \leq 1$.*
   $|(\lambda\,t)\;v| = 1 + (1 + |t|) + |v| = 2 + |t| + |v|$. The
   affine-substitution corollary gives $|t[v/0]| \leq |t| + |v| - 1$, so
   $|t[v/0]| < |(\lambda\,t)\;v|$.

**Inductive cases.**

6. *$(\xi_{\mathsf{let}})$: $\letk{t_1}{t_2} \to \letk{t_1'}{t_2}$ with $t_1 \to t_1'$.*
   By the induction hypothesis $|t_1'| < |t_1|$.

7. *$(\xi_{\mathsf{mat}})$: $\mtch{t}{\mathbf{bs}} \to \mtch{t'}{\mathbf{bs}}$ with $t \to t'$.*
   Analogous, with the branch summation unchanged.

8. *$(\xi_{\mathsf{def}})$: $\defk{t}{\mathbf{es}} \to \defk{t'}{\mathbf{es}}$ with $t \to t'$.*
   Analogous, with the exception summation unchanged.

9. *$(\xi_{\mathsf{app\text{-}l}})$: $f\;a \to f'\;a$ with $f \to f'$.*
   Analogous, with $|a|$ unchanged.

10. *$(\xi_{\mathsf{app\text{-}r}})$: $v\;a \to v\;a'$ with $a \to a'$.*
    Analogous, with $|v|$ unchanged.

Combining the ten cases, every single-step reduction strictly decreases
the size measure.

## Well-foundedness and conclusion

The natural-number strict ordering $<$ is well-founded. Let $R$ be the
reverse of $\to$ (that is, $R\;t'\;t$ iff $t \to t'$). The measure map
$|\cdot|:\FAdm \to \N$ satisfies
$t \to t' \implies |t'| < |t|$, hence the image of $R$ under $|\cdot|$ is
a subset of the well-founded relation $<$. A standard lifting lemma
(Nielsen and Plotkin's measure-decreasing well-foundedness, or König's
lemma applied to the finitely branching reduction graph bounded above by
$|t|$) yields well-foundedness of $R$. Strong normalization follows.

## Corollary (bounded reduction chain length)

Because every step strictly decreases size and size is a non-negative
integer, any reduction chain $t_0 \to t_1 \to \cdots \to t_k$ satisfies
$k \leq |t_0| - 1$. The evaluator's fuel counter in
`crates/lex-core/src/evaluate.rs` therefore serves as a correct
operational bound for all FAdm-shaped rules.

## Scope and boundary with the full admissible fragment

The FAdm grammar captures the evaluator-level core of the admissible
fragment described in paper §5 and implemented in
`crates/lex-core/src/evaluate.rs`: lookups (`Access`), let-bindings with
value substitution (ζ), match on finite constructor tags (μ), defeasible
rules on a value base with either empty or non-empty exception lists (δ₀
and δ_k), and affine lambdas under call-by-value β. Pi types, modals,
recursion, content-addressed references, and typed discretion holes are
excluded — paper §5 excludes these from admissibility and the exclusion
is the premise of the SN statement above, not a gap in the proof.

**Affineness and its role.** The β rule fires only when the lambda body
satisfies $\mathrm{occ}(\mathrm{body},\,0) \leq 1$. This is a genuine
restriction: a non-affine body such as $\lambda\,x.\,x\;x$ can duplicate
its argument and invalidates the size-measure argument used here. The
admissible-fragment typing rules in the Lex paper do not constrain a
priori which lambda bodies are affine; the affineness restriction is
therefore a sub-fragment of the paper's full admissible grammar, and it
captures the compliance-code idiom in which a lambda argument is used
once. Dropping affineness requires a reducibility-candidates argument
standard for simply-typed λ-calculus (Girard–Tait) and is scoped to a
follow-up mechanization.

**What remains excluded:**

- *Non-affine lambdas.* Requires reducibility candidates; outside this
  file.
- *Pi types, modals, recursion, content-addressed references, typed
  discretion holes.* Explicitly excluded from admissibility in paper §5;
  their exclusion is a premise of SN, not a gap.

The remaining open metatheory — preservation and progress, confluence,
and SN for the full fragment with recursion admitted under structural
guards — is the research agenda named in paper §11.

## Verification

`coqc formal/coq/FlatAdmissibleSN.v` exits with status 0 on Coq 8.18+ /
Rocq 9.1+. `Print Assumptions flat_admissible_sn_ext.` reports `Closed
under the global context`: the proof uses no axioms beyond the stdlib's
standard inductive/well-foundedness constructions. The same holds for
`flat_admissible_sn`, `step_decreases_size`, `subst_size`, and
`subst_size_affine`.
