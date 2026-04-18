# Strong Normalization of the Flat Admissible Fragment

This note accompanies the Coq development in `formal/coq/FlatAdmissibleSN.v`.
It supplies the paper-grade proof the mechanization discharges and records
the scope boundary with the full admissible fragment of Section 5 of the
Lex paper.

## Statement

Let $\FAdm$ denote the grammar

$$
t \ ::=\ x \ \mid\ c \ \mid\ a\;t \ \mid\ \letk{t_1}{t_2} \ \mid\ \mtch{t}{\overline{(c_i,\;e_i)}} \ \mid\ \defk{t}{\overline{(g_j,\;b_j)}}
$$

over an infinite set of variables $x$, a set of constructor tags $c$, and a
set of accessor names $a$. Let the reduction relation $\to$ be defined by
the rules

$$
\begin{array}{rcl}
(\zeta)\quad & \letk{c}{e} & \to\ e \\
(\mu_v)\quad & \mtch{c}{\overline{(c_i,\;e_i)}} & \to\ e_k \quad\text{when}\ c=c_k \\
(\delta_0)\quad & \defk{c}{\epsilon} & \to\ c \\
(\xi_{\mathsf{let}})\quad & \letk{t_1}{t_2} & \to\ \letk{t_1'}{t_2} \quad\text{if}\ t_1\to t_1' \\
(\xi_{\mathsf{mat}})\quad & \mtch{t}{\mathbf{bs}} & \to\ \mtch{t'}{\mathbf{bs}} \quad\text{if}\ t\to t' \\
(\xi_{\mathsf{def}})\quad & \defk{t}{\mathbf{es}} & \to\ \defk{t'}{\mathbf{es}} \quad\text{if}\ t\to t'. \\
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
\end{array}
$$

Every subterm of $t$ contributes a strictly positive amount; in particular
$|t| \geq 1$ for every term.

## Case analysis

**Base cases.**

1. *$(\zeta)$: $\letk{c}{e} \to e$.*
   $|\letk{c}{e}| = 1 + 1 + |e|$ and $|e| \leq |e|$, hence
   $|e| < |\letk{c}{e}|$.

2. *$(\mu_v)$: $\mtch{c}{\mathbf{bs}} \to e_k$ with $(c,e_k) \in \mathbf{bs}$.*
   The branch lookup returns a body that is a syntactic subterm of one of
   the arms, so $|e_k| \leq \sum_i |e_i|$, and
   $|\mtch{c}{\mathbf{bs}}| = 1 + 1 + \sum_i |e_i|$. Thus
   $|e_k| \leq \sum_i |e_i| < 1 + 1 + \sum_i |e_i|$.

3. *$(\delta_0)$: $\defk{c}{\epsilon} \to c$.*
   $|\defk{c}{\epsilon}| = 1 + 1 + 0 = 2$ and $|c| = 1$, hence
   $|c| < |\defk{c}{\epsilon}|$.

**Inductive cases.**

4. *$(\xi_{\mathsf{let}})$: $\letk{t_1}{t_2} \to \letk{t_1'}{t_2}$ with $t_1 \to t_1'$.*
   By the induction hypothesis $|t_1'| < |t_1|$, so
   $|\letk{t_1'}{t_2}| = 1 + |t_1'| + |t_2| < 1 + |t_1| + |t_2| = |\letk{t_1}{t_2}|$.

5. *$(\xi_{\mathsf{mat}})$: $\mtch{t}{\mathbf{bs}} \to \mtch{t'}{\mathbf{bs}}$ with $t \to t'$.*
   Analogous, with the branch summation unchanged.

6. *$(\xi_{\mathsf{def}})$: $\defk{t}{\mathbf{es}} \to \defk{t'}{\mathbf{es}}$ with $t \to t'$.*
   Analogous, with the exception summation unchanged.

Combining the six cases, every single-step reduction strictly decreases the
size measure.

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
value substitution (ζ), match on finite constructor tags (μ), and
defeasible rules whose base reduces to a value (δ). Pi types, lambdas,
general β-reduction, and recursion are excluded — paper §5 excludes these
from admissibility and the exclusion is the premise of the SN statement
above, not a gap in the proof.

Two extensions are routine but not included in the narrow mechanized
statement:

1. *Lambdas with β under call-by-value on prelude values.*
   Every admissible argument reduces to a constant before substitution, so
   $\beta$ on $(\lambda x.\,e)\;c$ produces $e[c/x]$. Because variables are
   only replaced by constants and every $x$ in $e$ is replaced by a term of
   size $1$, the substituted body has size $\leq |e|$, and
   $|(\lambda x.\,e)\;c| = 2 + |e| + 1 > |e[c/x]|$. Mechanizing this
   requires encoding capture-avoiding substitution — a standard but
   laborious development, scoped to a follow-up pass.

2. *Defeasible rules with non-empty exception lists.*
   Each exception body is itself an FAdm term; reduction inside an
   exception is handled by a further congruence rule analogous to
   $(\xi_{\mathsf{def}})$, and the size-decrease argument carries through
   unchanged. The priority-ordered selection of a satisfied exception is a
   reduction on the *body* rather than the exception list and does not
   affect the size measure.

Both extensions preserve the measure structure used in the narrow theorem.
The remaining open metatheory — preservation and progress, confluence,
and SN for the full fragment with recursion admitted under structural
guards — is the research agenda named in paper §11.

## Verification

`coqc formal/coq/FlatAdmissibleSN.v` exits with status 0 on Coq 8.18+.
`Print Assumptions flat_admissible_sn.` reports `Closed under the global
context`: the proof uses no axioms beyond the stdlib's standard
inductive/well-foundedness constructions.
