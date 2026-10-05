/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.BilinearAlgorithm
import AlgebraicComplexity.MatrixMultiplication.Exponent

/-!
# Recursive block compilation: rank certificates as arithmetic circuits

This module proves the **forward direction of Proposition 2.7** of He and Williams's CS 6810
lecture notes (<https://www.cs.cornell.edu/courses/cs6810/2023fa/Matrix.pdf>) — the ladder row
"Proposition 2.7" of `DESIGN.md`.  A rank-`r` decomposition of the `q × q × q`
matrix-multiplication tensor is compiled *recursively* into genuine straight-line programs for
the `n × n` matrix product whose total arithmetic size is `O(n ^ (log r / log q))` with an
explicit constant, not merely into one program per size.  This is Strassen's recursion
(V. Strassen, *Gaussian elimination is not optimal*, Numer. Math. 13 (1969) 354--356, §1) carried
out inside the exact cost model of `MatrixMultiplication/RankComplexity.lean`, which by itself
proves only the one-step compilation of a bilinear algorithm.

## Program combinators

`RankComplexity.lean` lets a program bind one register at a time (`Straightline.letBind`).  Block
recursion must consume the *whole output family* of a subprogram, so this file first supplies the
missing structural combinators, each with its evaluation law and its exact `linearOps` and
`mulOps` accounting:

* `Straightline.bindFin` and `Straightline.bindFamily`: bind a finite family of circuits as fresh
  registers and continue over the extended input type `ν ⊕ ι`;
* `Straightline.seq`: run a program and make **all** of its outputs available as registers of a
  continuation.  This is the sharing that makes a recursive call cost its own size once, however
  many later gates read its outputs;
* `Straightline.seqRep`: run `t` copies of one program in sequence, the `i`-th copy reading its
  inputs through a renaming `e i`; cost `t * p.cost + cont.cost`;
* `Straightline.reindexOut`: select a subfamily of output coordinates — cost-monotone for an
  injective selection (`linearOps_reindexOut_le`) and cost-preserving for a bijective one
  (`linearOps_reindexOut_bijective`).

## The recursion

* `Straightline.ComputesMatrixProduct p`: the semantic specification, "`p` computes the square
  matrix product on the index type `M`", in the transposed output convention of
  `matrixProductMap` (output `z` is the entry in row `z.2` and column `z.1`).
* `baseProgram`: the single multiplication gate, computing the `1 × 1` product.
* `blockLeftForm`, `blockRightForm`, `blockForms`, `blockOutput`, `blockStep`: one level of the
  recursion.  Given a length-`r` bilinear algorithm `A` for the `q × q` product and a program `p`
  for the `M × M` product, `blockStep A p` forms the `2 * r` block linear forms entrywise
  (`r * |M|^2` registers per side, each a combination of `q^2` inputs), runs `r` renamed copies
  of `p` on them, and recombines the `r` block products into the output blocks (`q^2 * |M|^2`
  combinations of `r` registers each).
* `transport` and `blockEquiv`: relabelling a matrix-product program along a bijection of index
  sets, used to keep the side length literally `Fin (q ^ k)` at every level.
* `powProgram A k`: the `k`-fold iterate, a program for the `q^k × q^k` product.
* `padIndex`, `padRename`, `padMatrix`, `padProgram`: restriction of a program for the `N × N`
  product to the `n × n` product for `n ≤ N`, by binding one constant-zero register, renaming
  every out-of-range input entry to it, and reading only the in-range outputs.  No gate is added.

## Principal results

* `sum_blockAlgorithm`: the block-substitution identity.  A scalar algorithm for the `q × q`
  product applied to `q × q` arrays of blocks computes the block product.  No commutativity
  between blocks is used: the algorithm's coefficients are scalars, and the two linear forms are
  multiplied in the order left form times right form.
* `computesMatrixProduct_blockStep`, `computesMatrixProduct_powProgram`,
  `computesMatrixProduct_padProgram`: correctness at each stage.
* `mulOps_blockStep` (`= r * p.mulOps`) and `mulOps_powProgram` (`= r ^ k`): the level-`k` program
  contains **exactly** `r ^ k` multiplication gates, one per leaf of the `r`-ary recursion tree;
  `nonscalarMuls_powProgram_le` records the resulting nonscalar bound.
* `totalOps_blockStep_le`, `totalOps_powProgram_add_le`, `totalOps_powProgram_le`: the cost
  recurrence and its solution `totalOps ≤ (1 + 6 * r * q^2) * r ^ k`.
* `exists_straightline_matrixProduct_of_rankLE`: the headline in natural numbers.  From
  `RankLE r ⟨q,q,q⟩` with `1 < q` and `q^2 < r`, for every `n` there is a straight-line program
  computing the `n × n` matrix product with at most `r ^ ⌈log_q n⌉` multiplication gates and at
  most `(1 + 6 * r * q^2) * r ^ ⌈log_q n⌉` operations in total.
* `exists_straightline_matrixProduct_rpow_of_rankLE` and
  `exists_straightline_matrixProduct_rpow_le_of_rankLE`: the polynomial form
  `totalOps ≤ ((1 + 6 * r * q^2) * r) * n ^ (log r / log q)` for `1 ≤ n`, and its weakening to
  every exponent `τ ≥ log r / log q`.
* `omega_le_and_exists_straightline_of_rankLE`: the two readings of one certificate side by side
  — the tensor-level bound `ω ≤ log r / log q` of `Exponent.lean` and the circuit-level family of
  size `O(n ^ (log r / log q))`.
* `exists_straightline_matrixProduct_of_omega_lt`: the exponent-level form over a field.  For
  every real `τ > ω` there are a constant `C` and, for every `n ≥ 1`, a straight-line program
  computing the `n × n` product in at most `C * n ^ τ` operations.  This is the forward half of
  Proposition 2.7 itself: the rank-growth exponent is an arithmetic-complexity exponent.
* `exists_straightline_matrixProduct_cubic`: a tiny end-to-end regression client.  The defining
  eight-term decomposition of `⟨2,2,2⟩` compiles to programs of size at most
  `193 * 8 ^ ⌈log₂ n⌉` — the classical cubic algorithm, obtained from nothing but the definition
  of matrix multiplication.

## The cost recurrence and the hypothesis `q^2 < r`

One block step costs `t (k+1) ≤ r * t k + c * q^(2k)` with `c = 6 * r * q^2`: the `2 * r * q^(2k)`
block linear forms cost `2 * q^2 - 1` each and the `q^(2k+2)` output combinations cost `2 * r - 1`
each.  The proved invariant is the additive form

```text
t k + c * q^(2k) ≤ (1 + c) * r ^ k,
```

whose induction step needs exactly `c * q^(2k) * (1 + q^2) ≤ c * q^(2k) * r`, that is `q^2 < r`.
This is the geometric-series comparison that makes the recursion `O(r^k)` rather than
`O(q^(2k))`; for `r ≤ q^2` the block additions, not the multiplications, dominate, and the same
recurrence only yields `O(k * q^(2k))`.

The hypothesis is not restrictive.  Over a field, flattening already forces `q^2 ≤ r` for every
rank certificate (`squareMatrixRankSequence` bounds in `MatrixMultiplication/Exponent.lean`), and
the substitution method improves this to `q^2 + 1 ≤ r` for `2 ≤ q`
(`matrixMultiplication_rank_lower_substitution_Y` in `Examples/SmallMatrixLowerBounds.lean`), so
no certificate over a field is excluded.  Over a general commutative semiring a certificate with
`r ≤ q^2` can be weakened to `RankLE (q^2 + 1)` by `Tensor.RankLE.mono`, at the cost of replacing
the exponent `log r / log q` by `log (q^2 + 1) / log q`, which exceeds `2` — and hence `ω` over
any field — by an amount tending to `0` in `q`.

## Conventions

* Costs count gates exactly as in `RankComplexity.lean`: every `add`, `mul` and `smul` gate costs
  one operation, a `Circuit` is a formula, and genuine sharing is expressed by binding a register.
  All statements here are about `linearOps`, `mulOps` and their sum `totalOps`.
* The output of a matrix-product program is indexed in the transposed convention of
  `matrixProductMap`, which is the `Z`-leg convention of `matrixMultiplication`.
* Everything except the exponent-level statement is over a commutative semiring; the base
  algorithm is arbitrary bilinear-algorithm data, so this file mentions no named decomposition
  and no numerical bound.
* The combinators are noncomputable only through the choice of an enumeration of a finite index
  type (`Fintype.equivFin`), exactly as `compileBilinear` already is.

## Layer placement

This file is a leaf of the matrix-multiplication theory layer.  It imports
`MatrixMultiplication/BilinearAlgorithm.lean` (for the rank/algorithm correspondence and
`matrixProductMap`) and `MatrixMultiplication/Exponent.lean` (for `omega` and the ceiling-log
estimate `real_pow_clog_le_mul_rpow`).  It reaches into no tensor-layer proof internals and
imports no client.

## Deliberate non-goals

Per the named-proof-obligation policy of `DESIGN.md`:

* **The converse of Proposition 2.7 is explicitly out of scope.**  Extracting a bilinear algorithm
  — hence a rank bound, hence a lower bound on `ω` — from an arbitrary straight-line program
  computing the matrix product is not proved, not stated, and not represented by any definition
  in this file.  Nothing here asserts that the arithmetic-complexity exponent equals the
  rank-growth exponent; only the inequality carried by an explicit certificate is proved.
* The exponent-level statement `exists_straightline_matrixProduct_of_omega_lt` is proved over a
  **field**, where `2 ≤ ω` is available.  Over a general commutative semiring `ω` may in
  principle fall below `2` and the slot padding to `q^2 + 1` used in its proof is no longer
  harmless, so only the certificate-level statements are claimed there.
* The multiplication count `r ^ k` is proved **exactly** for `mulOps` (all multiplication gates)
  and only as an upper bound for `nonscalarMuls`.  Showing that each of the `r ^ k` gates is
  syntactically nonscalar would need an "every output circuit depends on a live input" invariant
  threaded through `seq`, `seqRep` and `reindexOut`; it is not needed for any upper bound, and
  the honest certificate is the exact gate count.
-/

namespace AlgebraicComplexity

universe u v

namespace Straightline

variable {K : Type u} {μ : Type v}

/-! ### Binding a finite family of circuits as fresh registers -/

/-- Bind the `n` circuits `out 0, …, out (n-1)` to fresh registers, in this order, and continue
with `cont`, whose inputs `Sum.inl i` are the new registers and whose inputs `Sum.inr a` are the
old ones. -/
def bindFin : (n : ℕ) → {ι : Type v} → (Fin n → Circuit K ι) →
    Straightline K μ (Fin n ⊕ ι) → Straightline K μ ι
  | 0, _, _, cont => cont.rename (Sum.elim (fun i => i.elim0) id)
  | n + 1, _, out, cont =>
      .letBind (out 0)
        (bindFin n (fun i => (out i.succ).map some)
          (cont.rename
            (Sum.elim (fun i => Fin.cases (Sum.inr none) (fun j => Sum.inl j) i)
              (fun a => Sum.inr (some a)))))

/-- Binding the empty family is a pure renaming. -/
@[simp] theorem bindFin_zero {ι : Type v} (out : Fin 0 → Circuit K ι)
    (cont : Straightline K μ (Fin 0 ⊕ ι)) :
    bindFin 0 out cont = cont.rename (Sum.elim (fun i => i.elim0) id) := rfl

/-- Unfolding one step of `bindFin`. -/
theorem bindFin_succ (n : ℕ) {ι : Type v} (out : Fin (n + 1) → Circuit K ι)
    (cont : Straightline K μ (Fin (n + 1) ⊕ ι)) :
    bindFin (n + 1) out cont =
      .letBind (out 0)
        (bindFin n (fun i => (out i.succ).map some)
          (cont.rename
            (Sum.elim (fun i => Fin.cases (Sum.inr none) (fun j => Sum.inl j) i)
              (fun a => Sum.inr (some a))))) := rfl

/-- Evaluating `bindFin n out cont` runs `cont` in the environment that reads the `i`-th new
register as the value of the circuit `out i` and the old registers unchanged. -/
theorem eval_bindFin [Add K] [Mul K] :
    ∀ (n : ℕ) {ι : Type v} (out : Fin n → Circuit K ι)
      (cont : Straightline K μ (Fin n ⊕ ι)) (x : ι → K) (m : μ),
      (bindFin n out cont).eval x m
        = cont.eval (Sum.elim (fun i => (out i).eval x) x) m
  | 0, ι, out, cont, x, m => by
      have h : (fun z => x (Sum.elim (fun i : Fin 0 => i.elim0) id z))
          = Sum.elim (fun i : Fin 0 => (out i).eval x) x := by
        funext z
        cases z with
        | inl i => exact i.elim0
        | inr a => rfl
      rw [bindFin_zero, eval_rename]
      simpa [Function.comp_def] using congrArg (fun e => cont.eval e m) h
  | n + 1, ι, out, cont, x, m => by
      have h : (fun z =>
            Sum.elim (fun i : Fin n => ((out i.succ).map some).eval
                (extendEnv ((out 0).eval x) x))
              (extendEnv ((out 0).eval x) x)
            (Sum.elim (fun i => Fin.cases (Sum.inr none) (fun j => Sum.inl j) i)
              (fun a => Sum.inr (some a)) z))
          = Sum.elim (fun i => (out i).eval x) x := by
        funext z
        cases z with
        | inl i =>
            induction i using Fin.cases with
            | zero => simp
            | succ j => simp [Function.comp_def]
        | inr a => simp
      rw [bindFin_succ, eval_letBind, eval_bindFin n, eval_rename]
      simpa [Function.comp_def] using congrArg (fun e => cont.eval e m) h

section Costs

variable [Fintype μ]

/-- `bindFin` pays for each bound circuit exactly once. -/
theorem linearOps_bindFin :
    ∀ (n : ℕ) {ι : Type v} (out : Fin n → Circuit K ι)
      (cont : Straightline K μ (Fin n ⊕ ι)),
      (bindFin n out cont).linearOps = (∑ i, (out i).linearOps) + cont.linearOps
  | 0, ι, out, cont => by simp
  | n + 1, ι, out, cont => by
      rw [bindFin_succ, linearOps_letBind, linearOps_bindFin n, linearOps_rename,
        Fin.sum_univ_succ]
      simp [Circuit.linearOps_map, Nat.add_assoc]

/-- `bindFin` pays for the multiplication gates of each bound circuit exactly once. -/
theorem mulOps_bindFin :
    ∀ (n : ℕ) {ι : Type v} (out : Fin n → Circuit K ι)
      (cont : Straightline K μ (Fin n ⊕ ι)),
      (bindFin n out cont).mulOps = (∑ i, (out i).mulOps) + cont.mulOps
  | 0, ι, out, cont => by simp
  | n + 1, ι, out, cont => by
      rw [bindFin_succ, mulOps_letBind, mulOps_bindFin n, mulOps_rename, Fin.sum_univ_succ]
      simp [Circuit.mulOps_map, Nat.add_assoc]

end Costs

/-! ### Binding an arbitrary finite family of circuits -/

/-- Bind one fresh register per element of a finite index type `ν`, holding the value of the
circuit `out n`, and continue with `cont`.  Noncomputable only through the choice of an
enumeration of `ν`. -/
noncomputable def bindFamily {ν ι : Type v} [Fintype ν] (out : ν → Circuit K ι)
    (cont : Straightline K μ (ν ⊕ ι)) : Straightline K μ ι :=
  bindFin (Fintype.card ν) (fun i => out ((Fintype.equivFin ν).symm i))
    (cont.rename (Sum.map (Fintype.equivFin ν) id))

/-- Evaluating `bindFamily out cont` runs `cont` with each new register `Sum.inl n` holding the
value of `out n`. -/
theorem eval_bindFamily [Add K] [Mul K] {ν ι : Type v} [Fintype ν] (out : ν → Circuit K ι)
    (cont : Straightline K μ (ν ⊕ ι)) (x : ι → K) (m : μ) :
    (bindFamily out cont).eval x m
      = cont.eval (Sum.elim (fun n => (out n).eval x) x) m := by
  have h : (fun z => Sum.elim (fun i => (out ((Fintype.equivFin ν).symm i)).eval x) x
        (Sum.map (Fintype.equivFin ν) id z))
      = Sum.elim (fun n => (out n).eval x) x := by
    funext z
    cases z <;> simp
  rw [bindFamily, eval_bindFin, eval_rename]
  simpa [Function.comp_def] using congrArg (fun e => cont.eval e m) h

section FamilyCosts

variable [Fintype μ]

/-- `bindFamily` pays for each bound circuit exactly once. -/
theorem linearOps_bindFamily {ν ι : Type v} [Fintype ν] (out : ν → Circuit K ι)
    (cont : Straightline K μ (ν ⊕ ι)) :
    (bindFamily out cont).linearOps = (∑ n, (out n).linearOps) + cont.linearOps := by
  rw [bindFamily, linearOps_bindFin, linearOps_rename]
  congr 1
  exact Equiv.sum_comp (Fintype.equivFin ν).symm fun n => (out n).linearOps

/-- `bindFamily` pays for the multiplication gates of each bound circuit exactly once. -/
theorem mulOps_bindFamily {ν ι : Type v} [Fintype ν] (out : ν → Circuit K ι)
    (cont : Straightline K μ (ν ⊕ ι)) :
    (bindFamily out cont).mulOps = (∑ n, (out n).mulOps) + cont.mulOps := by
  rw [bindFamily, mulOps_bindFin, mulOps_rename]
  congr 1
  exact Equiv.sum_comp (Fintype.equivFin ν).symm fun n => (out n).mulOps

end FamilyCosts

/-! ### Sequential composition of programs -/

/-- Run the program `p`, bind each of its output coordinates to a fresh register, and continue
with `cont`, whose input `Sum.inl n` is the `n`-th output of `p` and whose input `Sum.inr a` is
the old register `a`.  This is the sharing combinator that lets one program consume the results
of another without recomputing them. -/
noncomputable def seq {ν : Type v} [Fintype ν] :
    {ι : Type v} → Straightline K ν ι → Straightline K μ (ν ⊕ ι) → Straightline K μ ι
  | _, .ret out, cont => bindFamily out cont
  | _, .letBind c body, cont => .letBind c (seq body (cont.rename (Sum.map id some)))

/-- Composing a returning program is binding its output family. -/
@[simp] theorem seq_ret {ν ι : Type v} [Fintype ν] (out : ν → Circuit K ι)
    (cont : Straightline K μ (ν ⊕ ι)) :
    seq (ret out) cont = bindFamily out cont := rfl

/-- Composition passes through a `letBind` of the first program. -/
@[simp] theorem seq_letBind {ν ι : Type v} [Fintype ν] (c : Circuit K ι)
    (body : Straightline K ν (Option ι)) (cont : Straightline K μ (ν ⊕ ι)) :
    seq (letBind c body) cont = letBind c (seq body (cont.rename (Sum.map id some))) := rfl

/-- Evaluating `seq p cont` runs `cont` with the outputs of `p` available as fresh registers. -/
theorem eval_seq [Add K] [Mul K] {ν : Type v} [Fintype ν] :
    ∀ {ι : Type v} (p : Straightline K ν ι) (cont : Straightline K μ (ν ⊕ ι)) (x : ι → K)
      (m : μ), (seq p cont).eval x m = cont.eval (Sum.elim (p.eval x) x) m
  | _, .ret out, cont, x, m => by
      rw [seq_ret, eval_bindFamily]
      rfl
  | _, .letBind c body, cont, x, m => by
      have h : (fun z => Sum.elim (body.eval (extendEnv (c.eval x) x))
            (extendEnv (c.eval x) x) (Sum.map id some z))
          = Sum.elim ((letBind c body).eval x) x := by
        funext z
        cases z <;> simp
      rw [seq_letBind, eval_letBind, eval_seq body, eval_rename]
      simpa [Function.comp_def] using congrArg (fun e => cont.eval e m) h

section SeqCosts

variable [Fintype μ]

/-- Composition adds the linear-operation counts of the two programs. -/
theorem linearOps_seq {ν : Type v} [Fintype ν] :
    ∀ {ι : Type v} (p : Straightline K ν ι) (cont : Straightline K μ (ν ⊕ ι)),
      (seq p cont).linearOps = p.linearOps + cont.linearOps
  | _, .ret out, cont => by rw [seq_ret, linearOps_bindFamily, linearOps_ret]
  | _, .letBind c body, cont => by
      rw [seq_letBind, linearOps_letBind, linearOps_seq body, linearOps_rename,
        linearOps_letBind, Nat.add_assoc]

/-- Composition adds the multiplication-gate counts of the two programs. -/
theorem mulOps_seq {ν : Type v} [Fintype ν] :
    ∀ {ι : Type v} (p : Straightline K ν ι) (cont : Straightline K μ (ν ⊕ ι)),
      (seq p cont).mulOps = p.mulOps + cont.mulOps
  | _, .ret out, cont => by rw [seq_ret, mulOps_bindFamily, mulOps_ret]
  | _, .letBind c body, cont => by
      rw [seq_letBind, mulOps_letBind, mulOps_seq body, mulOps_rename, mulOps_letBind,
        Nat.add_assoc]

end SeqCosts

/-! ### Running many renamed copies of one program -/

/-- Run `t` copies of the same program `p`, the `i`-th copy reading its inputs through the
renaming `e i`, and continue with `cont`, whose input `Sum.inl (i, n)` is the `n`-th output of
the `i`-th copy.  The copies are laid out sequentially, so the total cost is `t` times the cost
of `p` plus the cost of `cont`. -/
noncomputable def seqRep {ν ι₀ : Type v} [Fintype ν] (p : Straightline K ν ι₀) :
    (t : ℕ) → {ι : Type v} → (Fin t → ι₀ → ι) → Straightline K μ ((Fin t × ν) ⊕ ι) →
      Straightline K μ ι
  | 0, _, _, cont => cont.rename (Sum.elim (fun z => z.1.elim0) id)
  | t + 1, _, e, cont =>
      seq (p.rename (e 0))
        (seqRep p t (fun i a => Sum.inr (e i.succ a))
          (cont.rename
            (Sum.elim
              (fun z => Fin.cases (Sum.inr (Sum.inl z.2)) (fun i => Sum.inl (i, z.2)) z.1)
              (fun a => Sum.inr (Sum.inr a)))))

/-- Running no copies is a pure renaming. -/
@[simp] theorem seqRep_zero {ν ι₀ ι : Type v} [Fintype ν] (p : Straightline K ν ι₀)
    (e : Fin 0 → ι₀ → ι) (cont : Straightline K μ ((Fin 0 × ν) ⊕ ι)) :
    seqRep p 0 e cont = cont.rename (Sum.elim (fun z => z.1.elim0) id) := rfl

/-- Unfolding one copy of `seqRep`. -/
theorem seqRep_succ {ν ι₀ ι : Type v} [Fintype ν] (p : Straightline K ν ι₀) (t : ℕ)
    (e : Fin (t + 1) → ι₀ → ι) (cont : Straightline K μ ((Fin (t + 1) × ν) ⊕ ι)) :
    seqRep p (t + 1) e cont =
      seq (p.rename (e 0))
        (seqRep p t (fun i a => Sum.inr (e i.succ a))
          (cont.rename
            (Sum.elim
              (fun z => Fin.cases (Sum.inr (Sum.inl z.2)) (fun i => Sum.inl (i, z.2)) z.1)
              (fun a => Sum.inr (Sum.inr a))))) := rfl

/-- Evaluating `seqRep p t e cont` runs `cont` with the register `Sum.inl (i, n)` holding the
`n`-th output of `p` evaluated at the inputs pulled back along `e i`. -/
theorem eval_seqRep [Add K] [Mul K] {ν ι₀ : Type v} [Fintype ν] (p : Straightline K ν ι₀) :
    ∀ (t : ℕ) {ι : Type v} (e : Fin t → ι₀ → ι) (cont : Straightline K μ ((Fin t × ν) ⊕ ι))
      (x : ι → K) (m : μ),
      (seqRep p t e cont).eval x m
        = cont.eval (Sum.elim (fun z => p.eval (fun a => x (e z.1 a)) z.2) x) m
  | 0, ι, e, cont, x, m => by
      have h : (fun z => x (Sum.elim (fun z : Fin 0 × ν => z.1.elim0) id z))
          = Sum.elim (fun z : Fin 0 × ν => p.eval (fun a => x (e z.1 a)) z.2) x := by
        funext z
        cases z with
        | inl z => exact z.1.elim0
        | inr a => rfl
      rw [seqRep_zero, eval_rename]
      simpa [Function.comp_def] using congrArg (fun env => cont.eval env m) h
  | t + 1, ι, e, cont, x, m => by
      have h : (fun z =>
            Sum.elim
              (fun z : Fin t × ν =>
                p.eval (fun a => Sum.elim ((p.rename (e 0)).eval x) x (Sum.inr (e z.1.succ a)))
                  z.2)
              (Sum.elim ((p.rename (e 0)).eval x) x)
            (Sum.elim
              (fun z : Fin (t + 1) × ν =>
                Fin.cases (Sum.inr (Sum.inl z.2)) (fun i => Sum.inl (i, z.2)) z.1)
              (fun a => Sum.inr (Sum.inr a)) z))
          = Sum.elim (fun z : Fin (t + 1) × ν => p.eval (fun a => x (e z.1 a)) z.2) x := by
        funext z
        cases z with
        | inl z =>
            obtain ⟨i, n⟩ := z
            induction i using Fin.cases with
            | zero => simp [eval_rename, Function.comp_def]
            | succ j => simp
        | inr a => simp
      rw [seqRep_succ, eval_seq, eval_seqRep p t, eval_rename]
      simpa [Function.comp_def] using congrArg (fun env => cont.eval env m) h

section SeqRepCosts

variable [Fintype μ]

/-- Running `t` copies of `p` costs `t` times the linear operations of `p`. -/
theorem linearOps_seqRep {ν ι₀ : Type v} [Fintype ν] (p : Straightline K ν ι₀) :
    ∀ (t : ℕ) {ι : Type v} (e : Fin t → ι₀ → ι) (cont : Straightline K μ ((Fin t × ν) ⊕ ι)),
      (seqRep p t e cont).linearOps = t * p.linearOps + cont.linearOps
  | 0, ι, e, cont => by simp
  | t + 1, ι, e, cont => by
      rw [seqRep_succ, linearOps_seq, linearOps_seqRep p t, linearOps_rename, linearOps_rename,
        Nat.succ_mul]
      omega

/-- Running `t` copies of `p` costs `t` times the multiplication gates of `p`. -/
theorem mulOps_seqRep {ν ι₀ : Type v} [Fintype ν] (p : Straightline K ν ι₀) :
    ∀ (t : ℕ) {ι : Type v} (e : Fin t → ι₀ → ι) (cont : Straightline K μ ((Fin t × ν) ⊕ ι)),
      (seqRep p t e cont).mulOps = t * p.mulOps + cont.mulOps
  | 0, ι, e, cont => by simp
  | t + 1, ι, e, cont => by
      rw [seqRep_succ, mulOps_seq, mulOps_seqRep p t, mulOps_rename, mulOps_rename,
        Nat.succ_mul]
      omega

end SeqRepCosts

/-! ### Selecting a subfamily of output coordinates -/

/-- Reindex the output coordinates of a program along `h : μ' → μ`: the new output `m'` is the
old output `h m'`.  Gates are untouched, so for injective `h` no cost increases. -/
def reindexOut {μ' : Type v} (h : μ' → μ) :
    {ι : Type v} → Straightline K μ ι → Straightline K μ' ι
  | _, .ret out => .ret fun m => out (h m)
  | _, .letBind c body => .letBind c (reindexOut h body)

/-- Reindexing a returning program reindexes its output circuits. -/
@[simp] theorem reindexOut_ret {μ' ι : Type v} (h : μ' → μ) (out : μ → Circuit K ι) :
    reindexOut h (ret out) = ret fun m => out (h m) := rfl

/-- Reindexing passes through a `letBind`. -/
@[simp] theorem reindexOut_letBind {μ' ι : Type v} (h : μ' → μ) (c : Circuit K ι)
    (body : Straightline K μ (Option ι)) :
    reindexOut h (letBind c body) = letBind c (reindexOut h body) := rfl

/-- The reindexed program computes the selected output coordinates of the original. -/
theorem eval_reindexOut [Add K] [Mul K] {μ' : Type v} (h : μ' → μ) :
    ∀ {ι : Type v} (p : Straightline K μ ι) (x : ι → K) (m : μ'),
      (reindexOut h p).eval x m = p.eval x (h m)
  | _, .ret out, x, m => rfl
  | _, .letBind c body, x, m => by
      rw [reindexOut_letBind, eval_letBind, eval_letBind, eval_reindexOut h body]

section ReindexCosts

variable [Fintype μ] {μ' : Type v} [Fintype μ']

/-- Selecting an injective subfamily of outputs does not increase the linear-operation count. -/
theorem linearOps_reindexOut_le {h : μ' → μ} (hh : Function.Injective h) :
    ∀ {ι : Type v} (p : Straightline K μ ι), (reindexOut h p).linearOps ≤ p.linearOps
  | _, .ret out => by
      classical
      rw [reindexOut_ret, linearOps_ret, linearOps_ret]
      calc ∑ m : μ', (out (h m)).linearOps
          = ∑ m ∈ Finset.univ.image h, (out m).linearOps := by
            rw [Finset.sum_image fun a _ b _ hab => hh hab]
        _ ≤ ∑ m : μ, (out m).linearOps :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  | _, .letBind c body => by
      rw [reindexOut_letBind, linearOps_letBind, linearOps_letBind]
      exact Nat.add_le_add_left (linearOps_reindexOut_le hh body) _

/-- Selecting an injective subfamily of outputs does not increase the multiplication count. -/
theorem mulOps_reindexOut_le {h : μ' → μ} (hh : Function.Injective h) :
    ∀ {ι : Type v} (p : Straightline K μ ι), (reindexOut h p).mulOps ≤ p.mulOps
  | _, .ret out => by
      classical
      rw [reindexOut_ret, mulOps_ret, mulOps_ret]
      calc ∑ m : μ', (out (h m)).mulOps
          = ∑ m ∈ Finset.univ.image h, (out m).mulOps := by
            rw [Finset.sum_image fun a _ b _ hab => hh hab]
        _ ≤ ∑ m : μ, (out m).mulOps :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  | _, .letBind c body => by
      rw [reindexOut_letBind, mulOps_letBind, mulOps_letBind]
      exact Nat.add_le_add_left (mulOps_reindexOut_le hh body) _

end ReindexCosts

/-! ### Programs computing a square matrix product -/

/-- `p` computes the square matrix product on the index type `M`: reading an `M × M` matrix `x`
on the `Sum.inl` inputs and an `M × M` matrix `y` on the `Sum.inr` inputs, the output coordinate
`z` is the entry of `x * y` in row `z.2` and column `z.1`.  The transposed output convention is
the one of `matrixProductMap`, hence of the `Z` leg of `matrixMultiplication`. -/
def ComputesMatrixProduct {K : Type u} [AddCommMonoid K] [Mul K] {M : Type} [Fintype M]
    (p : Straightline K (M × M) ((M × M) ⊕ (M × M))) : Prop :=
  ∀ (x y : M × M → K) (z : M × M),
    p.eval (Sum.elim x y) z = ∑ j, x (z.2, j) * y (j, z.1)

end Straightline

open Straightline

/-! ### The base case: a single multiplication -/

/-- The one-gate program for the `1 × 1` matrix product. -/
def baseProgram (K : Type u) :
    Straightline K (Fin 1 × Fin 1) ((Fin 1 × Fin 1) ⊕ (Fin 1 × Fin 1)) :=
  .ret fun _ => .mul (.input (Sum.inl (0, 0))) (.input (Sum.inr (0, 0)))

variable {K : Type u}

/-- The base program computes the `1 × 1` matrix product. -/
theorem computesMatrixProduct_baseProgram [CommSemiring K] :
    ComputesMatrixProduct (baseProgram K) := by
  intro x y z
  obtain ⟨a, b⟩ := z
  have ha : a = 0 := Subsingleton.elim _ _
  have hb : b = 0 := Subsingleton.elim _ _
  subst ha
  subst hb
  simp [baseProgram]

/-- The base program has exactly one multiplication gate. -/
@[simp] theorem mulOps_baseProgram : (baseProgram K).mulOps = 1 := by
  simp [baseProgram]

/-- The base program has no linear operation. -/
@[simp] theorem linearOps_baseProgram : (baseProgram K).linearOps = 0 := by
  simp [baseProgram]

/-- The base program costs exactly one operation. -/
theorem totalOps_baseProgram : (baseProgram K).totalOps = 1 := by
  simp [Straightline.totalOps_eq]

/-! ### One level of the block recursion -/

section BlockStep

variable [CommSemiring K] {q r : ℕ}
  (A : BilinearAlgorithm K (Fin q × Fin q) (Fin q × Fin q) (Fin q × Fin q) r)
  {M : Type} [Fintype M]

/-- The circuit computing the `(i, j)` entry of the `t`-th left linear form of the algorithm
applied to the `q × q` array of blocks of the first input: `∑_{a,b} f t (a,b) * x ((a,i),(b,j))`.
It uses `2 * q^2 - 1` linear operations and no multiplication gate. -/
noncomputable def blockLeftForm (t : Fin r) (ij : M × M) :
    Circuit K (((Fin q × M) × (Fin q × M)) ⊕ ((Fin q × M) × (Fin q × M))) :=
  (Circuit.linearComb (A.f t)).map fun ab => Sum.inl ((ab.1, ij.1), (ab.2, ij.2))

/-- The circuit computing the `(i, j)` entry of the `t`-th right linear form of the algorithm
applied to the `q × q` array of blocks of the second input. -/
noncomputable def blockRightForm (t : Fin r) (ij : M × M) :
    Circuit K (((Fin q × M) × (Fin q × M)) ⊕ ((Fin q × M) × (Fin q × M))) :=
  (Circuit.linearComb (A.g t)).map fun ab => Sum.inr ((ab.1, ij.1), (ab.2, ij.2))

/-- The whole family of block linear forms, indexed by a side, a multiplication index `t`, and an
entry of the block. -/
noncomputable def blockForms :
    (Fin r × (M × M)) ⊕ (Fin r × (M × M)) →
      Circuit K (((Fin q × M) × (Fin q × M)) ⊕ ((Fin q × M) × (Fin q × M))) :=
  Sum.elim (fun z => blockLeftForm A z.1 z.2) fun z => blockRightForm A z.1 z.2

/-- The output circuit of a block step: the `z`-th output is `∑ t, w t (z.1.1, z.2.1)` times the
register holding the `(z.1.2, z.2.2)` entry of the `t`-th recursive block product. -/
noncomputable def blockOutput (z : (Fin q × M) × (Fin q × M)) :
    Circuit K ((Fin r × (M × M)) ⊕
      (((Fin r × (M × M)) ⊕ (Fin r × (M × M))) ⊕
        ((((Fin q × M) × (Fin q × M)) ⊕ ((Fin q × M) × (Fin q × M)))))) :=
  (Circuit.linearComb fun t : Fin r => A.w t (z.1.1, z.2.1)).map
    fun t => Sum.inl (t, (z.1.2, z.2.2))

/-- **One level of Strassen's block recursion.**  Given a length-`r` bilinear algorithm `A` for
the `q × q` product and a program `p` for the `M × M` product, `blockStep A p` computes the
`(Fin q × M) × (Fin q × M)` product: it forms the `2 * r` block linear forms entrywise, runs `r`
renamed copies of `p` on them, and recombines the results into the output blocks. -/
noncomputable def blockStep (p : Straightline K (M × M) ((M × M) ⊕ (M × M))) :
    Straightline K ((Fin q × M) × (Fin q × M))
      (((Fin q × M) × (Fin q × M)) ⊕ ((Fin q × M) × (Fin q × M))) :=
  bindFamily (blockForms A)
    (seqRep p r
      (fun t =>
        Sum.elim (fun ij => Sum.inl (Sum.inl (t, ij))) fun ij => Sum.inl (Sum.inr (t, ij)))
      (.ret (blockOutput A)))

omit [Fintype M] in
/-- Value of a left block form. -/
theorem eval_blockLeftForm (t : Fin r) (ij : M × M)
    (X Y : (Fin q × M) × (Fin q × M) → K) :
    (blockLeftForm A t ij).eval (Sum.elim X Y)
      = ∑ ab, A.f t ab * X ((ab.1, ij.1), (ab.2, ij.2)) := by
  simp [blockLeftForm, Function.comp_def]

omit [Fintype M] in
/-- Value of a right block form. -/
theorem eval_blockRightForm (t : Fin r) (ij : M × M)
    (X Y : (Fin q × M) × (Fin q × M) → K) :
    (blockRightForm A t ij).eval (Sum.elim X Y)
      = ∑ ab, A.g t ab * Y ((ab.1, ij.1), (ab.2, ij.2)) := by
  simp [blockRightForm, Function.comp_def]

/-- Evaluation of one block step, before the algorithm's defining identity is used: the `z`-th
output is `∑ t, w t (z.1.1, z.2.1)` times the `(z.1.2, z.2.2)` entry of the product computed by
the `t`-th recursive copy on the two block linear forms. -/
theorem eval_blockStep (p : Straightline K (M × M) ((M × M) ⊕ (M × M)))
    (X Y : (Fin q × M) × (Fin q × M) → K) (z : (Fin q × M) × (Fin q × M)) :
    (blockStep A p).eval (Sum.elim X Y) z
      = ∑ t, A.w t (z.1.1, z.2.1) *
          p.eval
            (Sum.elim (fun ij : M × M => ∑ ab, A.f t ab * X ((ab.1, ij.1), (ab.2, ij.2)))
              fun ij : M × M => ∑ ab, A.g t ab * Y ((ab.1, ij.1), (ab.2, ij.2)))
            (z.1.2, z.2.2) := by
  rw [blockStep, eval_bindFamily, eval_seqRep]
  simp only [eval_ret, blockOutput, Circuit.eval_map, Circuit.eval_linearComb, Function.comp_def,
    Sum.elim_inl]
  refine Finset.sum_congr rfl fun t _ =>
    congrArg (fun E => A.w t (z.1.1, z.2.1) * p.eval E (z.1.2, z.2.2)) ?_
  funext a
  cases a <;> simp [blockForms, eval_blockLeftForm, eval_blockRightForm]

/-- **Block substitution.**  If the scalar algorithm `A` computes the `q × q` matrix product,
then applying it to `q × q` arrays of blocks computes the block matrix product.  The identity is
applied one inner coordinate at a time: for a fixed inner column `w`, the `q × q` arrays
`(a, b) ↦ X ((a, v), (b, w))` and `(a, b) ↦ Y ((a, w), (b, u))` are ordinary scalar matrices, and
the algorithm's own correctness on them is exactly the required identity.  Summing over `w` and
regrouping the pair `(e, w)` into a single index of `Fin q × M` gives the block product.

Note that no commutativity between blocks is needed: the algorithm's coefficients are scalars and
the two linear forms are kept in the order left form times right form. -/
theorem sum_blockAlgorithm (hA : A.Computes (matrixProductMap (K := K) q q q))
    (X Y : (Fin q × M) × (Fin q × M) → K) (c d : Fin q) (u v : M) :
    ∑ t, A.w t (c, d) *
        (∑ w : M, (∑ ab, A.f t ab * X ((ab.1, v), (ab.2, w))) *
          (∑ ab, A.g t ab * Y ((ab.1, w), (ab.2, u))))
      = ∑ J : Fin q × M, X ((d, v), J) * Y (J, (c, u)) := by
  have key : ∀ w : M,
      ∑ t, A.w t (c, d) * ((∑ ab, A.f t ab * X ((ab.1, v), (ab.2, w))) *
          (∑ ab, A.g t ab * Y ((ab.1, w), (ab.2, u))))
        = ∑ e : Fin q, X ((d, v), (e, w)) * Y ((e, w), (c, u)) := by
    intro w
    have h := hA (fun ab => X ((ab.1, v), (ab.2, w))) (fun ab => Y ((ab.1, w), (ab.2, u))) (c, d)
    simp only [matrixProductMap_apply] at h
    rw [h]
    exact Finset.sum_congr rfl fun t _ => (mul_assoc _ _ _).symm
  calc ∑ t, A.w t (c, d) *
        (∑ w : M, (∑ ab, A.f t ab * X ((ab.1, v), (ab.2, w))) *
          (∑ ab, A.g t ab * Y ((ab.1, w), (ab.2, u))))
      = ∑ t, ∑ w : M, A.w t (c, d) * ((∑ ab, A.f t ab * X ((ab.1, v), (ab.2, w))) *
            (∑ ab, A.g t ab * Y ((ab.1, w), (ab.2, u)))) :=
        Finset.sum_congr rfl fun t _ => Finset.mul_sum _ _ _
    _ = ∑ w : M, ∑ t, A.w t (c, d) * ((∑ ab, A.f t ab * X ((ab.1, v), (ab.2, w))) *
            (∑ ab, A.g t ab * Y ((ab.1, w), (ab.2, u)))) := Finset.sum_comm
    _ = ∑ w : M, ∑ e : Fin q, X ((d, v), (e, w)) * Y ((e, w), (c, u)) :=
        Finset.sum_congr rfl fun w _ => key w
    _ = ∑ J : Fin q × M, X ((d, v), J) * Y (J, (c, u)) := by
        rw [Fintype.sum_prod_type]
        exact Finset.sum_comm

/-- **Correctness of one block step.**  If `A` computes the `q × q` matrix product and `p`
computes the `M × M` matrix product, then `blockStep A p` computes the
`(Fin q × M) × (Fin q × M)` matrix product. -/
theorem computesMatrixProduct_blockStep (hA : A.Computes (matrixProductMap (K := K) q q q))
    {p : Straightline K (M × M) ((M × M) ⊕ (M × M))} (hp : ComputesMatrixProduct p) :
    ComputesMatrixProduct (blockStep A p) := by
  intro X Y z
  obtain ⟨⟨c, u⟩, ⟨d, v⟩⟩ := z
  rw [eval_blockStep]
  refine Eq.trans (Finset.sum_congr rfl fun t _ => ?_) (sum_blockAlgorithm A hA X Y c d u v)
  rw [hp]

/-! #### Cost of one block step -/

/-- A block step contains exactly `r` copies of the gates of `p` and no other multiplication
gate. -/
theorem mulOps_blockStep (p : Straightline K (M × M) ((M × M) ⊕ (M × M))) :
    (blockStep A p).mulOps = r * p.mulOps := by
  rw [blockStep, mulOps_bindFamily, mulOps_seqRep, mulOps_ret]
  simp [blockForms, blockLeftForm, blockRightForm, blockOutput,
    Circuit.mulOps_linearComb]

/-- A block step adds at most `6 * r * q^2 * |M|^2` linear operations to the `r` recursive
copies: `2 * r * |M|^2` block linear forms of `q^2` terms each, and `q^2 * |M|^2` output
combinations of `r` terms each. -/
theorem linearOps_blockStep_le (p : Straightline K (M × M) ((M × M) ⊕ (M × M))) :
    (blockStep A p).linearOps
      ≤ r * p.linearOps + 6 * (r * (q * q) * (Fintype.card M * Fintype.card M)) := by
  have hform : (∑ n, (blockForms (M := M) A n).linearOps)
      = (r * (Fintype.card M * Fintype.card M) + r * (Fintype.card M * Fintype.card M)) *
          (2 * (q * q) - 1) := by
    have hf : ∀ n, (blockForms (M := M) A n).linearOps = 2 * (q * q) - 1 := by
      intro n
      cases n <;> simp [blockForms, blockLeftForm, blockRightForm, Circuit.linearOps_linearComb]
    rw [Finset.sum_congr rfl fun n _ => hf n, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
  have hout : (∑ z, (blockOutput (M := M) A z).linearOps)
      = (q * Fintype.card M) * (q * Fintype.card M) * (2 * r - 1) := by
    have hf : ∀ z, (blockOutput (M := M) A z).linearOps = 2 * r - 1 := by
      intro z
      simp [blockOutput, Circuit.linearOps_linearComb]
    rw [Finset.sum_congr rfl fun z _ => hf z, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    simp [Fintype.card_prod]
  have e1 : (r * (Fintype.card M * Fintype.card M) + r * (Fintype.card M * Fintype.card M)) *
        (2 * (q * q) - 1)
      ≤ 4 * (r * (q * q) * (Fintype.card M * Fintype.card M)) := by
    calc (r * (Fintype.card M * Fintype.card M) + r * (Fintype.card M * Fintype.card M)) *
            (2 * (q * q) - 1)
        ≤ (r * (Fintype.card M * Fintype.card M) + r * (Fintype.card M * Fintype.card M)) *
            (2 * (q * q)) := Nat.mul_le_mul_left _ (by omega)
      _ = 4 * (r * (q * q) * (Fintype.card M * Fintype.card M)) := by ring
  have e2 : (q * Fintype.card M) * (q * Fintype.card M) * (2 * r - 1)
      ≤ 2 * (r * (q * q) * (Fintype.card M * Fintype.card M)) := by
    calc (q * Fintype.card M) * (q * Fintype.card M) * (2 * r - 1)
        ≤ (q * Fintype.card M) * (q * Fintype.card M) * (2 * r) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (r * (q * q) * (Fintype.card M * Fintype.card M)) := by ring
  rw [blockStep, linearOps_bindFamily, linearOps_seqRep, linearOps_ret, hform, hout]
  calc (r * (Fintype.card M * Fintype.card M) + r * (Fintype.card M * Fintype.card M)) *
          (2 * (q * q) - 1)
        + (r * p.linearOps + (q * Fintype.card M) * (q * Fintype.card M) * (2 * r - 1))
      ≤ 4 * (r * (q * q) * (Fintype.card M * Fintype.card M))
        + (r * p.linearOps + 2 * (r * (q * q) * (Fintype.card M * Fintype.card M))) :=
        Nat.add_le_add e1 (Nat.add_le_add_left e2 _)
    _ = r * p.linearOps + 6 * (r * (q * q) * (Fintype.card M * Fintype.card M)) := by ring

/-- Total cost of one block step: `r` recursive copies plus `6 * r * q^2 * |M|^2` block
additions and scalar multiplications. -/
theorem totalOps_blockStep_le (p : Straightline K (M × M) ((M × M) ⊕ (M × M))) :
    (blockStep A p).totalOps
      ≤ r * p.totalOps + 6 * (r * (q * q) * (Fintype.card M * Fintype.card M)) := by
  rw [Straightline.totalOps_eq, Straightline.totalOps_eq, mulOps_blockStep, Nat.mul_add]
  calc (blockStep A p).linearOps + r * p.mulOps
      ≤ (r * p.linearOps + 6 * (r * (q * q) * (Fintype.card M * Fintype.card M)))
          + r * p.mulOps := Nat.add_le_add_right (linearOps_blockStep_le A p) _
    _ = r * p.linearOps + r * p.mulOps
          + 6 * (r * (q * q) * (Fintype.card M * Fintype.card M)) := by ring

end BlockStep

/-! ### Transporting a program along a bijection of index sets -/

section ReindexEquiv

variable {K : Type u} {μ μ' : Type v} [Fintype μ] [Fintype μ']

namespace Straightline

/-- Reindexing the outputs along a bijection preserves the linear-operation count. -/
theorem linearOps_reindexOut_bijective {h : μ' → μ} (hh : Function.Bijective h) :
    ∀ {ι : Type v} (p : Straightline K μ ι), (reindexOut h p).linearOps = p.linearOps
  | _, .ret out => by
      rw [reindexOut_ret, linearOps_ret, linearOps_ret]
      exact Fintype.sum_bijective h hh _ _ fun _ => rfl
  | _, .letBind c body => by
      rw [reindexOut_letBind, linearOps_letBind, linearOps_letBind,
        linearOps_reindexOut_bijective hh body]

/-- Reindexing the outputs along a bijection preserves the multiplication-gate count. -/
theorem mulOps_reindexOut_bijective {h : μ' → μ} (hh : Function.Bijective h) :
    ∀ {ι : Type v} (p : Straightline K μ ι), (reindexOut h p).mulOps = p.mulOps
  | _, .ret out => by
      rw [reindexOut_ret, mulOps_ret, mulOps_ret]
      exact Fintype.sum_bijective h hh _ _ fun _ => rfl
  | _, .letBind c body => by
      rw [reindexOut_letBind, mulOps_letBind, mulOps_letBind, mulOps_reindexOut_bijective hh body]

end Straightline

end ReindexEquiv

section Transport

variable {K : Type u} [CommSemiring K] {N N' : Type} [Fintype N] [Fintype N']

/-- Transport a matrix-product program along a bijection `ε : N ≃ N'` of index sets: the inputs
are renamed and the outputs are selected through `ε`.  No gate is added or removed. -/
noncomputable def transport (ε : N ≃ N')
    (p : Straightline K (N × N) ((N × N) ⊕ (N × N))) :
    Straightline K (N' × N') ((N' × N') ⊕ (N' × N')) :=
  Straightline.reindexOut (Prod.map ε.symm ε.symm)
    (p.rename (Sum.map (Prod.map ε ε) (Prod.map ε ε)))

/-- Transport along a bijection preserves computing the matrix product.

Proof sketch: renaming the inputs feeds the transported program's matrices to `p` through `ε`,
and selecting the output `(ε.symm z.1, ε.symm z.2)` undoes the relabelling; the inner sum is
reindexed by `ε` (`Equiv.sum_comp`). -/
theorem computesMatrixProduct_transport (ε : N ≃ N')
    {p : Straightline K (N × N) ((N × N) ⊕ (N × N))}
    (hp : Straightline.ComputesMatrixProduct p) :
    Straightline.ComputesMatrixProduct (transport ε p) := by
  intro X Y z
  have h : (Sum.elim X Y) ∘ (Sum.map (Prod.map ε ε) (Prod.map ε ε))
      = Sum.elim (fun ab : N × N => X (ε ab.1, ε ab.2))
          fun ab : N × N => Y (ε ab.1, ε ab.2) := by
    funext w
    cases w <;> rfl
  rw [transport, Straightline.eval_reindexOut, Straightline.eval_rename, h, hp]
  simp only [Prod.map_fst, Prod.map_snd, Equiv.apply_symm_apply]
  exact Equiv.sum_comp ε fun j => X (z.2, j) * Y (j, z.1)

omit [Fintype N] [Fintype N'] in
/-- Relabelling both matrix coordinates by a bijection is a bijection. -/
theorem bijective_prodMap_symm (ε : N ≃ N') :
    Function.Bijective (Prod.map ε.symm ε.symm : N' × N' → N × N) := by
  constructor
  · intro a b hab
    simpa [Prod.ext_iff] using hab
  · intro b
    exact ⟨(ε b.1, ε b.2), by simp⟩

omit [CommSemiring K] in
/-- Transport permutes the outputs, so it preserves the multiplication-gate count. -/
@[simp] theorem mulOps_transport (ε : N ≃ N')
    (p : Straightline K (N × N) ((N × N) ⊕ (N × N))) :
    (transport ε p).mulOps = p.mulOps := by
  rw [transport, Straightline.mulOps_reindexOut_bijective (bijective_prodMap_symm ε),
    Straightline.mulOps_rename]

omit [CommSemiring K] in
/-- Transport preserves the linear-operation count. -/
@[simp] theorem linearOps_transport (ε : N ≃ N')
    (p : Straightline K (N × N) ((N × N) ⊕ (N × N))) :
    (transport ε p).linearOps = p.linearOps := by
  rw [transport, Straightline.linearOps_reindexOut_bijective (bijective_prodMap_symm ε),
    Straightline.linearOps_rename]

omit [CommSemiring K] in
/-- Transport preserves the total operation count. -/
@[simp] theorem totalOps_transport (ε : N ≃ N')
    (p : Straightline K (N × N) ((N × N) ⊕ (N × N))) :
    (transport ε p).totalOps = p.totalOps := by
  rw [Straightline.totalOps_eq, Straightline.totalOps_eq, mulOps_transport, linearOps_transport]

end Transport

/-! ### The recursive program for `q^k × q^k` matrix multiplication -/

section PowProgram

variable {K : Type u} [CommSemiring K] {q r : ℕ}
  (A : BilinearAlgorithm K (Fin q × Fin q) (Fin q × Fin q) (Fin q × Fin q) r)

/-- Splitting an index of a side of length `q^(k+1)` into a block coordinate in `Fin q` and an
inner coordinate in `Fin (q^k)`. -/
def blockEquiv (q k : ℕ) : Fin q × Fin (q ^ k) ≃ Fin (q ^ (k + 1)) :=
  finProdFinEquiv.trans (finCongr (by ring))

/-- **The `k`-fold recursive block program.**  Iterating `blockStep` `k` times on the one-gate
base program gives a straight-line program for the `q^k × q^k` matrix product; each level is
transported along `blockEquiv` so that the side length is literally `Fin (q ^ k)`. -/
noncomputable def powProgram : (k : ℕ) →
    Straightline K (Fin (q ^ k) × Fin (q ^ k))
      ((Fin (q ^ k) × Fin (q ^ k)) ⊕ (Fin (q ^ k) × Fin (q ^ k)))
  | 0 => transport (finCongr (pow_zero q).symm) (baseProgram K)
  | k + 1 => transport (blockEquiv q k) (blockStep A (powProgram k))

/-- At level `0` the recursion is the single-gate program. -/
theorem powProgram_zero :
    powProgram A 0 = transport (finCongr (pow_zero q).symm) (baseProgram K) := rfl

/-- Each level of the recursion is one block step on the previous level. -/
theorem powProgram_succ (k : ℕ) :
    powProgram A (k + 1) = transport (blockEquiv q k) (blockStep A (powProgram A k)) := rfl

/-- **The recursive program is correct.**  If `A` computes the `q × q` matrix product, then
`powProgram A k` computes the `q^k × q^k` matrix product. -/
theorem computesMatrixProduct_powProgram (hA : A.Computes (matrixProductMap (K := K) q q q)) :
    ∀ k : ℕ, Straightline.ComputesMatrixProduct (powProgram A k)
  | 0 => by
      rw [powProgram_zero]
      exact computesMatrixProduct_transport _ computesMatrixProduct_baseProgram
  | k + 1 => by
      rw [powProgram_succ]
      exact computesMatrixProduct_transport _
        (computesMatrixProduct_blockStep A hA (computesMatrixProduct_powProgram hA k))

/-- **Exact multiplication count.**  The level-`k` program has exactly `r^k` multiplication
gates: one per leaf of the `r`-ary recursion tree of depth `k`.  In particular it performs at
most `r^k` nonscalar multiplications. -/
theorem mulOps_powProgram : ∀ k : ℕ, (powProgram A k).mulOps = r ^ k
  | 0 => by rw [powProgram_zero, mulOps_transport, mulOps_baseProgram, pow_zero]
  | k + 1 => by
      rw [powProgram_succ, mulOps_transport, mulOps_blockStep, mulOps_powProgram, pow_succ]
      ring

/-- The level-`k` program performs at most `r^k` nonscalar multiplications. -/
theorem nonscalarMuls_powProgram_le (k : ℕ) : (powProgram A k).nonscalarMuls ≤ r ^ k := by
  rw [← mulOps_powProgram A k]
  exact Straightline.nonscalarMulsOn_le_mulOps _ _

/-- Strengthened cost invariant for the recursion, carrying the `q^{2k}` term that makes the
induction go through.

Proof sketch: one block step costs `r` recursive calls plus `c * q^{2k}` block additions, with
`c = 6 * r * q^2`.  The statement `T k + c * q^{2k} ≤ (1 + c) * r^k` is preserved because
`c * q^{2k} + c * q^{2k+2} = c * q^{2k} * (1 + q^2) ≤ c * q^{2k} * r` exactly when `q^2 < r`;
this is the geometric-series comparison that makes the classical recursion `Θ(r^k)` rather than
`Θ(q^{2k})`. -/
theorem totalOps_powProgram_add_le (hqr : q * q < r) : ∀ k : ℕ,
    (powProgram A k).totalOps + 6 * (r * (q * q)) * (q ^ k * q ^ k)
      ≤ (1 + 6 * (r * (q * q))) * r ^ k := by
  have hq : 1 + q * q ≤ r := by omega
  intro k
  induction k with
  | zero =>
      rw [powProgram_zero, totalOps_transport, totalOps_baseProgram]
      simp
  | succ k ih =>
      have hstep : (powProgram A (k + 1)).totalOps
          ≤ r * (powProgram A k).totalOps + 6 * (r * (q * q)) * (q ^ k * q ^ k) := by
        rw [powProgram_succ, totalOps_transport]
        refine le_trans (totalOps_blockStep_le A (powProgram A k)) (le_of_eq ?_)
        rw [Fintype.card_fin]
        ring
      calc (powProgram A (k + 1)).totalOps + 6 * (r * (q * q)) * (q ^ (k + 1) * q ^ (k + 1))
          ≤ (r * (powProgram A k).totalOps + 6 * (r * (q * q)) * (q ^ k * q ^ k))
              + 6 * (r * (q * q)) * (q ^ (k + 1) * q ^ (k + 1)) :=
            Nat.add_le_add_right hstep _
        _ = r * (powProgram A k).totalOps
              + 6 * (r * (q * q)) * (q ^ k * q ^ k) * (1 + q * q) := by ring
        _ ≤ r * (powProgram A k).totalOps
              + 6 * (r * (q * q)) * (q ^ k * q ^ k) * r :=
            Nat.add_le_add_left (Nat.mul_le_mul_left _ hq) _
        _ = r * ((powProgram A k).totalOps + 6 * (r * (q * q)) * (q ^ k * q ^ k)) := by ring
        _ ≤ r * ((1 + 6 * (r * (q * q))) * r ^ k) := Nat.mul_le_mul_left _ ih
        _ = (1 + 6 * (r * (q * q))) * r ^ (k + 1) := by ring

/-- **Total cost of the recursive program.**  For `q^2 < r`, the level-`k` program performs at
most `(1 + 6 * r * q^2) * r^k` arithmetic operations in total — a constant depending only on the
base algorithm times the number `r^k` of multiplications. -/
theorem totalOps_powProgram_le (hqr : q * q < r) (k : ℕ) :
    (powProgram A k).totalOps ≤ (1 + 6 * (r * (q * q))) * r ^ k :=
  le_trans (Nat.le_add_right _ _) (totalOps_powProgram_add_le A hqr k)

end PowProgram

/-! ### Padding an arbitrary side length into a power of `q` -/

section Pad

variable {K : Type u} [CommSemiring K] {n N : ℕ}

/-- The `n × n` index underlying an `N × N` index, when both coordinates are in range. -/
def padIndex (n : ℕ) {N : ℕ} (ab : Fin N × Fin N) : Option (Fin n × Fin n) :=
  if h : (ab.1 : ℕ) < n ∧ (ab.2 : ℕ) < n then some (⟨ab.1, h.1⟩, ⟨ab.2, h.2⟩) else none

/-- The renaming sending each input entry of the large program either to the corresponding
entry of the small program or to the fresh zero register `none`. -/
def padRename (n : ℕ) {N : ℕ} :
    (Fin N × Fin N) ⊕ (Fin N × Fin N) → Option ((Fin n × Fin n) ⊕ (Fin n × Fin n)) :=
  Sum.elim (fun ab => (padIndex n ab).map Sum.inl) fun ab => (padIndex n ab).map Sum.inr

/-- The zero-padding of an `n × n` matrix to an `N × N` matrix. -/
def padMatrix (x : Fin n × Fin n → K) (ab : Fin N × Fin N) : K :=
  if h : (ab.1 : ℕ) < n ∧ (ab.2 : ℕ) < n then x (⟨ab.1, h.1⟩, ⟨ab.2, h.2⟩) else 0

/-- Padding restricted to in-range entries is the original matrix. -/
theorem padMatrix_castLE (hn : n ≤ N) (x : Fin n × Fin n → K) (a b : Fin n) :
    padMatrix (N := N) x (Fin.castLE hn a, Fin.castLE hn b) = x (a, b) := by
  have h : ((Fin.castLE hn a : Fin N) : ℕ) < n ∧ ((Fin.castLE hn b : Fin N) : ℕ) < n := ⟨a.2, b.2⟩
  simp only [padMatrix, dif_pos h]
  rfl

/-- Padding vanishes on an out-of-range column. -/
theorem padMatrix_of_le_right (x : Fin n × Fin n → K) (a J : Fin N) (hJ : n ≤ (J : ℕ)) :
    padMatrix x (a, J) = 0 := by
  have h : ¬ ((a : ℕ) < n ∧ (J : ℕ) < n) := by omega
  simp only [padMatrix, dif_neg h]

/-- Padding vanishes on an out-of-range row. -/
theorem padMatrix_of_le_left (x : Fin n × Fin n → K) (J a : Fin N) (hJ : n ≤ (J : ℕ)) :
    padMatrix x (J, a) = 0 := by
  have h : ¬ ((J : ℕ) < n ∧ (a : ℕ) < n) := by omega
  simp only [padMatrix, dif_neg h]

/-- Truncating a sum over `Fin N` to a sum over the first `n` indices, for a summand vanishing
beyond them. -/
private theorem sum_castLE_of_vanishing {M : Type*} [AddCommMonoid M] (hn : n ≤ N)
    (F : Fin N → M) (hF : ∀ J : Fin N, n ≤ (J : ℕ) → F J = 0) :
    ∑ J : Fin N, F J = ∑ j : Fin n, F (Fin.castLE hn j) := by
  classical
  have himg : ∑ j : Fin n, F (Fin.castLE hn j)
      = ∑ J ∈ Finset.univ.image (Fin.castLE hn), F J := by
    rw [Finset.sum_image fun a _ b _ hab => Fin.castLE_injective hn hab]
  rw [himg]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro J _ hJ
  refine hF J ?_
  by_contra hlt
  exact hJ (Finset.mem_image.mpr ⟨⟨J, by omega⟩, Finset.mem_univ _, rfl⟩)

/-- **Padding.**  A program for the `N × N` matrix product restricts to one for the `n × n`
product whenever `n ≤ N`: bind one constant-zero register, rename every out-of-range input entry
to it, and read only the in-range output entries.  No gate is added. -/
noncomputable def padProgram (hn : n ≤ N)
    (p : Straightline K (Fin N × Fin N) ((Fin N × Fin N) ⊕ (Fin N × Fin N))) :
    Straightline K (Fin n × Fin n) ((Fin n × Fin n) ⊕ (Fin n × Fin n)) :=
  .letBind (.const 0)
    (Straightline.reindexOut (Prod.map (Fin.castLE hn) (Fin.castLE hn)) (p.rename (padRename n)))

/-- Reading the two matrix coordinates of an in-range output is injective. -/
theorem injective_prodMap_castLE (hn : n ≤ N) :
    Function.Injective
      (Prod.map (Fin.castLE hn) (Fin.castLE hn) : Fin n × Fin n → Fin N × Fin N) := by
  intro a b hab
  simpa [Prod.ext_iff, Fin.ext_iff] using hab

/-- **Correctness of padding.**  If `p` computes the `N × N` matrix product and `n ≤ N`, then
`padProgram hn p` computes the `n × n` matrix product.

Proof sketch: the renamed environment is exactly the zero-padding of the two input matrices, so
the large program returns the `N × N` product of the padded matrices; every term of its inner sum
with an out-of-range summation index vanishes, and the remaining terms are the entries of the
small product. -/
theorem computesMatrixProduct_padProgram (hn : n ≤ N)
    {p : Straightline K (Fin N × Fin N) ((Fin N × Fin N) ⊕ (Fin N × Fin N))}
    (hp : Straightline.ComputesMatrixProduct p) :
    Straightline.ComputesMatrixProduct (padProgram hn p) := by
  intro x y z
  have henv : extendEnv (0 : K) (Sum.elim x y) ∘ padRename n
      = Sum.elim (padMatrix (N := N) x) (padMatrix (N := N) y) := by
    funext w
    rcases w with ab | ab <;>
      · by_cases h : (ab.1 : ℕ) < n ∧ (ab.2 : ℕ) < n
        · simp [padRename, padIndex, padMatrix, h]
        · simp [padRename, padIndex, padMatrix, h]
  rw [padProgram, Straightline.eval_letBind, Straightline.eval_reindexOut,
    Straightline.eval_rename, Circuit.eval_const, henv, hp]
  have hvanish : ∀ J : Fin N, n ≤ (J : ℕ) →
      padMatrix x ((Prod.map (Fin.castLE hn) (Fin.castLE hn) z).2, J) *
        padMatrix y (J, (Prod.map (Fin.castLE hn) (Fin.castLE hn) z).1) = 0 := by
    intro J hJ
    rw [padMatrix_of_le_right x _ J hJ, zero_mul]
  rw [sum_castLE_of_vanishing hn _ hvanish]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Prod.map_fst, Prod.map_snd, padMatrix_castLE hn x z.2 j, padMatrix_castLE hn y j z.1]

/-- Padding adds no multiplication gate. -/
theorem mulOps_padProgram_le (hn : n ≤ N)
    (p : Straightline K (Fin N × Fin N) ((Fin N × Fin N) ⊕ (Fin N × Fin N))) :
    (padProgram hn p).mulOps ≤ p.mulOps := by
  rw [padProgram, Straightline.mulOps_letBind, Circuit.mulOps_const, Nat.zero_add]
  exact le_trans (Straightline.mulOps_reindexOut_le (injective_prodMap_castLE hn) _)
    (le_of_eq (Straightline.mulOps_rename _ _))

/-- Padding adds no linear operation. -/
theorem linearOps_padProgram_le (hn : n ≤ N)
    (p : Straightline K (Fin N × Fin N) ((Fin N × Fin N) ⊕ (Fin N × Fin N))) :
    (padProgram hn p).linearOps ≤ p.linearOps := by
  rw [padProgram, Straightline.linearOps_letBind, Circuit.linearOps_const, Nat.zero_add]
  exact le_trans (Straightline.linearOps_reindexOut_le (injective_prodMap_castLE hn) _)
    (le_of_eq (Straightline.linearOps_rename _ _))

/-- Padding does not increase the total operation count. -/
theorem totalOps_padProgram_le (hn : n ≤ N)
    (p : Straightline K (Fin N × Fin N) ((Fin N × Fin N) ⊕ (Fin N × Fin N))) :
    (padProgram hn p).totalOps ≤ p.totalOps := by
  rw [Straightline.totalOps_eq, Straightline.totalOps_eq]
  exact Nat.add_le_add (linearOps_padProgram_le hn p) (mulOps_padProgram_le hn p)

end Pad

/-! ### The headline: rank certificates compile to arithmetic circuits -/

section Headline

open Tensor

variable {K : Type u} [CommSemiring K] {q r : ℕ}

/-- **Recursive compilation of a rank certificate into straight-line programs.**  A rank-`r`
decomposition of the `q × q × q` matrix-multiplication tensor with `q^2 < r` yields, for every
`n`, a straight-line program computing the `n × n` matrix product with at most
`r ^ ⌈log_q n⌉` multiplication gates and at most `(1 + 6 * r * q^2) * r ^ ⌈log_q n⌉` arithmetic
operations in total.

Proof sketch: the rank certificate is a length-`r` bilinear algorithm (`Fact 2.9`); `powProgram`
iterates the block substitution `k = ⌈log_q n⌉` times, giving exactly `r^k` multiplication gates
and, by the geometric-series estimate valid for `q^2 < r`, at most `(1 + 6 r q^2) r^k` operations;
`padProgram` restricts the resulting `q^k × q^k` program to the `n × n` product without adding a
gate. -/
theorem exists_straightline_matrixProduct_of_rankLE (hq : 1 < q) (hqr : q * q < r)
    (hrank : RankLE r (matrixMultiplication (K := K) q q q)) (n : ℕ) :
    ∃ p : Straightline K (Fin n × Fin n) ((Fin n × Fin n) ⊕ (Fin n × Fin n)),
      (∀ (x y : Fin n × Fin n → K) (z : Fin n × Fin n),
          p.eval (Sum.elim x y) z = matrixProductMap (K := K) n n n x y z)
        ∧ p.mulOps ≤ r ^ Nat.clog q n
        ∧ p.totalOps ≤ (1 + 6 * (r * (q * q))) * r ^ Nat.clog q n := by
  obtain ⟨A, hA⟩ := (matrixMultiplication_rankLE_iff_exists_algorithm (K := K) q q q r).mp hrank
  refine ⟨padProgram (Nat.le_pow_clog hq n) (powProgram A (Nat.clog q n)), ?_, ?_, ?_⟩
  · intro x y z
    rw [matrixProductMap_apply]
    exact computesMatrixProduct_padProgram _ (computesMatrixProduct_powProgram A hA _) x y z
  · exact le_trans (mulOps_padProgram_le _ _) (le_of_eq (mulOps_powProgram A _))
  · exact le_trans (totalOps_padProgram_le _ _) (totalOps_powProgram_le A hqr _)

/-- **Polynomial form of the compilation bound.**  Under the same hypotheses, the compiled
program for the `n × n` product performs at most `C * n ^ (log r / log q)` arithmetic operations,
with the explicit constant `C = (1 + 6 * r * q^2) * r` depending only on the base algorithm.

Proof sketch: `r ^ ⌈log_q n⌉ ≤ r * n ^ (log r / log q)` (`real_pow_clog_le_mul_rpow`), so the
natural-number bound of `exists_straightline_matrixProduct_of_rankLE` becomes the displayed
polynomial bound after casting. -/
theorem exists_straightline_matrixProduct_rpow_of_rankLE (hq : 1 < q) (hqr : q * q < r)
    (hrank : RankLE r (matrixMultiplication (K := K) q q q)) {n : ℕ} (hn : 1 ≤ n) :
    ∃ p : Straightline K (Fin n × Fin n) ((Fin n × Fin n) ⊕ (Fin n × Fin n)),
      (∀ (x y : Fin n × Fin n → K) (z : Fin n × Fin n),
          p.eval (Sum.elim x y) z = matrixProductMap (K := K) n n n x y z)
        ∧ (p.totalOps : ℝ)
            ≤ (((1 + 6 * (r * (q * q))) * r : ℕ) : ℝ) *
                (n : ℝ) ^ (Real.log r / Real.log q) := by
  obtain ⟨p, hcomp, -, hops⟩ := exists_straightline_matrixProduct_of_rankLE hq hqr hrank n
  refine ⟨p, hcomp, ?_⟩
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by
    have : 1 ≤ r := by omega
    exact_mod_cast this
  have hcast : (p.totalOps : ℝ)
      ≤ ((1 + 6 * (r * (q * q)) : ℕ) : ℝ) * ((r : ℝ) ^ Nat.clog q n) := by
    have := (Nat.cast_le (α := ℝ)).mpr hops
    push_cast at this ⊢
    exact this
  have hclog : ((r : ℝ) ^ Nat.clog q n) ≤ (r : ℝ) * (n : ℝ) ^ (Real.log r / Real.log q) :=
    real_pow_clog_le_mul_rpow hq hr1 hn
  calc (p.totalOps : ℝ)
      ≤ ((1 + 6 * (r * (q * q)) : ℕ) : ℝ) * ((r : ℝ) ^ Nat.clog q n) := hcast
    _ ≤ ((1 + 6 * (r * (q * q)) : ℕ) : ℝ) *
          ((r : ℝ) * (n : ℝ) ^ (Real.log r / Real.log q)) := by
        refine mul_le_mul_of_nonneg_left hclog (by positivity)
    _ = (((1 + 6 * (r * (q * q))) * r : ℕ) : ℝ) *
          (n : ℝ) ^ (Real.log r / Real.log q) := by
        push_cast
        ring

/-- **Epsilon form.**  For every real exponent `τ` at or above `log r / log q` — in particular
for every `τ` strictly greater — the compiled family computes the `n × n` matrix product within
`C * n ^ τ` operations, with the same explicit constant. -/
theorem exists_straightline_matrixProduct_rpow_le_of_rankLE (hq : 1 < q) (hqr : q * q < r)
    (hrank : RankLE r (matrixMultiplication (K := K) q q q)) {τ : ℝ}
    (hτ : Real.log r / Real.log q ≤ τ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ p : Straightline K (Fin n × Fin n) ((Fin n × Fin n) ⊕ (Fin n × Fin n)),
      (∀ (x y : Fin n × Fin n → K) (z : Fin n × Fin n),
          p.eval (Sum.elim x y) z = matrixProductMap (K := K) n n n x y z)
        ∧ (p.totalOps : ℝ) ≤ (((1 + 6 * (r * (q * q))) * r : ℕ) : ℝ) * (n : ℝ) ^ τ := by
  obtain ⟨p, hcomp, hops⟩ := exists_straightline_matrixProduct_rpow_of_rankLE hq hqr hrank hn
  refine ⟨p, hcomp, hops.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact Real.rpow_le_rpow_of_exponent_le hn1 hτ

/-- **Proposition 2.7, forward direction.**  A rank-`r` algorithm for the `q × q` product with
`q^2 < r` bounds the matrix-multiplication exponent by `log r / log q` *and* produces an explicit
family of straight-line programs of arithmetic size `O(n ^ (log r / log q))` for the `n × n`
product.  The two halves are the tensor-level and the circuit-level readings of the same
certificate. -/
theorem omega_le_and_exists_straightline_of_rankLE (hq : 1 < q) (hqr : q * q < r)
    (hrank : RankLE r (matrixMultiplication (K := K) q q q)) :
    omega K ≤ Real.log r / Real.log q ∧
      ∀ n : ℕ, 1 ≤ n →
        ∃ p : Straightline K (Fin n × Fin n) ((Fin n × Fin n) ⊕ (Fin n × Fin n)),
          (∀ (x y : Fin n × Fin n → K) (z : Fin n × Fin n),
              p.eval (Sum.elim x y) z = matrixProductMap (K := K) n n n x y z)
            ∧ (p.totalOps : ℝ)
                ≤ (((1 + 6 * (r * (q * q))) * r : ℕ) : ℝ) *
                    (n : ℝ) ^ (Real.log r / Real.log q) :=
  ⟨omega_le_log_of_rankLE K hq (by omega) hrank,
    fun _ hn => exists_straightline_matrixProduct_rpow_of_rankLE hq hqr hrank hn⟩

end Headline

/-! ### The exponent-level statement over a field -/

section OmegaLevel

variable {F : Type u} [Field F]

/-- Every sufficiently large natural number `q` satisfies `B ≤ q ^ δ`, for a positive real
exponent `δ`.  The witness is `⌈max B 1 ^ δ⁻¹⌉₊`. -/
private theorem exists_nat_le_rpow {δ : ℝ} (hδ : 0 < δ) (B : ℝ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → B ≤ (q : ℝ) ^ δ := by
  refine ⟨⌈max B 1 ^ δ⁻¹⌉₊, fun q hq => ?_⟩
  have hB1 : (0 : ℝ) < max B 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have h1 : (max B 1) ^ δ⁻¹ ≤ (q : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hq)
  calc B ≤ max B 1 := le_max_left _ _
    _ = ((max B 1) ^ δ⁻¹) ^ δ := (Real.rpow_inv_rpow hB1.le hδ.ne').symm
    _ ≤ (q : ℝ) ^ δ := Real.rpow_le_rpow (by positivity) h1 hδ.le

/-- **Proposition 2.7, forward direction at the level of the exponent.**  Over a field, every
real exponent `τ` strictly above `ω` is an arithmetic-complexity exponent for matrix
multiplication: there is a constant `C` and, for every `n ≥ 1`, a straight-line program computing
the `n × n` matrix product with at most `C * n ^ τ` arithmetic operations.

Proof sketch: choose `σ` with `ω < σ < τ`.  The rank-growth definition of `ω` supplies a constant
`C₀` with `RankLE L ⟨q,q,q⟩` for every slot budget `L ≥ C₀ * q^σ`
(`exists_rankLE_under_slot_budget_of_omega_lt`).  Take `q` large enough that both
`C₀ + 1 ≤ q^(τ-σ)` and `2 ≤ q^(τ-2)` — possible because `σ < τ` and, over a field, `2 ≤ ω < τ` —
and set `L := max ⌈C₀ * q^σ⌉₊ (q^2 + 1)`.  Then `L` is a legitimate rank certificate for
`⟨q,q,q⟩` with `q^2 < L` and `L ≤ q^τ`, so `log L / log q ≤ τ` and the recursive compilation
`exists_straightline_matrixProduct_rpow_le_of_rankLE` applies with the explicit constant
`(1 + 6 * L * q^2) * L`.

The padding to `q^2 + 1` slots is what makes the block recursion, rather than the block
additions, dominate; it is harmless because `2 ≤ ω < τ` over a field. -/
theorem exists_straightline_matrixProduct_of_omega_lt {τ : ℝ} (hτ : omega F < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ p : Straightline F (Fin n × Fin n) ((Fin n × Fin n) ⊕ (Fin n × Fin n)),
        (∀ (x y : Fin n × Fin n → F) (z : Fin n × Fin n),
            p.eval (Sum.elim x y) z = matrixProductMap (K := F) n n n x y z)
          ∧ (p.totalOps : ℝ) ≤ C * (n : ℝ) ^ τ := by
  obtain ⟨σ, hωσ, hστ⟩ := exists_between hτ
  obtain ⟨C₀, hC₀, hslots⟩ := exists_rankLE_under_slot_budget_of_omega_lt F hωσ
  have hσ0 : 0 ≤ σ := le_trans (omega_nonneg F) hωσ.le
  have h2τ : (2 : ℝ) < τ := lt_of_le_of_lt (two_le_omega F) hτ
  have hδ : 0 < min (τ - σ) (τ - 2) := lt_min (by linarith) (by linarith)
  obtain ⟨q₀, hq₀⟩ := exists_nat_le_rpow hδ (max (C₀ + 1) 2)
  set q : ℕ := max 2 q₀ with hqdef
  have hq2 : 2 ≤ q := le_max_left _ _
  have hq1 : 1 < q := hq2
  have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hqR0 : (0 : ℝ) < (q : ℝ) := lt_trans zero_lt_one hqR
  have hbase := hq₀ q (le_max_right _ _)
  have hA : C₀ + 1 ≤ (q : ℝ) ^ (τ - σ) :=
    le_trans (le_trans (le_max_left _ _) hbase)
      (Real.rpow_le_rpow_of_exponent_le hqR.le (min_le_left _ _))
  have hB : (2 : ℝ) ≤ (q : ℝ) ^ (τ - 2) :=
    le_trans (le_trans (le_max_right _ _) hbase)
      (Real.rpow_le_rpow_of_exponent_le hqR.le (min_le_right _ _))
  set L : ℕ := max ⌈C₀ * (q : ℝ) ^ σ⌉₊ (q * q + 1) with hLdef
  have hslot : C₀ * (q : ℝ) ^ σ ≤ (L : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_left _ _)
  have hrank : Tensor.RankLE L (matrixMultiplication (K := F) q q q) :=
    hslots q L (by omega) hslot
  have hqL : q * q < L := by
    have hle := le_max_right ⌈C₀ * (q : ℝ) ^ σ⌉₊ (q * q + 1)
    omega
  have hqσ1 : (1 : ℝ) ≤ (q : ℝ) ^ σ := Real.one_le_rpow hqR.le hσ0
  have hceil : ((⌈C₀ * (q : ℝ) ^ σ⌉₊ : ℕ) : ℝ) ≤ (q : ℝ) ^ τ := by
    have h0 : (0 : ℝ) ≤ C₀ * (q : ℝ) ^ σ := by positivity
    have h1 : ((⌈C₀ * (q : ℝ) ^ σ⌉₊ : ℕ) : ℝ) ≤ C₀ * (q : ℝ) ^ σ + 1 :=
      (Nat.ceil_lt_add_one h0).le
    have h2 : C₀ * (q : ℝ) ^ σ + 1 ≤ (C₀ + 1) * (q : ℝ) ^ σ := by nlinarith
    have h3 : (C₀ + 1) * (q : ℝ) ^ σ ≤ (q : ℝ) ^ (τ - σ) * (q : ℝ) ^ σ :=
      mul_le_mul_of_nonneg_right hA (by positivity)
    have h4 : (q : ℝ) ^ (τ - σ) * (q : ℝ) ^ σ = (q : ℝ) ^ τ := by
      rw [← Real.rpow_add hqR0]
      ring_nf
    linarith
  have hsq : ((q * q + 1 : ℕ) : ℝ) ≤ (q : ℝ) ^ τ := by
    have hqq : (1 : ℝ) ≤ (q : ℝ) * (q : ℝ) := by nlinarith
    have h1 : ((q * q + 1 : ℕ) : ℝ) ≤ 2 * ((q : ℝ) * (q : ℝ)) := by push_cast; linarith
    have h2 : (2 : ℝ) * ((q : ℝ) * (q : ℝ)) ≤ (q : ℝ) ^ (τ - 2) * ((q : ℝ) * (q : ℝ)) :=
      mul_le_mul_of_nonneg_right hB (by positivity)
    have h3 : (q : ℝ) ^ (τ - 2) * ((q : ℝ) * (q : ℝ)) = (q : ℝ) ^ τ := by
      have hsquare : ((q : ℝ) * (q : ℝ)) = (q : ℝ) ^ (2 : ℝ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        ring
      rw [hsquare, ← Real.rpow_add hqR0]
      ring_nf
    linarith
  have hLq : (L : ℝ) ≤ (q : ℝ) ^ τ := by
    rw [hLdef]
    push_cast
    exact max_le hceil (by push_cast at hsq; exact hsq)
  have hlogle : Real.log L / Real.log q ≤ τ := by
    have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hqR
    rw [div_le_iff₀ hlogq]
    have hL0 : (0 : ℝ) < (L : ℝ) := by
      have : 0 < L := by omega
      exact_mod_cast this
    calc Real.log (L : ℝ) ≤ Real.log ((q : ℝ) ^ τ) := Real.log_le_log hL0 hLq
      _ = τ * Real.log (q : ℝ) := Real.log_rpow hqR0 τ
  refine ⟨(((1 + 6 * (L * (q * q))) * L : ℕ) : ℝ), ?_, fun n hn => ?_⟩
  · have hpos : 0 < (1 + 6 * (L * (q * q))) * L := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast hpos
  · exact exists_straightline_matrixProduct_rpow_le_of_rankLE hq1 hqL hrank hlogle hn

end OmegaLevel

/-! ### A tiny regression client -/

section CubicClient

variable {K : Type u} [CommSemiring K]

/-- The one-gate base program costs exactly one operation. -/
example : (baseProgram ℕ).totalOps = 1 := totalOps_baseProgram

/-- **Tiny end-to-end client.**  The defining eight-term decomposition of `⟨2,2,2⟩` compiles,
through the recursion, into programs for the `n × n` matrix product with at most `8 ^ ⌈log₂ n⌉`
multiplication gates and at most `193 * 8 ^ ⌈log₂ n⌉` operations: the classical cubic algorithm,
obtained from nothing but the definition of matrix multiplication.  It exercises the whole
pipeline — rank certificate, bilinear algorithm, block recursion, padding — on data that needs no
external input. -/
theorem exists_straightline_matrixProduct_cubic (n : ℕ) :
    ∃ p : Straightline K (Fin n × Fin n) ((Fin n × Fin n) ⊕ (Fin n × Fin n)),
      (∀ (x y : Fin n × Fin n → K) (z : Fin n × Fin n),
          p.eval (Sum.elim x y) z = matrixProductMap (K := K) n n n x y z)
        ∧ p.mulOps ≤ 8 ^ Nat.clog 2 n
        ∧ p.totalOps ≤ 193 * 8 ^ Nat.clog 2 n := by
  have hrank : Tensor.RankLE 8 (matrixMultiplication (K := K) 2 2 2) := by
    simpa using matrixMultiplication_rankLE (K := K) 2 2 2
  simpa using
    exists_straightline_matrixProduct_of_rankLE (K := K) (q := 2) (r := 8)
      (by norm_num) (by norm_num) hrank n

end CubicClient

end AlgebraicComplexity
