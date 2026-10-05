/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Fintype.Card

/-!
# Straight-line programs and the cost of bilinear algorithms

This module is the honest foundation for the arithmetic-complexity model of the
matrix-multiplication exponent (the ladder row "Proposition 2.7" of `DESIGN.md`).  It defines a
syntactic model of arithmetic computation over a coefficient type `K` and proves the one-step
compilation theorem: explicit length-`r` bilinear-algorithm data compiles to a straight-line
program that computes every output coordinate of the associated bilinear map simultaneously,
using exactly `r` nonscalar multiplications and a number of linear operations bounded linearly
in `r` and the three index-set sizes.

## Objects

* `AlgebraicComplexity.Circuit K ι`: arithmetic expression trees with input gates indexed by
  `ι`, scalar-constant gates, addition gates, general multiplication gates, and
  scalar-multiplication gates.  A `Circuit` is a formula: it has no shared subexpressions.
* `Circuit.eval`: evaluation of a circuit at an input assignment `ι → K`.
* Cost measures on circuits: `Circuit.linearOps` (addition and scalar-multiplication gates),
  `Circuit.mulOps` (general multiplication gates), `Circuit.totalOps` (their sum), and
  `Circuit.nonscalarMulsOn dep` (multiplication gates both of whose operands contain an input
  gate marked live by `dep : ι → Bool`).  `Circuit.nonscalarMuls` marks every input live.
* `Circuit.linearCombList` and `Circuit.linearComb`: the standard circuit for a linear form
  `∑ i, a i * x i`, built from `|ι|` scalar multiplications and `|ι| - 1` additions.
* `AlgebraicComplexity.Straightline K μ ι`: straight-line programs with inputs indexed by `ι`
  and output coordinates indexed by `μ`.  A program is either a family of output circuits
  (`Straightline.ret`), or a `let`-binding `Straightline.letBind c body` that computes the
  circuit `c` once, stores it in a fresh register, and continues with a program over the
  extended input type `Option ι` (`none` is the new register, `some i` the old inputs).  This
  is exactly the sharing that expression trees lack: a bound register may be referenced by many
  output coordinates while its gates are counted once.
* Program-level evaluation `Straightline.eval`, the cost measures `Straightline.linearOps`,
  `Straightline.mulOps`, `Straightline.totalOps`, `Straightline.nonscalarMulsOn`,
  `Straightline.nonscalarMuls`, and the structural combinators `Straightline.rename` and
  `Straightline.addSmul`.
* `AlgebraicComplexity.compileBilinearList` and `AlgebraicComplexity.compileBilinear`: the
  compiler from explicit bilinear-algorithm data — `r` triples of coefficient vectors
  `f t : ι → K`, `g t : κ → K`, `w t : μ → K` — to a straight-line program over inputs
  `ι ⊕ κ`.

## Principal results

* `eval_compileBilinear`: the compiled program computes every output coordinate
  `∑ t, w t m * ((∑ i, f t i * x i) * (∑ j, g t j * y j))` of the bilinear map described by
  the data.
* `mulOps_compileBilinear`: the program contains exactly `r` multiplication gates.
* `nonscalarMuls_compileBilinear`: when `ι` and `κ` are nonempty, all `r` of them are
  nonscalar; `nonscalarMuls_compileBilinear_le` gives the unconditional bound `≤ r`.
* `linearOps_compileBilinear`: the exact number
  `r * ((2 * |ι| - 1) + (2 * |κ| - 1) + 2 * |μ|)` of linear operations, with the rounder
  corollaries `linearOps_compileBilinear_le` and `totalOps_compileBilinear_le` of order
  `r * (|ι| + |κ| + |μ|)`.
* `exists_straightline_bilinear`: the packaged existential statement combining the three.

## Conventions

* **Costs count gates of a syntax tree.**  Every `add`, `mul`, and `smul` gate costs one
  operation; `input` and `const` gates are free.  A `Circuit` is a formula, so a shared
  subexpression written twice is paid for twice; genuine sharing is expressed by binding a
  register with `Straightline.letBind`, whose gates are counted once no matter how often the
  register is read.
* **Input dependence is syntactic.**  `Circuit.usesInputOn dep` is `true` iff the tree
  contains an `input i` gate with `dep i = true`.  A multiplication gate is *nonscalar* when
  both operands are input-dependent in this syntactic sense.  Syntactic dependence can only
  overcount semantic dependence, so a syntactic nonscalar-multiplication count of `r` is an
  honest upper-bound certificate for multiplicative complexity.  At the program level, a
  register bound by `letBind` is marked live exactly when its defining circuit is
  input-dependent, so reading a register that holds a genuinely input-dependent product is a
  nonscalar operand, while reading a register holding a constant is not.
* **`smul` is multiplication by a constant scalar.**  Semantically `Circuit.smul a p`
  evaluates like `Circuit.mul (Circuit.const a) p`, but it is a separate gate counted among the
  linear operations, matching the usual convention that scalar multiplications are linear
  operations while only `mul` gates can be nonscalar.  (A `mul` gate with a `const` operand is
  also never nonscalar, so the two encodings agree on the nonscalar count.)
* **Hypotheses are minimal.**  The syntax needs no algebraic structure (`Zero K` only where the
  empty linear combination is `const 0`); evaluation needs `Add K` and `Mul K`; list-level
  evaluation lemmas need `AddZeroClass K` and `Mul K`; only the `Finset`-summed public
  statements need `AddCommMonoid K` and `Mul K`.  The intended instantiation is a commutative
  semiring, and every statement here holds over one.

## Layer placement

This file is a leaf of the matrix-multiplication theory layer.  It imports only Mathlib — no
tensor-layer or combinatorics modules — and mentions no named construction and no numerical
bound.  It is the semantic-model half of the planned bilinear-algorithm bridge; the tensor side
(rank-`r` decompositions of the matrix-multiplication tensor as bilinear-algorithm data) can
consume `compileBilinear` without this file knowing about tensors.

## Deliberate non-goals (future work)

Per the named-proof-obligation policy of `DESIGN.md`, this module proves only the one-step
compilation.  The full Proposition 2.7 equivalence between the arithmetic-complexity definition
of `ω` and the rank-growth definition used in `MatrixMultiplication/Exponent.lean` is
deliberately **not** stated or represented here.  In particular the following remain future
work: recursive Strassen-style compilation of a rank-`r` algorithm for `⟨q,q,q⟩` into
`O(n^(log_q r + ε))`-operation programs for `n × n` matrix multiplication; the converse
direction extracting a bilinear algorithm (and hence a rank bound) from an arbitrary program
computing a bilinear map; and any statement connecting `Straightline` costs to
`matrixMultiplicationExponent`.  Nothing unproved is represented by a definition in this file.
-/

namespace AlgebraicComplexity

universe u v

/-! ### Arithmetic expression circuits -/

/-- An arithmetic expression circuit (a formula) over the coefficient type `K` with input gates
indexed by `ι`.  `input i` reads the `i`-th input, `const a` is the scalar constant `a`,
`add`/`mul` are binary gates, and `smul a p` multiplies the subcircuit `p` by the constant
scalar `a`.  No algebraic structure on `K` is required to form a circuit. -/
inductive Circuit (K : Type u) (ι : Type v) : Type (max u v) where
  /-- Read the input indexed by `i`. -/
  | input : ι → Circuit K ι
  /-- The constant scalar `a`; free of cost. -/
  | const : K → Circuit K ι
  /-- An addition gate. -/
  | add : Circuit K ι → Circuit K ι → Circuit K ι
  /-- A general multiplication gate; the only gate that can be nonscalar. -/
  | mul : Circuit K ι → Circuit K ι → Circuit K ι
  /-- A scalar-multiplication gate: multiplication by the constant `a`, counted as a linear
  operation. -/
  | smul : K → Circuit K ι → Circuit K ι

namespace Circuit

variable {K : Type u} {ι κ : Type v}

section Eval

variable [Add K] [Mul K]

/-- Evaluate a circuit at the input assignment `x : ι → K`.  Addition and multiplication gates
evaluate by `+` and `*`, and `smul a p` evaluates to `a * eval x p`. -/
def eval (x : ι → K) : Circuit K ι → K
  | input i => x i
  | const a => a
  | add p q => p.eval x + q.eval x
  | mul p q => p.eval x * q.eval x
  | smul a p => a * p.eval x

/-- Evaluation of an input gate. -/
@[simp] theorem eval_input (x : ι → K) (i : ι) : (input i : Circuit K ι).eval x = x i := rfl

/-- Evaluation of a constant gate. -/
@[simp] theorem eval_const (x : ι → K) (a : K) : (const a : Circuit K ι).eval x = a := rfl

/-- Evaluation of an addition gate. -/
@[simp] theorem eval_add (x : ι → K) (p q : Circuit K ι) :
    (add p q).eval x = p.eval x + q.eval x := rfl

/-- Evaluation of a multiplication gate. -/
@[simp] theorem eval_mul (x : ι → K) (p q : Circuit K ι) :
    (mul p q).eval x = p.eval x * q.eval x := rfl

/-- Evaluation of a scalar-multiplication gate. -/
@[simp] theorem eval_smul (x : ι → K) (a : K) (p : Circuit K ι) :
    (smul a p).eval x = a * p.eval x := rfl

end Eval

/-! #### Cost measures on circuits -/

/-- The number of linear operations in a circuit: its addition and scalar-multiplication
gates.  Input and constant gates are free. -/
def linearOps : Circuit K ι → ℕ
  | input _ => 0
  | const _ => 0
  | add p q => p.linearOps + q.linearOps + 1
  | mul p q => p.linearOps + q.linearOps
  | smul _ p => p.linearOps + 1

/-- Input gates cost no linear operation. -/
@[simp] theorem linearOps_input (i : ι) : (input i : Circuit K ι).linearOps = 0 := rfl

/-- Constant gates cost no linear operation. -/
@[simp] theorem linearOps_const (a : K) : (const a : Circuit K ι).linearOps = 0 := rfl

/-- An addition gate costs one linear operation plus those of its operands. -/
@[simp] theorem linearOps_add (p q : Circuit K ι) :
    (add p q).linearOps = p.linearOps + q.linearOps + 1 := rfl

/-- A multiplication gate costs no linear operation of its own. -/
@[simp] theorem linearOps_mul (p q : Circuit K ι) :
    (mul p q).linearOps = p.linearOps + q.linearOps := rfl

/-- A scalar-multiplication gate costs one linear operation plus those of its operand. -/
@[simp] theorem linearOps_smul (a : K) (p : Circuit K ι) :
    (smul a p).linearOps = p.linearOps + 1 := rfl

/-- The number of general multiplication gates in a circuit. -/
def mulOps : Circuit K ι → ℕ
  | input _ => 0
  | const _ => 0
  | add p q => p.mulOps + q.mulOps
  | mul p q => p.mulOps + q.mulOps + 1
  | smul _ p => p.mulOps

/-- Input gates are not multiplication gates. -/
@[simp] theorem mulOps_input (i : ι) : (input i : Circuit K ι).mulOps = 0 := rfl

/-- Constant gates are not multiplication gates. -/
@[simp] theorem mulOps_const (a : K) : (const a : Circuit K ι).mulOps = 0 := rfl

/-- Addition gates contribute no multiplication gate. -/
@[simp] theorem mulOps_add (p q : Circuit K ι) : (add p q).mulOps = p.mulOps + q.mulOps := rfl

/-- A multiplication gate counts once, plus those of its operands. -/
@[simp] theorem mulOps_mul (p q : Circuit K ι) :
    (mul p q).mulOps = p.mulOps + q.mulOps + 1 := rfl

/-- Scalar-multiplication gates are not general multiplication gates. -/
@[simp] theorem mulOps_smul (a : K) (p : Circuit K ι) : (smul a p).mulOps = p.mulOps := rfl

/-- The total number of costed operations in a circuit: linear operations plus general
multiplications. -/
def totalOps (c : Circuit K ι) : ℕ := c.linearOps + c.mulOps

/-- `totalOps` unfolded; the total operation count splits as linear operations plus general
multiplications. -/
theorem totalOps_eq (c : Circuit K ι) : c.totalOps = c.linearOps + c.mulOps := rfl

/-- `usesInputOn dep c` is `true` iff the circuit `c` contains an input gate `input i` with
`dep i = true`.  This is the *syntactic* input-dependence used to classify multiplication
gates as scalar or nonscalar; it can only overcount semantic dependence. -/
def usesInputOn (dep : ι → Bool) : Circuit K ι → Bool
  | input i => dep i
  | const _ => false
  | add p q => p.usesInputOn dep || q.usesInputOn dep
  | mul p q => p.usesInputOn dep || q.usesInputOn dep
  | smul _ p => p.usesInputOn dep

/-- An input gate is live exactly when its index is live. -/
@[simp] theorem usesInputOn_input (dep : ι → Bool) (i : ι) :
    (input i : Circuit K ι).usesInputOn dep = dep i := rfl

/-- Constant gates contain no input gate. -/
@[simp] theorem usesInputOn_const (dep : ι → Bool) (a : K) :
    (const a : Circuit K ι).usesInputOn dep = false := rfl

/-- An addition gate is input-dependent when either operand is. -/
@[simp] theorem usesInputOn_add (dep : ι → Bool) (p q : Circuit K ι) :
    (add p q).usesInputOn dep = (p.usesInputOn dep || q.usesInputOn dep) := rfl

/-- A multiplication gate is input-dependent when either operand is. -/
@[simp] theorem usesInputOn_mul (dep : ι → Bool) (p q : Circuit K ι) :
    (mul p q).usesInputOn dep = (p.usesInputOn dep || q.usesInputOn dep) := rfl

/-- A scalar-multiplication gate is input-dependent when its operand is. -/
@[simp] theorem usesInputOn_smul (dep : ι → Bool) (a : K) (p : Circuit K ι) :
    (smul a p).usesInputOn dep = p.usesInputOn dep := rfl

/-- `usesInput c` is `true` iff `c` contains any input gate. -/
def usesInput (c : Circuit K ι) : Bool := c.usesInputOn fun _ => true

/-- The number of *nonscalar* multiplication gates of a circuit relative to the liveness
predicate `dep`: multiplication gates both of whose operands contain a live input gate.
Additions and scalar multiplications are never nonscalar. -/
def nonscalarMulsOn (dep : ι → Bool) : Circuit K ι → ℕ
  | input _ => 0
  | const _ => 0
  | add p q => p.nonscalarMulsOn dep + q.nonscalarMulsOn dep
  | mul p q => p.nonscalarMulsOn dep + q.nonscalarMulsOn dep +
      (if p.usesInputOn dep && q.usesInputOn dep then 1 else 0)
  | smul _ p => p.nonscalarMulsOn dep

/-- Input gates contain no multiplication. -/
@[simp] theorem nonscalarMulsOn_input (dep : ι → Bool) (i : ι) :
    (input i : Circuit K ι).nonscalarMulsOn dep = 0 := rfl

/-- Constant gates contain no multiplication. -/
@[simp] theorem nonscalarMulsOn_const (dep : ι → Bool) (a : K) :
    (const a : Circuit K ι).nonscalarMulsOn dep = 0 := rfl

/-- Addition gates contribute no nonscalar multiplication of their own. -/
@[simp] theorem nonscalarMulsOn_add (dep : ι → Bool) (p q : Circuit K ι) :
    (add p q).nonscalarMulsOn dep = p.nonscalarMulsOn dep + q.nonscalarMulsOn dep := rfl

/-- A multiplication gate is nonscalar exactly when both operands are input-dependent. -/
@[simp] theorem nonscalarMulsOn_mul (dep : ι → Bool) (p q : Circuit K ι) :
    (mul p q).nonscalarMulsOn dep = p.nonscalarMulsOn dep + q.nonscalarMulsOn dep +
      (if p.usesInputOn dep && q.usesInputOn dep then 1 else 0) := rfl

/-- Scalar-multiplication gates contribute no nonscalar multiplication of their own. -/
@[simp] theorem nonscalarMulsOn_smul (dep : ι → Bool) (a : K) (p : Circuit K ι) :
    (smul a p).nonscalarMulsOn dep = p.nonscalarMulsOn dep := rfl

/-- The number of nonscalar multiplication gates of a circuit, with every input live. -/
def nonscalarMuls (c : Circuit K ι) : ℕ := c.nonscalarMulsOn fun _ => true

/-- Nonscalar multiplications are a subset of all multiplication gates: for every liveness
predicate, `nonscalarMulsOn dep c ≤ mulOps c`. -/
theorem nonscalarMulsOn_le_mulOps (dep : ι → Bool) (c : Circuit K ι) :
    c.nonscalarMulsOn dep ≤ c.mulOps := by
  induction c with
  | input i => simp
  | const a => simp
  | add p q hp hq => simpa using Nat.add_le_add hp hq
  | mul p q hp hq =>
      simp only [nonscalarMulsOn_mul, mulOps_mul]
      split <;> omega
  | smul a p hp => simpa using hp

/-! #### Renaming inputs -/

/-- Rename the inputs of a circuit along `e : ι → κ`.  Renaming is purely structural: it
preserves every gate and hence every cost measure, and evaluation after renaming is evaluation
at the pulled-back assignment (`eval_map`). -/
def map (e : ι → κ) : Circuit K ι → Circuit K κ
  | input i => input (e i)
  | const a => const a
  | add p q => add (p.map e) (q.map e)
  | mul p q => mul (p.map e) (q.map e)
  | smul a p => smul a (p.map e)

/-- Evaluating a renamed circuit is evaluating the original at the pulled-back assignment. -/
@[simp] theorem eval_map [Add K] [Mul K] (e : ι → κ) (x : κ → K) (c : Circuit K ι) :
    (c.map e).eval x = c.eval (x ∘ e) := by
  induction c with
  | input i => rfl
  | const a => rfl
  | add p q hp hq => simp [map, hp, hq]
  | mul p q hp hq => simp [map, hp, hq]
  | smul a p hp => simp [map, hp]

/-- Renaming preserves the linear-operation count. -/
@[simp] theorem linearOps_map (e : ι → κ) (c : Circuit K ι) :
    (c.map e).linearOps = c.linearOps := by
  induction c with
  | input i => rfl
  | const a => rfl
  | add p q hp hq => simp [map, hp, hq]
  | mul p q hp hq => simp [map, hp, hq]
  | smul a p hp => simp [map, hp]

/-- Renaming preserves the multiplication-gate count. -/
@[simp] theorem mulOps_map (e : ι → κ) (c : Circuit K ι) : (c.map e).mulOps = c.mulOps := by
  induction c with
  | input i => rfl
  | const a => rfl
  | add p q hp hq => simp [map, hp, hq]
  | mul p q hp hq => simp [map, hp, hq]
  | smul a p hp => simp [map, hp]

/-- Renamed circuits are input-dependent for `dep` exactly when the original is
input-dependent for the pulled-back liveness predicate `dep ∘ e`. -/
@[simp] theorem usesInputOn_map (e : ι → κ) (dep : κ → Bool) (c : Circuit K ι) :
    (c.map e).usesInputOn dep = c.usesInputOn (dep ∘ e) := by
  induction c with
  | input i => rfl
  | const a => rfl
  | add p q hp hq => simp [map, hp, hq]
  | mul p q hp hq => simp [map, hp, hq]
  | smul a p hp => simp [map, hp]

/-- Renaming preserves the nonscalar-multiplication count, after pulling the liveness
predicate back along the renaming. -/
@[simp] theorem nonscalarMulsOn_map (e : ι → κ) (dep : κ → Bool) (c : Circuit K ι) :
    (c.map e).nonscalarMulsOn dep = c.nonscalarMulsOn (dep ∘ e) := by
  induction c with
  | input i => rfl
  | const a => rfl
  | add p q hp hq => simp [map, hp, hq]
  | mul p q hp hq => simp [map, hp, hq]
  | smul a p hp => simp [map, hp]

/-! #### Linear-combination circuits -/

section LinearComb

variable [Zero K]

/-- The standard circuit for the linear form `∑ i ∈ l, a i * x i` over an explicit list `l` of
input indices: one scalar multiplication per index and one addition per index after the first,
so `|l|` scalar multiplications and `|l| - 1` additions in total.  The empty combination is the
constant `0`. -/
def linearCombList (a : ι → K) : List ι → Circuit K ι
  | [] => const 0
  | [i] => smul (a i) (input i)
  | i :: j :: l => add (smul (a i) (input i)) (linearCombList a (j :: l))

/-- The empty linear combination is the constant `0`. -/
@[simp] theorem linearCombList_nil (a : ι → K) : linearCombList a [] = (const 0 : Circuit K ι) :=
  rfl

/-- A single-index linear combination is one scalar multiplication of the input. -/
@[simp] theorem linearCombList_singleton (a : ι → K) (i : ι) :
    linearCombList a [i] = smul (a i) (input i) := rfl

/-- A linear combination over at least two indices peels off its first scalar multiple with one
addition. -/
@[simp] theorem linearCombList_cons_cons (a : ι → K) (i j : ι) (l : List ι) :
    linearCombList a (i :: j :: l) = add (smul (a i) (input i)) (linearCombList a (j :: l)) :=
  rfl

/-- The linear-combination circuit over a list of length `n` performs exactly `2 * n - 1`
linear operations (`n` scalar multiplications and `n - 1` additions; natural subtraction makes
the formula exact for `n = 0` as well). -/
theorem linearOps_linearCombList (a : ι → K) (l : List ι) :
    (linearCombList a l).linearOps = 2 * l.length - 1 := by
  induction l with
  | nil => simp
  | cons i l ih =>
      cases l with
      | nil => simp
      | cons j l =>
          simp only [linearCombList_cons_cons, linearOps_add, linearOps_smul, linearOps_input,
            List.length_cons] at ih ⊢
          omega

/-- The linear-combination circuit contains no general multiplication gate. -/
theorem mulOps_linearCombList (a : ι → K) (l : List ι) :
    (linearCombList a l).mulOps = 0 := by
  induction l with
  | nil => simp
  | cons i l ih =>
      cases l with
      | nil => simp
      | cons j l => simpa using ih

/-- The linear-combination circuit performs no nonscalar multiplication, for any liveness
predicate. -/
theorem nonscalarMulsOn_linearCombList (dep : ι → Bool) (a : ι → K) (l : List ι) :
    (linearCombList a l).nonscalarMulsOn dep = 0 := by
  induction l with
  | nil => simp
  | cons i l ih =>
      cases l with
      | nil => simp
      | cons j l => simpa using ih

/-- The linear-combination circuit over `l` contains a live input gate iff some index in `l`
is live. -/
theorem usesInputOn_linearCombList (dep : ι → Bool) (a : ι → K) (l : List ι) :
    (linearCombList a l).usesInputOn dep = l.any dep := by
  induction l with
  | nil => simp
  | cons i l ih =>
      cases l with
      | nil => simp
      | cons j l => simp [ih]

end LinearComb

/-- The linear-combination circuit over the list `l` evaluates to the list sum
`∑ i ∈ l, a i * x i`.  Stated for `AddZeroClass` and `Mul` only; the zero of the empty
combination is the additive zero. -/
theorem eval_linearCombList [AddZeroClass K] [Mul K] (a : ι → K) (l : List ι) (x : ι → K) :
    (linearCombList a l).eval x = (l.map fun i => a i * x i).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
      cases l with
      | nil => simp
      | cons j l => simp [ih]

section LinearCombFintype

variable [Zero K] [Fintype ι]

/-- The canonical linear-form circuit `∑ i, a i * x i` over a finite input type, obtained by
enumerating `Finset.univ`.  Noncomputable only because `Finset.toList` chooses an enumeration
order; every theorem about it is order-independent. -/
noncomputable def linearComb (a : ι → K) : Circuit K ι :=
  linearCombList a Finset.univ.toList

/-- The canonical linear-form circuit on `n = |ι|` inputs performs exactly `2 * n - 1` linear
operations: `n` scalar multiplications and `n - 1` additions. -/
theorem linearOps_linearComb (a : ι → K) :
    (linearComb a).linearOps = 2 * Fintype.card ι - 1 := by
  rw [linearComb, linearOps_linearCombList, Finset.length_toList, Finset.card_univ]

/-- The canonical linear-form circuit contains no general multiplication gate. -/
theorem mulOps_linearComb (a : ι → K) : (linearComb a).mulOps = 0 :=
  mulOps_linearCombList a _

/-- The canonical linear-form circuit on `n = |ι|` inputs performs `2 * n - 1` operations in
total. -/
theorem totalOps_linearComb (a : ι → K) :
    (linearComb a).totalOps = 2 * Fintype.card ι - 1 := by
  rw [totalOps_eq, linearOps_linearComb, mulOps_linearComb]
  omega

/-- The canonical linear-form circuit performs no nonscalar multiplication. -/
theorem nonscalarMulsOn_linearComb (dep : ι → Bool) (a : ι → K) :
    (linearComb a).nonscalarMulsOn dep = 0 :=
  nonscalarMulsOn_linearCombList dep a _

end LinearCombFintype

/-- The canonical linear-form circuit evaluates to the linear form `∑ i, a i * x i`. -/
@[simp] theorem eval_linearComb [AddCommMonoid K] [Mul K] [Fintype ι] (a : ι → K) (x : ι → K) :
    (linearComb a).eval x = ∑ i, a i * x i := by
  rw [linearComb, eval_linearCombList, Finset.sum_map_toList]

end Circuit

/-! ### Straight-line programs -/

/-- Extend an assignment on `α` by a value for one fresh register: the new register is `none`,
and the old names are reached through `some`. -/
def extendEnv {α : Type v} {β : Type*} (b : β) (x : α → β) : Option α → β
  | none => b
  | some a => x a

/-- The fresh register of an extended environment holds the new value. -/
@[simp] theorem extendEnv_none {α : Type v} {β : Type*} (b : β) (x : α → β) :
    extendEnv b x none = b := rfl

/-- Old names of an extended environment keep their values. -/
@[simp] theorem extendEnv_some {α : Type v} {β : Type*} (b : β) (x : α → β) (a : α) :
    extendEnv b x (some a) = x a := rfl

/-- Extending an environment and then restricting to the old names gives back the original
environment. -/
@[simp] theorem extendEnv_comp_some {α : Type v} {β : Type*} (b : β) (x : α → β) :
    extendEnv b x ∘ some = x := rfl

/-- A straight-line program over `K` with input registers indexed by `ι` and output
coordinates indexed by `μ`.  `ret out` returns one output circuit per coordinate;
`letBind c body` evaluates the circuit `c` **once**, binds the result to a fresh register, and
continues with `body`, whose input type `Option ι` has the new register at `none` and the old
inputs under `some`.  Because a bound register may be read many times while its defining
circuit is counted once, straight-line programs express the sharing that plain expression
trees cannot. -/
inductive Straightline (K : Type u) (μ : Type v) : Type v → Type (max u (v + 1)) where
  /-- Return one output circuit for each output coordinate. -/
  | ret {ι : Type v} (out : μ → Circuit K ι) : Straightline K μ ι
  /-- Compute `bound` once, store it in a fresh register (`none`), and continue. -/
  | letBind {ι : Type v} (bound : Circuit K ι) (body : Straightline K μ (Option ι)) :
      Straightline K μ ι

namespace Straightline

variable {K : Type u} {μ : Type v}

section Eval

variable [Add K] [Mul K]

/-- Evaluate a straight-line program at the input assignment `x`, producing the value of each
output coordinate.  A `letBind` evaluates its bound circuit once and extends the environment
with the resulting register value. -/
def eval : {ι : Type v} → Straightline K μ ι → (ι → K) → μ → K
  | _, .ret out, x, m => (out m).eval x
  | _, .letBind c body, x, m => body.eval (extendEnv (c.eval x) x) m

/-- Evaluation of a returning program. -/
@[simp] theorem eval_ret {ι : Type v} (out : μ → Circuit K ι) (x : ι → K) (m : μ) :
    (ret out).eval x m = (out m).eval x := rfl

/-- Evaluation of a `letBind`: bind the value of the bound circuit and continue. -/
@[simp] theorem eval_letBind {ι : Type v} (c : Circuit K ι)
    (body : Straightline K μ (Option ι)) (x : ι → K) (m : μ) :
    (letBind c body).eval x m = body.eval (extendEnv (c.eval x) x) m := rfl

end Eval

/-! #### Cost measures on programs -/

section Costs

variable [Fintype μ]

/-- The number of linear operations (addition and scalar-multiplication gates) in a program:
bound circuits are counted once each, and the output circuits of the final `ret` are summed
over all output coordinates. -/
def linearOps : {ι : Type v} → Straightline K μ ι → ℕ
  | _, .ret out => ∑ m, (out m).linearOps
  | _, .letBind c body => c.linearOps + linearOps body

/-- The linear operations of a returning program are summed over its output circuits. -/
@[simp] theorem linearOps_ret {ι : Type v} (out : μ → Circuit K ι) :
    (ret out : Straightline K μ ι).linearOps = ∑ m, (out m).linearOps := rfl

/-- A `letBind` pays for its bound circuit once. -/
@[simp] theorem linearOps_letBind {ι : Type v} (c : Circuit K ι)
    (body : Straightline K μ (Option ι)) :
    (letBind c body).linearOps = c.linearOps + body.linearOps := rfl

/-- The number of general multiplication gates in a program, with bound circuits counted
once. -/
def mulOps : {ι : Type v} → Straightline K μ ι → ℕ
  | _, .ret out => ∑ m, (out m).mulOps
  | _, .letBind c body => c.mulOps + mulOps body

/-- The multiplication gates of a returning program are summed over its output circuits. -/
@[simp] theorem mulOps_ret {ι : Type v} (out : μ → Circuit K ι) :
    (ret out : Straightline K μ ι).mulOps = ∑ m, (out m).mulOps := rfl

/-- A `letBind` pays for the multiplication gates of its bound circuit once. -/
@[simp] theorem mulOps_letBind {ι : Type v} (c : Circuit K ι)
    (body : Straightline K μ (Option ι)) :
    (letBind c body).mulOps = c.mulOps + body.mulOps := rfl

/-- The total number of costed operations in a program: linear operations plus general
multiplications. -/
def totalOps {ι : Type v} (p : Straightline K μ ι) : ℕ := p.linearOps + p.mulOps

/-- `totalOps` unfolded. -/
theorem totalOps_eq {ι : Type v} (p : Straightline K μ ι) :
    p.totalOps = p.linearOps + p.mulOps := rfl

/-- The number of nonscalar multiplication gates in a program, relative to a liveness
predicate on the current input registers.  Crossing a `letBind` extends the predicate: the new
register is live exactly when the bound circuit is input-dependent, so a register holding a
genuinely input-dependent value is a nonscalar operand while a register holding a constant is
not. -/
def nonscalarMulsOn : {ι : Type v} → (ι → Bool) → Straightline K μ ι → ℕ
  | _, dep, .ret out => ∑ m, (out m).nonscalarMulsOn dep
  | _, dep, .letBind c body =>
      c.nonscalarMulsOn dep + nonscalarMulsOn (extendEnv (c.usesInputOn dep) dep) body

/-- The nonscalar multiplications of a returning program are summed over its output
circuits. -/
@[simp] theorem nonscalarMulsOn_ret {ι : Type v} (dep : ι → Bool) (out : μ → Circuit K ι) :
    (ret out : Straightline K μ ι).nonscalarMulsOn dep = ∑ m, (out m).nonscalarMulsOn dep :=
  rfl

/-- Crossing a `letBind` counts the bound circuit once and marks the new register live exactly
when the bound circuit is input-dependent. -/
@[simp] theorem nonscalarMulsOn_letBind {ι : Type v} (dep : ι → Bool) (c : Circuit K ι)
    (body : Straightline K μ (Option ι)) :
    (letBind c body).nonscalarMulsOn dep =
      c.nonscalarMulsOn dep + body.nonscalarMulsOn (extendEnv (c.usesInputOn dep) dep) := rfl

/-- The number of nonscalar multiplication gates in a program, with every input live. -/
def nonscalarMuls {ι : Type v} (p : Straightline K μ ι) : ℕ :=
  p.nonscalarMulsOn fun _ => true

/-- Nonscalar multiplications are a subset of all multiplication gates of a program. -/
theorem nonscalarMulsOn_le_mulOps :
    ∀ {ι : Type v} (dep : ι → Bool) (p : Straightline K μ ι),
      p.nonscalarMulsOn dep ≤ p.mulOps
  | _, dep, .ret out =>
      Finset.sum_le_sum fun m _ => Circuit.nonscalarMulsOn_le_mulOps dep (out m)
  | _, dep, .letBind c body =>
      Nat.add_le_add (Circuit.nonscalarMulsOn_le_mulOps dep c)
        (nonscalarMulsOn_le_mulOps _ body)

end Costs

/-! #### Renaming program inputs -/

/-- Rename the inputs of a program along `e : ι → κ`, renaming every bound circuit and every
output circuit.  Registers introduced by `letBind` are untouched (`Option.map e`). -/
def rename : {ι κ : Type v} → (ι → κ) → Straightline K μ ι → Straightline K μ κ
  | _, _, e, .ret out => .ret fun m => (out m).map e
  | _, _, e, .letBind c body => .letBind (c.map e) (rename (Option.map e) body)

/-- Renaming a returning program renames each output circuit. -/
@[simp] theorem rename_ret {ι κ : Type v} (e : ι → κ) (out : μ → Circuit K ι) :
    (ret out : Straightline K μ ι).rename e = ret fun m => (out m).map e := rfl

/-- Renaming a `letBind` renames the bound circuit and continues under `Option.map`. -/
@[simp] theorem rename_letBind {ι κ : Type v} (e : ι → κ) (c : Circuit K ι)
    (body : Straightline K μ (Option ι)) :
    (letBind c body).rename e = letBind (c.map e) (body.rename (Option.map e)) := rfl

/-- Evaluating a renamed program is evaluating the original at the pulled-back assignment.

Proof sketch: structural induction on the program.  For a `letBind` the two environment
extensions agree register by register: the fresh register receives the same value because
renaming does not change the bound circuit's semantics (`Circuit.eval_map`), and old registers
are read through the renaming. -/
theorem eval_rename [Add K] [Mul K] :
    ∀ {ι κ : Type v} (e : ι → κ) (p : Straightline K μ ι) (x : κ → K) (m : μ),
      (p.rename e).eval x m = p.eval (x ∘ e) m
  | _, _, e, .ret out, x, m => by simp
  | _, _, e, .letBind c body, x, m => by
      have h : extendEnv ((c.map e).eval x) x ∘ Option.map e
          = extendEnv (c.eval (x ∘ e)) (x ∘ e) := by
        funext o
        cases o <;> simp
      simp only [rename_letBind, eval_letBind, eval_rename (Option.map e) body, ← h]

section RenameCosts

variable [Fintype μ]

/-- Renaming preserves the linear-operation count of a program. -/
@[simp] theorem linearOps_rename :
    ∀ {ι κ : Type v} (e : ι → κ) (p : Straightline K μ ι),
      (p.rename e).linearOps = p.linearOps
  | _, _, e, .ret out => by simp
  | _, _, e, .letBind c body => by
      simp [linearOps_rename (Option.map e) body]

/-- Renaming preserves the multiplication-gate count of a program. -/
@[simp] theorem mulOps_rename :
    ∀ {ι κ : Type v} (e : ι → κ) (p : Straightline K μ ι),
      (p.rename e).mulOps = p.mulOps
  | _, _, e, .ret out => by simp
  | _, _, e, .letBind c body => by
      simp [mulOps_rename (Option.map e) body]

/-- Renaming a program pulls the liveness predicate back along the renaming without changing
the nonscalar-multiplication count.

Proof sketch: structural induction; at a `letBind` the extended predicates agree because
`Circuit.usesInputOn_map` identifies the liveness of the renamed bound circuit with the
liveness of the original under the pulled-back predicate. -/
theorem nonscalarMulsOn_rename :
    ∀ {ι κ : Type v} (e : ι → κ) (dep : κ → Bool) (p : Straightline K μ ι),
      (p.rename e).nonscalarMulsOn dep = p.nonscalarMulsOn (dep ∘ e)
  | _, _, e, dep, .ret out => by simp
  | _, _, e, dep, .letBind c body => by
      have h : extendEnv ((c.map e).usesInputOn dep) dep ∘ Option.map e
          = extendEnv (c.usesInputOn (dep ∘ e)) (dep ∘ e) := by
        funext o
        cases o <;> simp
      simp only [rename_letBind, nonscalarMulsOn_letBind, Circuit.nonscalarMulsOn_map,
        nonscalarMulsOn_rename (Option.map e) _ body, h]

end RenameCosts

/-! #### Adding a scalar multiple of a register to every output -/

/-- Add the scalar multiple `w m * x a` of the register `a` to every output coordinate `m` of
a program, threading the register name through any intervening `letBind`s.  This costs one
scalar multiplication and one addition per output coordinate and no multiplication gates. -/
def addSmul (w : μ → K) : {ι : Type v} → ι → Straightline K μ ι → Straightline K μ ι
  | _, a, .ret out => .ret fun m => .add (.smul (w m) (.input a)) (out m)
  | _, a, .letBind c body => .letBind c (addSmul w (some a) body)

/-- `addSmul` on a returning program prepends one scalar multiple and one addition to each
output circuit. -/
@[simp] theorem addSmul_ret {ι : Type v} (w : μ → K) (a : ι) (out : μ → Circuit K ι) :
    (ret out : Straightline K μ ι).addSmul w a =
      ret fun m => .add (.smul (w m) (.input a)) (out m) := rfl

/-- `addSmul` passes through a `letBind`, following the register name under `some`. -/
@[simp] theorem addSmul_letBind {ι : Type v} (w : μ → K) (a : ι) (c : Circuit K ι)
    (body : Straightline K μ (Option ι)) :
    (letBind c body).addSmul w a = letBind c (body.addSmul w (some a)) := rfl

/-- `addSmul` adds `w m * x a` to the value of every output coordinate `m`. -/
theorem eval_addSmul [Add K] [Mul K] (w : μ → K) :
    ∀ {ι : Type v} (a : ι) (p : Straightline K μ ι) (x : ι → K) (m : μ),
      (p.addSmul w a).eval x m = w m * x a + p.eval x m
  | _, a, .ret out, x, m => by simp
  | _, a, .letBind c body, x, m => by
      simp [eval_addSmul w (some a) body]

section AddSmulCosts

variable [Fintype μ]

/-- `addSmul` costs exactly one scalar multiplication and one addition per output
coordinate. -/
theorem linearOps_addSmul (w : μ → K) :
    ∀ {ι : Type v} (a : ι) (p : Straightline K μ ι),
      (p.addSmul w a).linearOps = p.linearOps + 2 * Fintype.card μ
  | _, a, .ret out => by
      simp [Finset.sum_add_distrib, Finset.card_univ, Nat.mul_comm]
      omega
  | _, a, .letBind c body => by
      simp [linearOps_addSmul w (some a) body]
      omega

/-- `addSmul` introduces no multiplication gate. -/
theorem mulOps_addSmul (w : μ → K) :
    ∀ {ι : Type v} (a : ι) (p : Straightline K μ ι),
      (p.addSmul w a).mulOps = p.mulOps
  | _, a, .ret out => by simp
  | _, a, .letBind c body => by
      simp [mulOps_addSmul w (some a) body]

/-- `addSmul` introduces no nonscalar multiplication, for any liveness predicate. -/
theorem nonscalarMulsOn_addSmul (w : μ → K) :
    ∀ {ι : Type v} (a : ι) (dep : ι → Bool) (p : Straightline K μ ι),
      (p.addSmul w a).nonscalarMulsOn dep = p.nonscalarMulsOn dep
  | _, a, dep, .ret out => by simp
  | _, a, dep, .letBind c body => by
      simp [nonscalarMulsOn_addSmul w (some a) _ body]

end AddSmulCosts

end Straightline

/-! ### Compiling bilinear algorithms into straight-line programs -/

section Compile

variable {K : Type u} {ι κ μ : Type v}

/-- Compile explicit bilinear-algorithm data into a straight-line program over the inputs
`ι ⊕ κ` (`Sum.inl` the `x`-inputs, `Sum.inr` the `y`-inputs).  The data is a list of triples
`(f, g, w)`; for each triple the compiler binds one register to the product
`(∑ i ∈ lι, f i * x i) * (∑ j ∈ lκ, g j * y j)` of two linear forms — the unique
multiplication gate of that stage — and adds `w m` times that register to every output
coordinate `m`.  The enumeration lists `lι`, `lκ` of the two input index sets are explicit so
that the compiler itself stays computable; the `Fintype` wrapper `compileBilinear` fixes them
to `Finset.univ.toList`. -/
def compileBilinearList [Zero K] (lι : List ι) (lκ : List κ) :
    List ((ι → K) × (κ → K) × (μ → K)) → Straightline K μ (ι ⊕ κ)
  | [] => .ret fun _ => .const 0
  | ⟨f, g, w⟩ :: L =>
      .letBind
        (.mul ((Circuit.linearCombList f lι).map Sum.inl)
          ((Circuit.linearCombList g lκ).map Sum.inr))
        (((compileBilinearList lι lκ L).rename some).addSmul w none)

/-- The compiled program computes, at every output coordinate `m`, the sum over the algorithm's
triples of `w m` times the product of the two linear forms.

Proof sketch: induction on the list of triples.  Each stage binds the product register once;
`Straightline.eval_addSmul` accounts for the contribution `w m * register` to every output, and
`Straightline.eval_rename` plus `extendEnv_comp_some` shows the remaining stages evaluate in
the unextended environment, which is the induction hypothesis.  Only `AddZeroClass` and `Mul`
are needed because the statement mirrors the syntax tree exactly; no distributivity is used. -/
theorem eval_compileBilinearList [AddZeroClass K] [Mul K] (lι : List ι) (lκ : List κ)
    (L : List ((ι → K) × (κ → K) × (μ → K))) (env : ι ⊕ κ → K) (m : μ) :
    (compileBilinearList lι lκ L).eval env m
      = (L.map fun t => t.2.2 m *
          ((lι.map fun i => t.1 i * env (Sum.inl i)).sum *
            (lκ.map fun j => t.2.1 j * env (Sum.inr j)).sum)).sum := by
  induction L with
  | nil => simp [compileBilinearList]
  | cons t L ih =>
      obtain ⟨f, g, w⟩ := t
      simp [compileBilinearList, Straightline.eval_addSmul, Straightline.eval_rename,
        Circuit.eval_linearCombList, ih, Function.comp_def]

/-- Each triple of the bilinear-algorithm data contributes exactly one multiplication gate to
the compiled program. -/
theorem mulOps_compileBilinearList [Zero K] [Fintype μ] (lι : List ι) (lκ : List κ)
    (L : List ((ι → K) × (κ → K) × (μ → K))) :
    (compileBilinearList lι lκ L).mulOps = L.length := by
  induction L with
  | nil => simp [compileBilinearList]
  | cons t L ih =>
      obtain ⟨f, g, w⟩ := t
      simp [compileBilinearList, Straightline.mulOps_addSmul, Circuit.mulOps_linearCombList,
        ih]
      omega

/-- Exact linear-operation count of the compiled program: each of the `|L|` stages costs
`2 * |lι| - 1` linear operations for the left form, `2 * |lκ| - 1` for the right form, and
`2 * |μ|` for distributing the product register to the outputs (natural subtraction makes the
formula exact even for empty index lists). -/
theorem linearOps_compileBilinearList [Zero K] [Fintype μ] (lι : List ι) (lκ : List κ)
    (L : List ((ι → K) × (κ → K) × (μ → K))) :
    (compileBilinearList lι lκ L).linearOps
      = L.length * ((2 * lι.length - 1) + (2 * lκ.length - 1) + 2 * Fintype.card μ) := by
  induction L with
  | nil => simp [compileBilinearList]
  | cons t L ih =>
      obtain ⟨f, g, w⟩ := t
      simp only [compileBilinearList, Straightline.linearOps_letBind, Circuit.linearOps_mul,
        Circuit.linearOps_map, Circuit.linearOps_linearCombList,
        Straightline.linearOps_addSmul, Straightline.linearOps_rename, ih, List.length_cons,
        Nat.succ_mul]
      omega

/-- At most one nonscalar multiplication per stage: the compiled program performs at most
`|L|` nonscalar multiplications, for every liveness predicate. -/
theorem nonscalarMulsOn_compileBilinearList_le [Zero K] [Fintype μ] (lι : List ι)
    (lκ : List κ) (dep : ι ⊕ κ → Bool) (L : List ((ι → K) × (κ → K) × (μ → K))) :
    (compileBilinearList lι lκ L).nonscalarMulsOn dep ≤ L.length := by
  induction L with
  | nil => simp [compileBilinearList]
  | cons t L ih =>
      obtain ⟨f, g, w⟩ := t
      simp only [compileBilinearList, Straightline.nonscalarMulsOn_letBind,
        Circuit.nonscalarMulsOn_mul, Circuit.nonscalarMulsOn_map,
        Circuit.nonscalarMulsOn_linearCombList, Straightline.nonscalarMulsOn_addSmul,
        Straightline.nonscalarMulsOn_rename, extendEnv_comp_some, List.length_cons]
      split <;> omega

/-- A list is `any`-true for the constantly-true predicate as soon as it is nonempty.  Local
helper for the exact nonscalar count. -/
private theorem any_true_of_ne_nil {α : Type*} {l : List α} (h : l ≠ []) :
    l.any (fun _ => true) = true := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l => simp

/-- Exact nonscalar-multiplication count of the compiled program: when both enumeration lists
are nonempty, each stage's product of two genuinely input-dependent linear forms is nonscalar,
so the program performs exactly `|L|` nonscalar multiplications.

Proof sketch: induction on the triples.  The bound circuit of a stage is a `mul` gate whose
operands are linear forms containing input gates from `lι` and `lκ` respectively, so with every
input live the gate counts once; the register-liveness extension disappears when restricted to
the surviving stages because `extendEnv b dep ∘ some = dep`. -/
theorem nonscalarMuls_compileBilinearList [Zero K] [Fintype μ] {lι : List ι} {lκ : List κ}
    (hι : lι ≠ []) (hκ : lκ ≠ []) (L : List ((ι → K) × (κ → K) × (μ → K))) :
    (compileBilinearList lι lκ L).nonscalarMuls = L.length := by
  induction L with
  | nil => simp [compileBilinearList, Straightline.nonscalarMuls]
  | cons t L ih =>
      obtain ⟨f, g, w⟩ := t
      have h1 : lι.any (fun _ => true) = true := any_true_of_ne_nil hι
      have h2 : lκ.any (fun _ => true) = true := any_true_of_ne_nil hκ
      simp only [Straightline.nonscalarMuls, compileBilinearList,
        Straightline.nonscalarMulsOn_letBind, Circuit.nonscalarMulsOn_mul,
        Circuit.nonscalarMulsOn_map, Circuit.nonscalarMulsOn_linearCombList,
        Circuit.usesInputOn_map, Circuit.usesInputOn_linearCombList,
        Straightline.nonscalarMulsOn_addSmul, Straightline.nonscalarMulsOn_rename,
        List.length_cons, Function.comp_def] at ih ⊢
      simp [h1, h2, ih]
      omega

end Compile

/-! ### The one-step compilation theorem over finite index types -/

section CompileFintype

variable {K : Type u} {ι κ μ : Type v} [Fintype ι] [Fintype κ] [Fintype μ]

/-- Compile length-`r` bilinear-algorithm data — coefficient families `f t : ι → K`,
`g t : κ → K` and output vectors `w t : μ → K` for `t : Fin r` — into a straight-line program
over the inputs `ι ⊕ κ`.  The program binds one register per `t` to the product
`(∑ i, f t i * x i) * (∑ j, g t j * y j)` and accumulates `∑ t, w t m * register t` into each
output coordinate `m`.  Noncomputable only through the choice of enumeration order of the
finite index sets. -/
noncomputable def compileBilinear [Zero K] (r : ℕ) (f : Fin r → ι → K) (g : Fin r → κ → K)
    (w : Fin r → μ → K) : Straightline K μ (ι ⊕ κ) :=
  compileBilinearList Finset.univ.toList Finset.univ.toList
    ((List.finRange r).map fun t => (f t, g t, w t))

omit [Fintype μ] in
/-- **Correctness of the one-step compilation.**  On the input assignment splitting as
`x : ι → K` and `y : κ → K`, every output coordinate `m` of the compiled program evaluates to
the bilinear map determined by the algorithm data:
`∑ t, w t m * ((∑ i, f t i * x i) * (∑ j, g t j * y j))`.

Proof sketch: `eval_compileBilinearList` computes the value as a list sum over the `r`
compiled stages; converting the enumeration lists back to `Finset` sums
(`Finset.sum_map_toList`, `Fin.sum_univ_def`) yields the displayed bilinear expression. -/
theorem eval_compileBilinear [AddCommMonoid K] [Mul K] (r : ℕ) (f : Fin r → ι → K)
    (g : Fin r → κ → K) (w : Fin r → μ → K) (x : ι → K) (y : κ → K) (m : μ) :
    (compileBilinear r f g w).eval (Sum.elim x y) m
      = ∑ t, w t m * ((∑ i, f t i * x i) * (∑ j, g t j * y j)) := by
  rw [compileBilinear, eval_compileBilinearList, List.map_map]
  conv_rhs => rw [Fin.sum_univ_def]
  simp [Function.comp_def]

/-- The compiled program contains exactly `r` multiplication gates, one per triple of the
algorithm data. -/
theorem mulOps_compileBilinear [Zero K] (r : ℕ) (f : Fin r → ι → K) (g : Fin r → κ → K)
    (w : Fin r → μ → K) : (compileBilinear r f g w).mulOps = r := by
  simp [compileBilinear, mulOps_compileBilinearList]

/-- Exact linear-operation count of the compiled program:
`r * ((2 * |ι| - 1) + (2 * |κ| - 1) + 2 * |μ|)` — per multiplication, two full linear forms
and one scalar-multiple-accumulate into each output coordinate. -/
theorem linearOps_compileBilinear [Zero K] (r : ℕ) (f : Fin r → ι → K) (g : Fin r → κ → K)
    (w : Fin r → μ → K) :
    (compileBilinear r f g w).linearOps
      = r * ((2 * Fintype.card ι - 1) + (2 * Fintype.card κ - 1) + 2 * Fintype.card μ) := by
  simp [compileBilinear, linearOps_compileBilinearList, Finset.length_toList,
    Finset.card_univ]

/-- Rounded form of the linear-operation count: at most
`2 * r * (|ι| + |κ| + |μ|)` linear operations. -/
theorem linearOps_compileBilinear_le [Zero K] (r : ℕ) (f : Fin r → ι → K)
    (g : Fin r → κ → K) (w : Fin r → μ → K) :
    (compileBilinear r f g w).linearOps
      ≤ 2 * r * (Fintype.card ι + Fintype.card κ + Fintype.card μ) := by
  rw [linearOps_compileBilinear]
  calc r * ((2 * Fintype.card ι - 1) + (2 * Fintype.card κ - 1) + 2 * Fintype.card μ)
      ≤ r * (2 * (Fintype.card ι + Fintype.card κ + Fintype.card μ)) :=
        Nat.mul_le_mul le_rfl (by omega)
    _ = 2 * r * (Fintype.card ι + Fintype.card κ + Fintype.card μ) := by
        rw [Nat.mul_left_comm, ← Nat.mul_assoc]

/-- Total-operation bound for the compiled program: at most
`r * (2 * (|ι| + |κ| + |μ|) + 1)` operations, of which exactly `r` are multiplications. -/
theorem totalOps_compileBilinear_le [Zero K] (r : ℕ) (f : Fin r → ι → K) (g : Fin r → κ → K)
    (w : Fin r → μ → K) :
    (compileBilinear r f g w).totalOps
      ≤ r * (2 * (Fintype.card ι + Fintype.card κ + Fintype.card μ) + 1) := by
  rw [Straightline.totalOps_eq, mulOps_compileBilinear, Nat.mul_add, Nat.mul_one]
  refine Nat.add_le_add_right ?_ r
  calc (compileBilinear r f g w).linearOps
      ≤ 2 * r * (Fintype.card ι + Fintype.card κ + Fintype.card μ) :=
        linearOps_compileBilinear_le r f g w
    _ = r * (2 * (Fintype.card ι + Fintype.card κ + Fintype.card μ)) := by
        rw [Nat.mul_comm 2 r, Nat.mul_assoc]

/-- The compiled program performs at most `r` nonscalar multiplications, with no hypothesis on
the index types. -/
theorem nonscalarMuls_compileBilinear_le [Zero K] (r : ℕ) (f : Fin r → ι → K)
    (g : Fin r → κ → K) (w : Fin r → μ → K) :
    (compileBilinear r f g w).nonscalarMuls ≤ r := by
  have h := nonscalarMulsOn_compileBilinearList_le (Finset.univ.toList (α := ι))
    (Finset.univ.toList (α := κ)) (fun _ => true)
    ((List.finRange r).map fun t => (f t, g t, w t))
  simpa [compileBilinear, Straightline.nonscalarMuls] using h

/-- **Exact nonscalar-multiplication count.**  When both input index types are nonempty, the
compiled program performs exactly `r` nonscalar multiplications: each bound register is a
product of two linear forms that genuinely contain input gates. -/
theorem nonscalarMuls_compileBilinear [Zero K] [Nonempty ι] [Nonempty κ] (r : ℕ)
    (f : Fin r → ι → K) (g : Fin r → κ → K) (w : Fin r → μ → K) :
    (compileBilinear r f g w).nonscalarMuls = r := by
  have hι : (Finset.univ : Finset ι).toList ≠ [] := Finset.univ_nonempty.toList_ne_nil
  have hκ : (Finset.univ : Finset κ).toList ≠ [] := Finset.univ_nonempty.toList_ne_nil
  rw [compileBilinear, nonscalarMuls_compileBilinearList hι hκ]
  simp

/-- **One-step compilation of a bilinear algorithm, packaged.**  Length-`r` bilinear-algorithm
data over finite index types yields a straight-line program on the inputs `ι ⊕ κ` that
computes every output coordinate of the associated bilinear map simultaneously, using at most
`r` nonscalar multiplications and at most `r * (2 * (|ι| + |κ| + |μ|) + 1)` operations in
total.

Proof sketch: the witness is `compileBilinear r f g w`; correctness is
`eval_compileBilinear`, and the two cost bounds are `nonscalarMuls_compileBilinear_le` and
`totalOps_compileBilinear_le`.  Under `Nonempty ι` and `Nonempty κ` the nonscalar count is
exactly `r` (`nonscalarMuls_compileBilinear`). -/
theorem exists_straightline_bilinear [AddCommMonoid K] [Mul K] (r : ℕ) (f : Fin r → ι → K)
    (g : Fin r → κ → K) (w : Fin r → μ → K) :
    ∃ p : Straightline K μ (ι ⊕ κ),
      (∀ (x : ι → K) (y : κ → K) (m : μ),
          p.eval (Sum.elim x y) m
            = ∑ t, w t m * ((∑ i, f t i * x i) * (∑ j, g t j * y j)))
        ∧ p.nonscalarMuls ≤ r
        ∧ p.totalOps ≤ r * (2 * (Fintype.card ι + Fintype.card κ + Fintype.card μ) + 1) :=
  ⟨compileBilinear r f g w, eval_compileBilinear r f g w,
    nonscalarMuls_compileBilinear_le r f g w, totalOps_compileBilinear_le r f g w⟩

end CompileFintype

/-! ### Tiny regression examples

Deliberately small closed instances guarding the gate-count and dependence conventions, in the
spirit of the design contract's tiny-client policy. -/

section Examples

/-- A product of two inputs is one nonscalar multiplication. -/
example : (Circuit.mul (.input true) (.input false) : Circuit ℕ Bool).nonscalarMuls = 1 := rfl

/-- A scalar multiple of an input is not a nonscalar multiplication. -/
example : (Circuit.smul 3 (.input ()) : Circuit ℕ Unit).nonscalarMuls = 0 := rfl

/-- A product with a constant operand is a multiplication gate but not a nonscalar one. -/
example : (Circuit.mul (.const 3) (.input ()) : Circuit ℕ Unit).nonscalarMuls = 0 := rfl

/-- A product with a constant operand still counts as a multiplication gate. -/
example : (Circuit.mul (.const 3) (.input ()) : Circuit ℕ Unit).mulOps = 1 := rfl

/-- Evaluation of a small circuit: `x true * x false` at `x = (2, 3)`. -/
example : (Circuit.mul (.input true) (.input false) : Circuit ℕ Bool).eval
    (fun b => cond b 2 3) = 6 := rfl

/-- A one-register straight-line program computing `x true * x false` through a bound
register. -/
example :
    (Straightline.letBind (Circuit.mul (.input true) (.input false))
        (Straightline.ret fun _ : Unit => .input none) : Straightline ℕ Unit Bool).eval
      (fun b => cond b 2 3) () = 6 := rfl

/-- The register read in the previous program is live, but reading it multiplies nothing, so
the program has exactly the one nonscalar multiplication of its bound circuit. -/
example :
    (Straightline.letBind (Circuit.mul (.input true) (.input false))
        (Straightline.ret fun _ : Unit => .input none) : Straightline ℕ Unit Bool).nonscalarMuls
      = 1 := by
  simp [Straightline.nonscalarMuls]

end Examples

end AlgebraicComplexity
