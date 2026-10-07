/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.BilinearAlgorithm
import AlgebraicComplexity.MatrixMultiplication.Exponent
import AlgebraicComplexity.MatrixMultiplication.RankComplexityRecursion
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Straight-line programs bound tensor rank

`MatrixMultiplication/RankComplexity.lean` and `RankComplexityRecursion.lean` prove the forward
direction of Proposition 2.7 of the Cornell CS 6810 notes: a rank certificate compiles to
straight-line programs, and `ω < τ` yields programs of size `O(n^τ)` for the `n × n` product.
This file proves the **converse**, which is Strassen's observation that multiplications are all
that matter:

> a straight-line program with `M` multiplication gates that computes a bilinear map over an
> infinite field yields a bilinear algorithm of length at most `2M` for it.

Hence `R(⟨m,n,p⟩) ≤ 2 · (number of multiplication gates)` for every program computing the
`m × n` by `n × p` matrix product, and a family of programs of size `O(n^τ)` forces `ω ≤ τ`.
Together with the forward direction this is the full equivalence: over an infinite field, the
rank-growth exponent `omega` *is* the exponent of arithmetic complexity
(`omega_le_iff_exists_straightline`).

## Proof

The argument keeps, for every register of the program, only the part of the polynomial it
computes that has degree at most one in the `x`-inputs and at most one in the `y`-inputs:

```text
c  +  ∑ᵢ ℓᵢ xᵢ  +  ∑ⱼ ℓ'ⱼ yⱼ  +  ∑ᵢⱼ βᵢⱼ xᵢ yⱼ.
```

These truncations form a commutative ring, `Trunc K ι κ`, in which products of two `x`-variables
or of two `y`-variables vanish.  It is not built by hand: it is the trivial square-zero extension
of the trivial square-zero extension `K ⊕ (ι → K)` by `κ` copies of itself, so Mathlib supplies
the ring structure.  Its multiplication law for the bilinear part is

```text
β(t · u) = c(t) β(u) + c(u) β(t) + ℓ(t) ⊗ ℓ'(u) + ℓ(u) ⊗ ℓ'(t)        (`Trunc.bil_mul`),
```

so each multiplication gate adds at most **two** rank-one matrices to the span in which the
bilinear parts of all registers live, while additions and scalar multiplications add none
(`Circuit.exists_bilSpan`, `Straightline.exists_bilSpan`).  A program with `M` multiplication
gates therefore has all its output bilinear parts in the span of at most `2M` rank-one matrices,
which is a bilinear algorithm of length at most `2M`.

What links the program's behaviour on points of `K` to its value in `Trunc` is the polynomial
ring: evaluating the program on the variables of `MvPolynomial (ι ⊕ κ) K` gives a polynomial that
agrees with the bilinear map at every point, hence equals it when `K` is an infinite field
(`MvPolynomial.funext`), and the truncation is a ring homomorphism out of the polynomial ring.
All three evaluations are instances of one naturality lemma, `Straightline.eval_mapCoeff`.

## Main results

* `Circuit.mapCoeff`, `Straightline.mapCoeff`, `Straightline.eval_mapCoeff`: change of the
  coefficient ring of a program, and naturality of evaluation.
* `Trunc`, `Trunc.bil_mul`: the truncated algebra and its product rule.
* `Straightline.exists_bilSpan`: the structure theorem — `2 · mulOps` rank-one matrices span
  every output's bilinear part.
* `exists_bilinearAlgorithm_of_straightline`: a program computing a bilinear map over an infinite
  field gives a bilinear algorithm of length at most `2 · mulOps`.
* `rankLE_matrixMultiplication_of_straightline`: `R(⟨m,n,p⟩) ≤ 2 · mulOps`.
* `omega_le_of_straightline`: programs with `O(n^τ)` multiplication gates force `ω ≤ τ`.
* `omega_le_iff_exists_straightline`: **Proposition 2.7** as an equivalence.

## Scope

* **Infinite fields.**  The hypothesis is that the program computes the map *as a function* on
  `K`-points.  Over a finite field that is strictly weaker than a polynomial identity (`x² = x`
  on `𝔽₂`), and the structure theorem needs the identity.  The constant `2` is the classical
  one; it is not claimed to be optimal.
* **All multiplication gates are counted**, scalar or not: `mulOps`, not `nonscalarMuls`.  The
  bound with nonscalar multiplications only is true and is not proved here.
* Division gates do not exist in this model; Strassen's elimination of divisions is not
  formalized.

## References

* V. Strassen, *Vermeidung von Divisionen*, J. reine angew. Math. 264 (1973).
* He and Williams, Cornell CS 6810 matrix-multiplication notes, Proposition 2.7.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

/-! ### Changing the coefficient type of a program -/

namespace Circuit

variable {K : Type u} {A : Type w} {ι : Type v}

/-- Apply a map to every constant of a circuit. -/
def mapCoeff (φ : K → A) : Circuit K ι → Circuit A ι
  | input i => input i
  | const a => const (φ a)
  | add p q => add (p.mapCoeff φ) (q.mapCoeff φ)
  | mul p q => mul (p.mapCoeff φ) (q.mapCoeff φ)
  | smul a p => smul (φ a) (p.mapCoeff φ)

/-- Changing coefficients does not change the number of multiplication gates. -/
@[simp] theorem mulOps_mapCoeff (φ : K → A) (c : Circuit K ι) :
    (c.mapCoeff φ).mulOps = c.mulOps := by
  induction c with
  | input i => rfl
  | const a => rfl
  | add p q hp hq => simp [mapCoeff, hp, hq]
  | mul p q hp hq => simp [mapCoeff, hp, hq]
  | smul a p hp => simp [mapCoeff, hp]

/-- Changing coefficients twice is changing them once along the composite. -/
theorem mapCoeff_mapCoeff {B : Type*} (φ : K → A) (ψ : A → B) (c : Circuit K ι) :
    (c.mapCoeff φ).mapCoeff ψ = c.mapCoeff fun a ↦ ψ (φ a) := by
  induction c with
  | input i => rfl
  | const a => rfl
  | add p q hp hq => simp [mapCoeff, hp, hq]
  | mul p q hp hq => simp [mapCoeff, hp, hq]
  | smul a p hp => simp [mapCoeff, hp]

/-- Changing coefficients along the identity does nothing. -/
theorem mapCoeff_id (c : Circuit K ι) : c.mapCoeff (fun a ↦ a) = c := by
  induction c with
  | input i => rfl
  | const a => rfl
  | add p q hp hq => simp [mapCoeff, hp, hq]
  | mul p q hp hq => simp [mapCoeff, hp, hq]
  | smul a p hp => simp [mapCoeff, hp]

/-- **Naturality of circuit evaluation.**  A map that preserves `+` and `*` commutes with
evaluation. -/
theorem eval_mapCoeff [Add K] [Mul K] [Add A] [Mul A] (φ : K → A)
    (hadd : ∀ a b, φ (a + b) = φ a + φ b) (hmul : ∀ a b, φ (a * b) = φ a * φ b)
    (c : Circuit K ι) (x : ι → K) :
    (c.mapCoeff φ).eval (fun i ↦ φ (x i)) = φ (c.eval x) := by
  induction c with
  | input i => rfl
  | const a => rfl
  | add p q hp hq => simp [mapCoeff, hp, hq, hadd]
  | mul p q hp hq => simp [mapCoeff, hp, hq, hmul]
  | smul a p hp => simp [mapCoeff, hp, hmul]

end Circuit

namespace Straightline

variable {K : Type u} {A : Type w} {μ : Type v}

/-- Apply a map to every constant of a straight-line program. -/
def mapCoeff (φ : K → A) : {ι : Type v} → Straightline K μ ι → Straightline A μ ι
  | _, .ret out => .ret fun m ↦ (out m).mapCoeff φ
  | _, .letBind c body => .letBind (c.mapCoeff φ) (mapCoeff φ body)

/-- Changing coefficients does not change the number of multiplication gates. -/
@[simp] theorem mulOps_mapCoeff [Fintype μ] (φ : K → A) {ι : Type v}
    (p : Straightline K μ ι) : (p.mapCoeff φ).mulOps = p.mulOps := by
  induction p with
  | ret out => simp [mapCoeff]
  | letBind c body ih => simp [mapCoeff, ih]

/-- Changing coefficients twice is changing them once along the composite. -/
theorem mapCoeff_mapCoeff {B : Type*} (φ : K → A) (ψ : A → B) {ι : Type v}
    (p : Straightline K μ ι) :
    (p.mapCoeff φ).mapCoeff ψ = p.mapCoeff fun a ↦ ψ (φ a) := by
  induction p with
  | ret out => simp [mapCoeff, Circuit.mapCoeff_mapCoeff]
  | letBind c body ih => simp [mapCoeff, Circuit.mapCoeff_mapCoeff, ih]

/-- Changing coefficients along the identity does nothing. -/
theorem mapCoeff_id {ι : Type v} (p : Straightline K μ ι) : p.mapCoeff (fun a ↦ a) = p := by
  induction p with
  | ret out => simp [mapCoeff, Circuit.mapCoeff_id]
  | letBind c body ih => simp [mapCoeff, Circuit.mapCoeff_id, ih]

/-- **Naturality of program evaluation.**  A map that preserves `+` and `*` commutes with
evaluation of a straight-line program. -/
theorem eval_mapCoeff [Add K] [Mul K] [Add A] [Mul A] (φ : K → A)
    (hadd : ∀ a b, φ (a + b) = φ a + φ b) (hmul : ∀ a b, φ (a * b) = φ a * φ b)
    {ι : Type v} (p : Straightline K μ ι) (x : ι → K) (m : μ) :
    (p.mapCoeff φ).eval (fun i ↦ φ (x i)) m = φ (p.eval x m) := by
  induction p with
  | ret out => simp [mapCoeff, Circuit.eval_mapCoeff φ hadd hmul]
  | letBind c body ih =>
      simp only [mapCoeff, eval_letBind]
      rw [Circuit.eval_mapCoeff φ hadd hmul]
      have h : extendEnv (φ (c.eval x)) (fun i ↦ φ (x i)) =
          fun o ↦ φ (extendEnv (c.eval x) x o) := by
        funext o
        cases o <;> rfl
      rw [h]
      exact ih _

end Straightline

/-! ### The truncated algebra -/

section Truncation

variable (K : Type u) [CommRing K] (ι κ : Type v)

/-- Polynomials in the `x`-variables truncated at degree one: `K ⊕ (ι → K)`, with the product
of two `x`-variables equal to zero. -/
abbrev TruncX := TrivSqZeroExt K (ι → K)

/-- Polynomials in the `x`- and `y`-variables truncated at degree one in each family:
`c + ∑ ℓᵢ xᵢ + ∑ ℓ'ⱼ yⱼ + ∑ βᵢⱼ xᵢ yⱼ`.  As a ring it is the trivial square-zero extension of
`TruncX K ι` by `κ` copies of itself, the `j`-th copy holding `ℓ'ⱼ + ∑ᵢ βᵢⱼ xᵢ`. -/
abbrev Trunc := TrivSqZeroExt (TruncX K ι) (κ → TruncX K ι)

end Truncation

namespace Trunc

variable {K : Type u} [CommRing K] {ι κ : Type v}

/-- The constant term. -/
def const (t : Trunc K ι κ) : K := t.fst.fst

/-- The coefficient of `xᵢ`. -/
def linX (t : Trunc K ι κ) (i : ι) : K := t.fst.snd i

/-- The coefficient of `yⱼ`. -/
def linY (t : Trunc K ι κ) (j : κ) : K := (t.snd j).fst

/-- The coefficient of `xᵢ yⱼ`: the bilinear part, as a matrix. -/
def bil (t : Trunc K ι κ) (i : ι) (j : κ) : K := (t.snd j).snd i

@[simp] theorem const_add (t u : Trunc K ι κ) : (t + u).const = t.const + u.const := rfl

@[simp] theorem linX_add (t u : Trunc K ι κ) (i : ι) :
    (t + u).linX i = t.linX i + u.linX i := rfl

@[simp] theorem linY_add (t u : Trunc K ι κ) (j : κ) :
    (t + u).linY j = t.linY j + u.linY j := rfl

@[simp] theorem bil_add (t u : Trunc K ι κ) : (t + u).bil = t.bil + u.bil := rfl

@[simp] theorem bil_zero : (0 : Trunc K ι κ).bil = 0 := rfl

/-- The bilinear part of a finite sum is the sum of the bilinear parts. -/
theorem bil_sum {α : Type*} (s : Finset α) (t : α → Trunc K ι κ) :
    (∑ a ∈ s, t a).bil = ∑ a ∈ s, (t a).bil := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, bil_add, ih]

/-- The constant term is multiplicative. -/
@[simp] theorem const_mul (t u : Trunc K ι κ) : (t * u).const = t.const * u.const := rfl

/-- Product rule for the `x`-linear part. -/
theorem linX_mul (t u : Trunc K ι κ) (i : ι) :
    (t * u).linX i = t.const * u.linX i + u.const * t.linX i := by
  simp [linX, const, TrivSqZeroExt.snd_mul]

/-- Product rule for the `y`-linear part. -/
theorem linY_mul (t u : Trunc K ι κ) (j : κ) :
    (t * u).linY j = t.const * u.linY j + u.const * t.linY j := by
  simp [linY, const, TrivSqZeroExt.snd_mul]

/-- **Product rule for the bilinear part.**  Besides the two scaled bilinear parts, a product
contributes exactly two rank-one matrices. -/
theorem bil_mul (t u : Trunc K ι κ) (i : ι) (j : κ) :
    (t * u).bil i j =
      t.const * u.bil i j + u.const * t.bil i j + t.linX i * u.linY j + u.linX i * t.linY j := by
  simp [bil, linX, linY, const, TrivSqZeroExt.snd_mul]
  ring

/-- The scalar `a` as a truncated polynomial. -/
def ofScalar (a : K) : Trunc K ι κ := TrivSqZeroExt.inl (TrivSqZeroExt.inl a)

/-- `ofScalar` as a ring homomorphism. -/
def ofScalarHom : K →+* Trunc K ι κ :=
  (TrivSqZeroExt.inlHom (TruncX K ι) (κ → TruncX K ι)).comp (TrivSqZeroExt.inlHom K (ι → K))

@[simp] theorem ofScalarHom_apply (a : K) :
    (ofScalarHom : K →+* Trunc K ι κ) a = ofScalar a := rfl

@[simp] theorem const_ofScalar (a : K) : (ofScalar a : Trunc K ι κ).const = a := rfl

@[simp] theorem linX_ofScalar (a : K) (i : ι) : (ofScalar a : Trunc K ι κ).linX i = 0 := rfl

@[simp] theorem linY_ofScalar (a : K) (j : κ) : (ofScalar a : Trunc K ι κ).linY j = 0 := rfl

@[simp] theorem bil_ofScalar (a : K) : (ofScalar a : Trunc K ι κ).bil = 0 := rfl

/-- The variable `xᵢ`. -/
def varX [DecidableEq ι] (i : ι) : Trunc K ι κ :=
  TrivSqZeroExt.inl (TrivSqZeroExt.inr (Pi.single i 1))

/-- The variable `yⱼ`. -/
def varY [DecidableEq κ] (j : κ) : Trunc K ι κ :=
  TrivSqZeroExt.inr (Pi.single j 1)

@[simp] theorem const_varX [DecidableEq ι] (i : ι) : (varX i : Trunc K ι κ).const = 0 := rfl

@[simp] theorem linX_varX [DecidableEq ι] (i i' : ι) :
    (varX i : Trunc K ι κ).linX i' = if i' = i then 1 else 0 := by
  simp [varX, linX, Pi.single_apply]

@[simp] theorem linY_varX [DecidableEq ι] (i : ι) (j : κ) :
    (varX i : Trunc K ι κ).linY j = 0 := rfl

@[simp] theorem bil_varX [DecidableEq ι] (i : ι) : (varX i : Trunc K ι κ).bil = 0 := rfl

@[simp] theorem const_varY [DecidableEq κ] (j : κ) : (varY j : Trunc K ι κ).const = 0 := rfl

@[simp] theorem linX_varY [DecidableEq κ] (j : κ) (i : ι) :
    (varY j : Trunc K ι κ).linX i = 0 := rfl

@[simp] theorem linY_varY [DecidableEq κ] (j j' : κ) :
    (varY j : Trunc K ι κ).linY j' = if j' = j then 1 else 0 := by
  by_cases h : j' = j <;> simp [varY, linY, h]

@[simp] theorem bil_varY [DecidableEq κ] (j : κ) : (varY j : Trunc K ι κ).bil = 0 := by
  funext i j'
  by_cases h : j' = j <;> simp [varY, bil, h]

/-- The bilinear part of the monomial `a · xᵢ · yⱼ` is `a` at position `(i, j)`. -/
theorem bil_monomial [DecidableEq ι] [DecidableEq κ] (a : K) (i i' : ι) (j j' : κ) :
    (ofScalar a * varX i * varY j : Trunc K ι κ).bil i' j' =
      if i' = i ∧ j' = j then a else 0 := by
  rw [bil_mul, linX_mul, const_mul, bil_mul]
  by_cases hi : i' = i <;> by_cases hj : j' = j <;> simp [hi, hj]

end Trunc

/-! ### The span of the rank-one matrices contributed by multiplication gates -/

section BilSpan

variable {K : Type u} [CommRing K] {ι κ : Type v}

/-- The rank-one matrices `f ⊗ g` listed in `L`. -/
def rankOneGens (L : List ((ι → K) × (κ → K))) : Set (ι → κ → K) :=
  {M | ∃ fg ∈ L, M = fun i j ↦ fg.1 i * fg.2 j}

/-- The span of the rank-one matrices listed in `L`. -/
abbrev bilSpan (L : List ((ι → K) × (κ → K))) : Submodule K (ι → κ → K) :=
  Submodule.span K (rankOneGens L)

/-- A longer list spans more. -/
theorem bilSpan_mono {L L' : List ((ι → K) × (κ → K))} (h : ∀ fg ∈ L, fg ∈ L') :
    bilSpan L ≤ bilSpan L' :=
  Submodule.span_mono fun _ ⟨fg, hfg, hM⟩ ↦ ⟨fg, h fg hfg, hM⟩

/-- A listed rank-one matrix lies in the span. -/
theorem rankOne_mem_bilSpan {L : List ((ι → K) × (κ → K))} {f : ι → K} {g : κ → K}
    (h : (f, g) ∈ L) : (fun i j ↦ f i * g j) ∈ bilSpan L :=
  Submodule.subset_span ⟨(f, g), h, rfl⟩

/-- **Structure theorem for circuits.**  Evaluate a circuit with coefficients in `K` in the
truncated algebra, at an environment whose bilinear parts all lie in the span of `L₀`.  Then the
bilinear part of the value lies in the span of `L₀` together with at most `2 · mulOps` further
rank-one matrices. -/
theorem Circuit.exists_bilSpan {σ : Type v} (c : Circuit K σ) (env : σ → Trunc K ι κ)
    (L₀ : List ((ι → K) × (κ → K))) (henv : ∀ s, (env s).bil ∈ bilSpan L₀) :
    ∃ L : List ((ι → K) × (κ → K)), L.length ≤ 2 * c.mulOps ∧
      ((c.mapCoeff Trunc.ofScalar).eval env).bil ∈ bilSpan (L₀ ++ L) := by
  induction c with
  | input s =>
      refine ⟨[], by simp, ?_⟩
      simpa [Circuit.mapCoeff] using henv s
  | const a =>
      refine ⟨[], by simp, ?_⟩
      simp [Circuit.mapCoeff]
  | add p q hp hq =>
      obtain ⟨Lp, hLp, hp⟩ := hp
      obtain ⟨Lq, hLq, hq⟩ := hq
      refine ⟨Lp ++ Lq, ?_, ?_⟩
      · rw [List.length_append, Circuit.mulOps_add]
        omega
      · have h1 : bilSpan (L₀ ++ Lp) ≤ bilSpan (L₀ ++ (Lp ++ Lq)) :=
          bilSpan_mono fun fg h ↦ by
            rcases List.mem_append.mp h with h | h
            · exact List.mem_append_left _ h
            · exact List.mem_append_right _ (List.mem_append_left _ h)
        have h2 : bilSpan (L₀ ++ Lq) ≤ bilSpan (L₀ ++ (Lp ++ Lq)) :=
          bilSpan_mono fun fg h ↦ by
            rcases List.mem_append.mp h with h | h
            · exact List.mem_append_left _ h
            · exact List.mem_append_right _ (List.mem_append_right _ h)
        simp only [Circuit.mapCoeff, Circuit.eval_add, Trunc.bil_add]
        exact add_mem (h1 hp) (h2 hq)
  | mul p q hp hq =>
      obtain ⟨Lp, hLp, hp⟩ := hp
      obtain ⟨Lq, hLq, hq⟩ := hq
      set tp := (p.mapCoeff Trunc.ofScalar).eval env with htp
      set tq := (q.mapCoeff Trunc.ofScalar).eval env with htq
      refine ⟨Lp ++ (Lq ++ [(tp.linX, tq.linY), (tq.linX, tp.linY)]), ?_, ?_⟩
      · simp only [List.length_append, List.length_cons, List.length_nil, Circuit.mulOps_mul]
        omega
      · have h1 : bilSpan (L₀ ++ Lp) ≤
            bilSpan (L₀ ++ (Lp ++ (Lq ++ [(tp.linX, tq.linY), (tq.linX, tp.linY)]))) :=
          bilSpan_mono fun fg h ↦ by
            rcases List.mem_append.mp h with h | h
            · exact List.mem_append_left _ h
            · exact List.mem_append_right _ (List.mem_append_left _ h)
        have h2 : bilSpan (L₀ ++ Lq) ≤
            bilSpan (L₀ ++ (Lp ++ (Lq ++ [(tp.linX, tq.linY), (tq.linX, tp.linY)]))) :=
          bilSpan_mono fun fg h ↦ by
            rcases List.mem_append.mp h with h | h
            · exact List.mem_append_left _ h
            · exact List.mem_append_right _
                (List.mem_append_right _ (List.mem_append_left _ h))
        have h3 : (fun i j ↦ tp.linX i * tq.linY j) ∈
            bilSpan (L₀ ++ (Lp ++ (Lq ++ [(tp.linX, tq.linY), (tq.linX, tp.linY)]))) :=
          rankOne_mem_bilSpan (by simp)
        have h4 : (fun i j ↦ tq.linX i * tp.linY j) ∈
            bilSpan (L₀ ++ (Lp ++ (Lq ++ [(tp.linX, tq.linY), (tq.linX, tp.linY)]))) :=
          rankOne_mem_bilSpan (by simp)
        have hbil : (tp * tq).bil =
            tp.const • tq.bil + tq.const • tp.bil + (fun i j ↦ tp.linX i * tq.linY j) +
              fun i j ↦ tq.linX i * tp.linY j := by
          funext i j
          simp [Trunc.bil_mul]
        simp only [Circuit.mapCoeff, Circuit.eval_mul]
        rw [← htp, ← htq, hbil]
        exact add_mem (add_mem (add_mem (Submodule.smul_mem _ _ (h2 hq))
          (Submodule.smul_mem _ _ (h1 hp))) h3) h4
  | smul a p hp =>
      obtain ⟨Lp, hLp, hp⟩ := hp
      refine ⟨Lp, by simpa using hLp, ?_⟩
      have hbil : (Trunc.ofScalar a * (p.mapCoeff Trunc.ofScalar).eval env).bil =
          a • ((p.mapCoeff Trunc.ofScalar).eval env).bil := by
        funext i j
        simp [Trunc.bil_mul]
      simp only [Circuit.mapCoeff, Circuit.eval_smul]
      rw [hbil]
      exact Submodule.smul_mem _ _ hp

/-- **Structure theorem for straight-line programs.**  Evaluate a program with coefficients in
`K` in the truncated algebra, at an environment whose bilinear parts all lie in the span of `L₀`.
Then the bilinear parts of all outputs lie in the span of `L₀` together with at most
`2 · mulOps` further rank-one matrices — the same ones for every output. -/
theorem Straightline.exists_bilSpan {μ : Type v} [Fintype μ] {σ : Type v}
    (p : Straightline K μ σ) (env : σ → Trunc K ι κ)
    (L₀ : List ((ι → K) × (κ → K))) (henv : ∀ s, (env s).bil ∈ bilSpan L₀) :
    ∃ L : List ((ι → K) × (κ → K)), L.length ≤ 2 * p.mulOps ∧
      ∀ m, ((p.mapCoeff Trunc.ofScalar).eval env m).bil ∈ bilSpan (L₀ ++ L) := by
  induction p generalizing L₀ with
  | ret out =>
      choose Lm hLm hmem using fun m ↦ (out m).exists_bilSpan env L₀ henv
      refine ⟨Finset.univ.toList.flatMap Lm, ?_, fun m ↦ ?_⟩
      · rw [List.length_flatMap, Finset.sum_map_toList, Straightline.mulOps_ret, Finset.mul_sum]
        exact Finset.sum_le_sum fun m _ ↦ hLm m
      · refine bilSpan_mono (fun fg h ↦ ?_) (hmem m)
        rcases List.mem_append.mp h with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _
            (List.mem_flatMap.mpr ⟨m, Finset.mem_toList.mpr (Finset.mem_univ m), h⟩)
  | letBind c body ih =>
      obtain ⟨Lc, hLc, hc⟩ := c.exists_bilSpan env L₀ henv
      obtain ⟨Lb, hLb, hb⟩ := ih (extendEnv ((c.mapCoeff Trunc.ofScalar).eval env) env)
        (L₀ ++ Lc) (by
          intro o
          cases o with
          | none => exact hc
          | some s => exact bilSpan_mono (fun fg h ↦ List.mem_append_left _ h) (henv s))
      refine ⟨Lc ++ Lb, ?_, fun m ↦ ?_⟩
      · rw [List.length_append, Straightline.mulOps_letBind]
        omega
      · rw [← List.append_assoc]
        exact hb m

end BilSpan

/-! ### From a program to a bilinear algorithm -/

section Main

variable {F : Type u} [Field F] [Infinite F]
variable {ι κ μ : Type v} [Fintype ι] [Fintype κ] [Fintype μ] [DecidableEq ι] [DecidableEq κ]

/-- **A straight-line program computing a bilinear map yields a bilinear algorithm of at most
twice as many multiplications** (Strassen; notes, Proposition 2.7, converse direction).

Over an infinite field, if `p` computes the bilinear map `B` on all inputs, then `B` has a
bilinear algorithm of length at most `2 · p.mulOps`. -/
theorem exists_bilinearAlgorithm_of_straightline (B : CoordinateBilinearMap F ι κ μ)
    (p : Straightline F μ (ι ⊕ κ))
    (hp : ∀ (x : ι → F) (y : κ → F) (m : μ), p.eval (Sum.elim x y) m = B x y m) :
    ∃ r, r ≤ 2 * p.mulOps ∧ ∃ A : BilinearAlgorithm F ι κ μ r, A.Computes B := by
  classical
  set c := coeffOfBilinearMap B with hc
  have hB : ∀ (x : ι → F) (y : κ → F) (m : μ), B x y m = ∑ i, ∑ j, c i j m * x i * y j := by
    intro x y m
    conv_lhs => rw [← bilinearMapOfCoeff_coeffOfBilinearMap B]
    rfl
  -- The polynomial computed by each output equals the bilinear form.
  let q : μ → MvPolynomial (ι ⊕ κ) F :=
    fun m ↦ (p.mapCoeff MvPolynomial.C).eval MvPolynomial.X m
  let bpoly : μ → MvPolynomial (ι ⊕ κ) F := fun m ↦
    ∑ i, ∑ j, MvPolynomial.C (c i j m) * MvPolynomial.X (Sum.inl i) * MvPolynomial.X (Sum.inr j)
  have hq : ∀ m, q m = bpoly m := by
    intro m
    refine MvPolynomial.funext fun w ↦ ?_
    have h1 := Straightline.eval_mapCoeff (MvPolynomial.eval w) (map_add _) (map_mul _)
      (p.mapCoeff MvPolynomial.C) MvPolynomial.X m
    rw [Straightline.mapCoeff_mapCoeff] at h1
    simp only [MvPolynomial.eval_C, MvPolynomial.eval_X] at h1
    rw [Straightline.mapCoeff_id] at h1
    have h2 : w = Sum.elim (fun i ↦ w (Sum.inl i)) (fun j ↦ w (Sum.inr j)) := by
      funext s
      cases s <;> rfl
    rw [← h1, h2, hp, hB]
    simp [bpoly]
  -- Truncate.
  let envT : ι ⊕ κ → Trunc F ι κ := Sum.elim Trunc.varX Trunc.varY
  let τ : MvPolynomial (ι ⊕ κ) F →+* Trunc F ι κ :=
    MvPolynomial.eval₂Hom Trunc.ofScalarHom envT
  have hτ : ∀ m, τ (q m) = (p.mapCoeff Trunc.ofScalar).eval envT m := by
    intro m
    have h1 := Straightline.eval_mapCoeff τ (map_add _) (map_mul _)
      (p.mapCoeff MvPolynomial.C) MvPolynomial.X m
    rw [Straightline.mapCoeff_mapCoeff] at h1
    simp only [τ, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
      Trunc.ofScalarHom_apply] at h1
    exact h1.symm
  have hbil : ∀ m, ((p.mapCoeff Trunc.ofScalar).eval envT m).bil = fun i j ↦ c i j m := by
    intro m
    rw [← hτ m, hq m]
    funext i' j'
    simp only [bpoly, map_sum, map_mul, τ, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
      Trunc.ofScalarHom_apply, envT, Sum.elim_inl, Sum.elim_inr, Trunc.bil_sum,
      Finset.sum_apply, Trunc.bil_monomial]
    rw [Finset.sum_eq_single i']
    · rw [Finset.sum_eq_single j']
      · simp
      · intro j _ hj
        simp [Ne.symm hj]
      · intro h
        exact absurd (Finset.mem_univ j') h
    · intro i _ hi
      exact Finset.sum_eq_zero fun j _ ↦ by simp [Ne.symm hi]
    · intro h
      exact absurd (Finset.mem_univ i') h
  -- The structure theorem.
  obtain ⟨L, hL, hmem⟩ := p.exists_bilSpan envT [] (by
    intro s
    cases s <;> simp [envT])
  have hgens : rankOneGens L =
      Set.range fun k : Fin L.length ↦ fun (i : ι) (j : κ) ↦ (L.get k).1 i * (L.get k).2 j := by
    ext M
    constructor
    · rintro ⟨fg, hfg, rfl⟩
      obtain ⟨k, rfl⟩ := List.mem_iff_get.mp hfg
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨L.get k, List.get_mem _ _, rfl⟩
  have hw : ∀ m, ∃ w : Fin L.length → F,
      ∑ k, w k • (fun (i : ι) (j : κ) ↦ (L.get k).1 i * (L.get k).2 j) = fun i j ↦ c i j m := by
    intro m
    have h := hmem m
    rw [List.nil_append, hbil m, bilSpan, hgens] at h
    exact (Submodule.mem_span_range_iff_exists_fun F).mp h
  choose w hw using hw
  refine ⟨L.length, hL, ⟨fun k ↦ (L.get k).1, fun k ↦ (L.get k).2, fun k m ↦ w m k⟩, ?_⟩
  intro x y m
  show B x y m = ∑ k, w m k * (∑ a, (L.get k).1 a * x a) * (∑ b, (L.get k).2 b * y b)
  have hcm : ∀ i j, c i j m = ∑ k, w m k * ((L.get k).1 i * (L.get k).2 j) := by
    intro i j
    have h := congrFun (congrFun (hw m) i) j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h.symm
  have hR : ∀ k, w m k * (∑ a, (L.get k).1 a * x a) * (∑ b, (L.get k).2 b * y b) =
      ∑ a, ∑ b, w m k * ((L.get k).1 a * (L.get k).2 b) * x a * y b := by
    intro k
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ ↦ by ring
  rw [hB]
  simp only [hcm, hR, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  conv_rhs => rw [Finset.sum_comm]

end Main

/-! ### Matrix multiplication and the exponent -/

section MatrixMultiplication

variable {F : Type u} [Field F] [Infinite F]

/-- **The rank of matrix multiplication is at most twice the number of multiplication gates** of
any straight-line program computing the product. -/
theorem rankLE_matrixMultiplication_of_straightline {m n p : ℕ}
    (prog : Straightline F (Fin p × Fin m) ((Fin m × Fin n) ⊕ (Fin n × Fin p)))
    (hprog : ∀ (x : Fin m × Fin n → F) (y : Fin n × Fin p → F) (z : Fin p × Fin m),
      prog.eval (Sum.elim x y) z = matrixProductMap (K := F) m n p x y z) :
    RankLE (2 * prog.mulOps) (matrixMultiplication (K := F) m n p) := by
  obtain ⟨r, hr, A, hA⟩ :=
    exists_bilinearAlgorithm_of_straightline (matrixProductMap (K := F) m n p) prog hprog
  exact ((matrixMultiplication_rankLE_iff_exists_algorithm (K := F) m n p r).mpr ⟨A, hA⟩).mono hr

/-- **Programs with `O(n^τ)` multiplication gates force `ω ≤ τ`** (notes, Proposition 2.7,
converse direction). -/
theorem omega_le_of_straightline {τ C : ℝ} (hτ : 0 ≤ τ) (hC : 0 < C)
    (h : ∀ n : ℕ, 1 ≤ n →
      ∃ prog : Straightline F (Fin n × Fin n) ((Fin n × Fin n) ⊕ (Fin n × Fin n)),
        (∀ (x y : Fin n × Fin n → F) (z : Fin n × Fin n),
            prog.eval (Sum.elim x y) z = matrixProductMap (K := F) n n n x y z)
          ∧ (prog.mulOps : ℝ) ≤ C * (n : ℝ) ^ τ) :
    omega F ≤ τ := by
  refine omega_le F ⟨hτ, 2 * C, by positivity, fun n hn ↦ ?_⟩
  obtain ⟨prog, hprog, hcost⟩ := h n hn
  have hrank : squareMatrixRankSequence F n ≤ 2 * prog.mulOps :=
    rank_le_iff.mpr (rankLE_matrixMultiplication_of_straightline prog hprog)
  calc (squareMatrixRankSequence F n : ℝ) ≤ ((2 * prog.mulOps : ℕ) : ℝ) := by
        exact_mod_cast hrank
    _ = 2 * (prog.mulOps : ℝ) := by push_cast; ring
    _ ≤ 2 * (C * (n : ℝ) ^ τ) := by linarith
    _ = 2 * C * (n : ℝ) ^ τ := by ring

/-- **Proposition 2.7.**  Over an infinite field, `ω ≤ τ` if and only if, for every `ε > 0`, the
`n × n` matrix product is computed by straight-line programs with `O(n^(τ+ε))` arithmetic
operations.

The forward direction is `exists_straightline_matrixProduct_of_omega_lt`
(`RankComplexityRecursion.lean`); the converse is `omega_le_of_straightline`, since the
multiplication gates are among the operations. -/
theorem omega_le_iff_exists_straightline {τ : ℝ} (hτ : 0 ≤ τ) :
    omega F ≤ τ ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ prog : Straightline F (Fin n × Fin n) ((Fin n × Fin n) ⊕ (Fin n × Fin n)),
        (∀ (x y : Fin n × Fin n → F) (z : Fin n × Fin n),
            prog.eval (Sum.elim x y) z = matrixProductMap (K := F) n n n x y z)
          ∧ (prog.totalOps : ℝ) ≤ C * (n : ℝ) ^ (τ + ε) := by
  constructor
  · intro h ε hε
    exact exists_straightline_matrixProduct_of_omega_lt (lt_of_le_of_lt h (by linarith))
  · intro h
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    obtain ⟨C, hC, hprog⟩ := h ε hε
    refine omega_le_of_straightline (by linarith) hC fun n hn ↦ ?_
    obtain ⟨prog, hcomp, hcost⟩ := hprog n hn
    refine ⟨prog, hcomp, le_trans ?_ hcost⟩
    have hle : prog.mulOps ≤ prog.totalOps := by
      rw [Straightline.totalOps_eq]
      omega
    exact_mod_cast hle

end MatrixMultiplication

end AlgebraicComplexity
