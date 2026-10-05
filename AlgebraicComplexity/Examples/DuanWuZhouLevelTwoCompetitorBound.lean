/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCompetitorCount

set_option autoImplicit false

/-!
# `V`, defined so that its certificate holds by construction

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoCompetitorCount.lean`'s
`dwz63_hV_of_mul` asks a client for `hprod`, the division-free certificate

`|matchable α K| · |compatibleSet comp₀| ≤ V · |T_K|`.

Taking `V` to be the integer ceiling of the left side over `|T_K|` makes `hprod` true **by
definition**, so no numeric certificate has to be supplied at all: what a client must instead
establish is an *upper* bound on that same `V`, which is where the rate estimates enter
(`Examples/DuanWuZhouLevelTwoCompetitorRateBrick.lean`).

* `dwz63CompetitorBound` is `⌈(|matchable| · |compatibleSet|) / |T_K|⌉`, spelled
  `(P + T - 1) / T`.
* `dwz63_competitorBound_spec` is `hprod`, by `Nat.div_add_mod` alone.
* `dwz63_competitorBound_le_iff` is the exact reduction `V ≤ D ↔ P ≤ D · T`, which is what turns a
  rate comparison into the hypothesis `hVdeg` of
  `Examples/DuanWuZhouLevelTwoJointHashBranch.lean`.
* `dwz63UniformCompetitorBound` takes the `Finset.sup` over the marked family, so one `V` serves
  every retained triple with no uniformity lemma about `|matchable|` or `|compatibleSet|`; the
  committed `card_matchableCompatible_eq_of_mem_typicalSet` and
  `card_compatibleSet_eq_of_multiplicity_eq` say the supremum is attained everywhere, but nothing
  here needs that.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, §6.2 (`global_value.tex`), `lemma:pcomp_g`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor ProgressionHash CompatibleSplit
open scoped BigOperators

universe u v w x

/-! ## Ceiling division -/

/-- `P ≤ ⌈P / T⌉ · T`. -/
theorem dwz63_le_ceilDiv_mul (P T : ℕ) (hT : 0 < T) : P ≤ (P + T - 1) / T * T := by
  have h1 : T * ((P + T - 1) / T) + (P + T - 1) % T = P + T - 1 := Nat.div_add_mod _ _
  have h2 : (P + T - 1) % T < T := Nat.mod_lt _ hT
  have h3 : (P + T - 1) / T * T = T * ((P + T - 1) / T) := Nat.mul_comm _ _
  omega

/-- `⌈P / T⌉ ≤ D ↔ P ≤ D · T`. -/
theorem dwz63_ceilDiv_le_iff (P T D : ℕ) (hT : 0 < T) :
    (P + T - 1) / T ≤ D ↔ P ≤ D * T := by
  constructor
  · intro h
    exact le_trans (dwz63_le_ceilDiv_mul P T hT) (Nat.mul_le_mul_right T h)
  · intro h
    have h1 : T * ((P + T - 1) / T) + (P + T - 1) % T = P + T - 1 := Nat.div_add_mod _ _
    have h2 : (P + T - 1) % T < T := Nat.mod_lt _ hT
    by_contra hcon
    have hD : D + 1 ≤ (P + T - 1) / T := by omega
    have hmul : T * (D + 1) ≤ T * ((P + T - 1) / T) := Nat.mul_le_mul_left T hD
    have hDT : D * T = T * D := Nat.mul_comm _ _
    have hexpand : T * (D + 1) = T * D + T := by ring
    omega

/-! ## The competitor bound -/

section Bound

variable {C : Type u} [Fintype C] [DecidableEq C]
variable {L : Type v} [Fintype L] [DecidableEq L]
variable {Z : Type w} [Fintype Z] [DecidableEq Z]
variable {N : ℕ}

/-- **`V`, as the integer ceiling of the exact quantity.** -/
noncomputable def dwz63CompetitorBound (S : SplitRequirements C L Z) (αType : C → ℕ)
    (K : Fin N → Z) (comp₀ : Fin N → C) : ℕ :=
  ((S.matchable αType K).card * (S.compatibleSet comp₀).card + (S.typicalSet K).card - 1) /
    (S.typicalSet K).card

omit [DecidableEq C] [DecidableEq L] [DecidableEq Z] in
/-- **`hprod`, by definition.** -/
theorem dwz63_competitorBound_spec (S : SplitRequirements C L Z) (αType : C → ℕ)
    (K : Fin N → Z) (comp₀ : Fin N → C) (hT : 0 < (S.typicalSet K).card) :
    (S.matchable αType K).card * (S.compatibleSet comp₀).card ≤
      dwz63CompetitorBound S αType K comp₀ * (S.typicalSet K).card :=
  dwz63_le_ceilDiv_mul _ _ hT

omit [DecidableEq C] [DecidableEq L] [DecidableEq Z] in
/-- **The exact reduction of an upper bound on `V` to a product inequality.** -/
theorem dwz63_competitorBound_le_iff (S : SplitRequirements C L Z) (αType : C → ℕ)
    (K : Fin N → Z) (comp₀ : Fin N → C) (D : ℕ) (hT : 0 < (S.typicalSet K).card) :
    dwz63CompetitorBound S αType K comp₀ ≤ D ↔
      (S.matchable αType K).card * (S.compatibleSet comp₀).card ≤ D * (S.typicalSet K).card :=
  dwz63_ceilDiv_le_iff _ _ _ hT

end Bound

/-! ## One bound for the whole marked family -/

section Uniform

variable {R : Type x} [Field R] {N : ℕ} {targetVal : R}
variable {C : Type u} [Fintype C] [DecidableEq C]
variable {L : Type v} [Fintype L] [DecidableEq L]
variable {Z : Type w} [Fintype Z] [DecidableEq Z]
variable {A : Type v}

/-- **The uniform competitor bound**: the supremum over the marked family. -/
noncomputable def dwz63UniformCompetitorBound (S : SplitRequirements C L Z)
    (component : LegalTriple R (Fin N) targetVal → (Fin N → C)) (αType : C → ℕ)
    (marked : Finset (LegalTriple R (Fin N) targetVal)) : ℕ := by
  classical
  exact marked.sup fun a ↦ dwz63CompetitorBound S αType (S.zIndex ∘ component a) (component a)

omit [DecidableEq C] [DecidableEq L] [DecidableEq Z] in
/-- **`hprod` at the uniform bound.** -/
theorem dwz63_uniformCompetitorBound_spec (S : SplitRequirements C L Z)
    (component : LegalTriple R (Fin N) targetVal → (Fin N → C)) (αType : C → ℕ)
    (marked : Finset (LegalTriple R (Fin N) targetVal))
    (hT : ∀ a ∈ marked, 0 < (S.typicalSet (S.zIndex ∘ component a)).card) :
    ∀ a ∈ marked,
      (S.matchable αType (S.zIndex ∘ component a)).card *
          (S.compatibleSet (component a)).card ≤
        dwz63UniformCompetitorBound S component αType marked *
          (S.typicalSet (S.zIndex ∘ component a)).card := by
  classical
  intro a ha
  refine le_trans (dwz63_competitorBound_spec S αType _ _ (hT a ha)) ?_
  have hsup : dwz63CompetitorBound S αType (S.zIndex ∘ component a) (component a) ≤
      dwz63UniformCompetitorBound S component αType marked := by
    unfold dwz63UniformCompetitorBound
    exact Finset.le_sup (f := fun b ↦ dwz63CompetitorBound S αType
      (S.zIndex ∘ component b) (component b)) ha
  exact Nat.mul_le_mul_right _ hsup

/-- **`hV` with no numeric certificate left to supply.**

`dwz63_hV_of_mul` at `V := dwz63UniformCompetitorBound`; the typicalness premises are the ones
`dwz63SplitCompat_isTypical` already produces. -/
theorem dwz63_hV_uniform (S : SplitRequirements C L Z)
    (component : LegalTriple R (Fin N) targetVal → (Fin N → C))
    (read : LegalTriple R (Fin N) targetVal → A → (Fin N → L)) (αType : C → ℕ)
    (marked : Finset (LegalTriple R (Fin N) targetVal))
    (huseful : ∀ a ∈ marked, ∀ w : A, S.IsUseful (component a) (read a w))
    (hcompType : ∀ a ∈ marked, WordType.multiplicity (component a) = αType)
    (hT : ∀ a ∈ marked, 0 < (S.typicalSet (S.zIndex ∘ component a)).card) :
    ∀ a ∈ marked, ∀ w : A,
      (S.matchableCompatible αType (S.zIndex ∘ component a) (read a w)).card ≤
        dwz63UniformCompetitorBound S component αType marked :=
  dwz63_hV_of_mul S component read αType marked _ huseful hcompType
    (dwz63_uniformCompetitorBound_spec S component αType marked hT)

end Uniform

end AlgebraicComplexity.Examples
