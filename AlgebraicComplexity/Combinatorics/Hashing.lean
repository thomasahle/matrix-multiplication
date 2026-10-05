/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ThreeTermProgression
import AlgebraicComplexity.Combinatorics.LinearHash
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.LinearCombination

/-!
# Finite affine hash seeds

This file begins the exact counting layer of laser-method hashing.  For fixed `X`- and `Y`-block
indices and a fixed bucket, the constraints that both hashes equal that bucket determine the
offset and shift uniquely, while leaving every linear weight free.  We package the resulting
bijection and exact fiber cardinality.

Together with `ProgressionHash.surviving_hashes_equal`, this proves the deterministic and first
uniform-counting parts of the hashing lemma used in both the global and constituent stages of
*More Asymmetry Yields Faster Matrix Multiplication*.  Collision conditioning and isolation are
kept as later, genuinely probabilistic layers.
-/

namespace AlgebraicComplexity

universe u v

namespace ProgressionHash

/-- Random data in the standard affine hashing construction: one common offset, one `Y`/`Z`
shift, and one independently chosen linear weight per tensor position. -/
@[ext] structure Seed (R : Type u) (ι : Type v) where
  offset : R
  shift : R
  weights : ι → R

/-- Seeds are canonically equivalent to the product of their three fields. -/
def Seed.equivProd {R : Type u} {ι : Type v} :
    Seed R ι ≃ R × R × (ι → R) where
  toFun seed := (seed.offset, seed.shift, seed.weights)
  invFun data := ⟨data.1, data.2.1, data.2.2⟩
  left_inv seed := by cases seed; rfl
  right_inv data := by cases data; rfl

instance Seed.instNonempty
    {R : Type u} {ι : Type v} [Nonempty R] : Nonempty (Seed R ι) :=
  Nonempty.map (fun r => ⟨r, r, fun _ => r⟩) ‹Nonempty R›

noncomputable instance Seed.instFintype
    {R : Type u} {ι : Type v} [Fintype R] [Fintype ι] : Fintype (Seed R ι) := by
  letI := Classical.decEq ι
  exact Fintype.ofEquiv (R × R × (ι → R)) Seed.equivProd.symm

namespace Seed

variable {R : Type u} [Field R]
variable {ι : Type v} [Fintype ι]

/-- `X`-hash determined by a seed. -/
noncomputable def xHash (seed : Seed R ι) (I : ι → R) : R :=
  hashX seed.offset seed.weights I

/-- `Y`-hash determined by a seed. -/
noncomputable def yHash (seed : Seed R ι) (J : ι → R) : R :=
  hashY seed.offset seed.shift seed.weights J

/-- `Z`-hash determined by a seed. -/
noncomputable def zHash (seed : Seed R ι) (target : R) (K : ι → R) : R :=
  hashZ seed.offset seed.shift target seed.weights K

/-- The event that the fixed `X`- and `Y`-blocks both hash to bucket `b`. -/
def InCommonBucket (I J : ι → R) (b : R) (seed : Seed R ι) : Prop :=
  seed.xHash I = b ∧ seed.yHash J = b

/-- The event that all three hashes of a block triple equal the prescribed bucket. -/
def InCommonTriple (I J K : ι → R) (target b : R) (seed : Seed R ι) : Prop :=
  seed.xHash I = b ∧ seed.yHash J = b ∧ seed.zHash target K = b

/-- Given freely chosen linear weights, the unique offset and shift that put fixed `X` and `Y`
indices into bucket `b`. -/
noncomputable def forWeights (I J : ι → R) (b : R) (weights : ι → R) : Seed R ι where
  offset := b - linear weights I
  shift := b - (b - linear weights I) - linear weights J
  weights := weights

@[simp] theorem forWeights_xHash (I J : ι → R) (b : R) (weights : ι → R) :
    (forWeights I J b weights).xHash I = b := by
  simp [forWeights, xHash, hashX]

@[simp] theorem forWeights_yHash (I J : ι → R) (b : R) (weights : ι → R) :
    (forWeights I J b weights).yHash J = b := by
  simp [forWeights, yHash, hashY]

/-- Once the original `X/Y` triple is fixed in bucket `b`, a second `Y`-index lands in `b`
exactly when the free weight table lies in the zero fiber of the difference vector. -/
theorem forWeights_yHash_alt_iff (I J J' : ι → R) (b : R) (weights : ι → R) :
    (forWeights I J b weights).yHash J' = b ↔
      FiniteLinearHash.dot weights (J' - J) = 0 := by
  rw [FiniteLinearHash.dot_sub_eq_zero_iff]
  change
    (b - linear weights I) +
        (b - (b - linear weights I) - linear weights J) + linear weights J' = b ↔
      linear weights J' = linear weights J
  constructor <;> intro h <;> linear_combination h

/-- Translate an alternative `X`-word into the equivalent alternative `Y`-word inside a fixed
common-bucket fiber.  This small affine identity lets the isolation/counting layer use one kind
of collision event for conflicts on any tensor leg. -/
def transportXAlternative (I J I' : ι → R) : ι → R :=
  J + I' - I

/-- Once `(I,J)` lies in a common bucket, hashing an alternative `X`-word is the same as hashing
its translated `Y`-word. -/
theorem yHash_transportXAlternative_eq_xHash
    (seed : Seed R ι) (I J I' : ι → R) (b : R)
    (hcommon : InCommonBucket I J b seed) :
    seed.yHash (transportXAlternative I J I') = seed.xHash I' := by
  classical
  have hx := hcommon.1
  have hy := hcommon.2
  unfold transportXAlternative yHash xHash hashY hashX at *
  unfold linear at *
  simp only [Pi.add_apply, Pi.sub_apply, mul_sub, mul_add,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  linear_combination hy - hx

omit [Fintype ι] in
/-- A genuinely different `X`-word translates to a genuinely different `Y`-word. -/
theorem transportXAlternative_ne
    (I J I' : ι → R) (hne : I' ≠ I) :
    transportXAlternative I J I' ≠ J := by
  intro h
  apply hne
  funext i
  have hi := congrFun h i
  simp only [transportXAlternative, Pi.add_apply, Pi.sub_apply] at hi
  linear_combination hi

/-- Exact parametrization of a common-bucket fiber by the unconstrained linear weights. -/
noncomputable def commonBucketEquivWeights (I J : ι → R) (b : R) :
    (ι → R) ≃ {seed : Seed R ι // InCommonBucket I J b seed} where
  toFun weights :=
    ⟨forWeights I J b weights, forWeights_xHash I J b weights,
      forWeights_yHash I J b weights⟩
  invFun seed := seed.1.weights
  left_inv _ := rfl
  right_inv seed := by
    apply Subtype.ext
    rcases seed with ⟨⟨offset, shift, weights⟩, hx, hy⟩
    have hoffset : b - linear weights I = offset := by
      rw [← hx]
      simp [xHash, hashX]
    have hshift : b - (b - linear weights I) - linear weights J = shift := by
      rw [hoffset, ← hy]
      simp [yHash, hashY]
      ring
    exact Seed.ext hoffset hshift rfl

/-- The seeds placing both an original pair `(I,J)` and an alternative `J'` in bucket `b` are
equivalent to one dot-product fiber in the free weight table. -/
noncomputable def commonBucketCollisionEquivLinearFiber (I J J' : ι → R) (b : R) :
    {weights : ι → R // FiniteLinearHash.dot weights (J' - J) = 0} ≃
      {seed : Seed R ι // InCommonBucket I J b seed ∧ seed.yHash J' = b} := by
  let base := commonBucketEquivWeights I J b
  let restricted :
      {weights : ι → R // FiniteLinearHash.dot weights (J' - J) = 0} ≃
        {seed : {seed : Seed R ι // InCommonBucket I J b seed} //
          seed.1.yHash J' = b} :=
    base.subtypeEquiv fun weights => by
      change FiniteLinearHash.dot weights (J' - J) = 0 ↔
        (forWeights I J b weights).yHash J' = b
      exact (forWeights_yHash_alt_iff I J J' b weights).symm
  exact restricted.trans
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (InCommonBucket I J b) (fun seed => seed.yHash J' = b))

/-- A legal block triple in a common `X`/`Y` bucket has its `Z`-hash in that bucket as well. -/
theorem zHash_eq_of_commonBucket [NeZero (2 : R)]
    (seed : Seed R ι) (I J K : ι → R) (target b : R)
    (hlegal : ∀ t, I t + J t + K t = target)
    (hb : InCommonBucket I J b seed) :
    seed.zHash target K = b := by
  have hp := hash_progression seed.offset seed.shift target seed.weights I J K hlegal
  rw [← xHash, ← yHash, ← zHash, hb.1, hb.2] at hp
  have htwo : (2 : R) * b = 2 * seed.zHash target K := by
    simpa [two_mul] using hp
  exact (mul_left_cancel₀ (NeZero.ne (2 : R)) htwo).symm

/-- For a legal block triple, constraining the `X`- and `Y`-hashes already constrains the
`Z`-hash.  Thus the paper's three-hash event is exactly the two-equation common-bucket event. -/
theorem inCommonTriple_iff_commonBucket [NeZero (2 : R)]
    (seed : Seed R ι) (I J K : ι → R) (target b : R)
    (hlegal : ∀ t, I t + J t + K t = target) :
    InCommonTriple I J K target b seed ↔ InCommonBucket I J b seed := by
  constructor
  · rintro ⟨hX, hY, _⟩
    exact ⟨hX, hY⟩
  · intro hb
    exact ⟨hb.1, hb.2, zHash_eq_of_commonBucket seed I J K target b hlegal hb⟩

section Finite

variable [Fintype R]

omit [Field R] in
/-- Cardinality of the affine-seed space in its product presentation. -/
theorem card_seed :
    Fintype.card (Seed R ι) =
      Fintype.card R * (Fintype.card R * Fintype.card R ^ Fintype.card ι) := by
  classical
  rw [Fintype.card_congr (Seed.equivProd : Seed R ι ≃ R × R × (ι → R))]
  simp only [Fintype.card_prod, Fintype.card_fun]

/-- The common-bucket fiber has one element for every choice of linear weights. -/
theorem card_commonBucket (I J : ι → R) (b : R) :
    Nat.card {seed : Seed R ι // InCommonBucket I J b seed} =
      Fintype.card R ^ Fintype.card ι := by
  calc
    Nat.card {seed : Seed R ι // InCommonBucket I J b seed} = Nat.card (ι → R) :=
      (Nat.card_congr (commonBucketEquivWeights I J b)).symm
    _ = Nat.card R ^ Nat.card ι := Nat.card_fun
    _ = Fintype.card R ^ Fintype.card ι := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

/-- The two affine constraints defining a common bucket remove exactly two field degrees of
freedom from the complete seed space. -/
theorem card_commonBucket_mul_square (I J : ι → R) (b : R) :
    Nat.card {seed : Seed R ι // InCommonBucket I J b seed} *
        (Fintype.card R * Fintype.card R) = Fintype.card (Seed R ι) := by
  rw [card_commonBucket, card_seed]
  ring

end Finite

/-- Exact conditional-collision count.  If `J'` differs from `J`, then among the seeds putting
`(I,J)` in bucket `b`, precisely a `1 / |R|` fraction also put `J'` in bucket `b`. -/
theorem card_commonBucket_collision_mul (I J J' : ι → R) (b : R) (hJJ' : J' ≠ J) :
    Nat.card {seed : Seed R ι //
        InCommonBucket I J b seed ∧ seed.yHash J' = b} * Nat.card R =
      Nat.card {seed : Seed R ι // InCommonBucket I J b seed} := by
  have hdiff : J' - J ≠ 0 := sub_ne_zero.mpr hJJ'
  calc
    Nat.card {seed : Seed R ι //
          InCommonBucket I J b seed ∧ seed.yHash J' = b} * Nat.card R =
        Nat.card {weights : ι → R //
          FiniteLinearHash.dot weights (J' - J) = 0} * Nat.card R := by
            rw [Nat.card_congr (commonBucketCollisionEquivLinearFiber I J J' b)]
    _ = Nat.card (ι → R) := FiniteLinearHash.card_dot_fiber_mul hdiff 0
    _ = Nat.card {seed : Seed R ι // InCommonBucket I J b seed} :=
      Nat.card_congr (commonBucketEquivWeights I J b)

end Seed

end ProgressionHash

end AlgebraicComplexity
