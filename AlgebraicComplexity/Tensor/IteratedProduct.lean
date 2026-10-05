/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.IndexedProduct
import AlgebraicComplexity.Tensor.PositiveWord
import AlgebraicComplexity.Tensor.PositiveWordConst
import AlgebraicComplexity.Tensor.Power

/-!
# Positive iterated external products

This file uses a left-associated external product to expose the independent blocks in powers of
finite indexed direct sums.  Canonical `Tensor.power` remains the public representation for
asymptotic invariants; the parenthesized representation here is a proof device for multinomial
type extraction.

The natural-number parameter counts *additional* factors.  Thus `iteratedExternal T 0 = T` and
`iteratedExternal T n` contains `n + 1` copies of `T`.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]

/-- A packaged family of modules, one for each tensor leg.

Packaging the instances makes recursively parenthesized tensor-product spaces straightforward:
each recursive step constructs another object of the same universe.  The ordinary public tensor
API continues to use the underlying `Space` family directly. -/
structure LegModuleFamily (K : Type u) [CommSemiring K] where
  Space : Leg → Type (max u v)
  [addCommMonoid : ∀ c, AddCommMonoid (Space c)]
  [module : ∀ c, Module K (Space c)]

attribute [instance] LegModuleFamily.addCommMonoid LegModuleFamily.module

/-- Package an ordinary family of tensor-leg modules. -/
def LegModuleFamily.of (V : Leg → Type (max u v))
    [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)] :
    LegModuleFamily.{u, v} K where
  Space := V

namespace LegModuleFamily

/-- Reindex a packaged leg-module family along a tensor orientation. -/
@[reducible] def permute (A : LegModuleFamily.{u, v} K) (e : Orientation) :
    LegModuleFamily.{u, v} K where
  Space c := A.Space (e.symm c)

/-- Pair corresponding legs of two packaged families. -/
@[reducible] def external (A B : LegModuleFamily.{u, v} K) : LegModuleFamily.{u, v} K where
  Space c := TensorProduct K (A.Space c) (B.Space c)

/-- Left-associated leg spaces for a positive iterated external product. -/
@[reducible] def iterated (A : LegModuleFamily.{u, v} K) : ℕ → LegModuleFamily.{u, v} K
  | 0 => A
  | n + 1 => (iterated A n).external A

end LegModuleFamily

/-- A positive left-associated external power; the value at `n` has `n + 1` factors. -/
def iteratedExternal (A : LegModuleFamily.{u, v} K) (T : Tensor3 K A.Space) :
    (n : ℕ) → Tensor3 K (A.iterated n).Space
  | 0 => T
  | n + 1 => external (iteratedExternal A T n) T

@[simp] theorem iteratedExternal_zero (A : LegModuleFamily.{u, v} K)
    (T : Tensor3 K A.Space) :
    iteratedExternal A T 0 = T := rfl

@[simp] theorem iteratedExternal_succ (A : LegModuleFamily.{u, v} K)
    (T : Tensor3 K A.Space) (n : ℕ) :
    iteratedExternal A T (n + 1) = external (iteratedExternal A T n) T := rfl

/-- Apply a function letterwise to a recursively represented positive word. -/
def positiveWordMap {J : Type*} (f : I → J) :
    (n : ℕ) → PositiveWord I n → PositiveWord J n
  | 0, i => f i
  | n + 1, q => (positiveWordMap f n q.1, f q.2)

/-- Transport a recursive positive word across an equality of its additional-factor
parameters. -/
def positiveWordCast {n m : ℕ} (h : n = m) (word : PositiveWord I n) :
    PositiveWord I m :=
  _root_.cast (congrArg (PositiveWord I) h) word

@[simp] theorem positiveWordCast_rfl (word : PositiveWord I n) :
    positiveWordCast rfl word = word := rfl

@[simp] theorem positiveWordMap_zero {J : Type*} (f : I → J) (i : I) :
    positiveWordMap f 0 i = f i := rfl

@[simp] theorem positiveWordMap_succ {J : Type*} (f : I → J) (n : ℕ)
    (q : PositiveWord I (n + 1)) :
    positiveWordMap f (n + 1) q = (positiveWordMap f n q.1, f q.2) := rfl

/-- Function representation of a constant positive word. -/
@[simp] theorem positiveWordEquiv_const (i : I) (n : ℕ) :
    positiveWordEquiv I n (positiveWordConst i n) = fun _ ↦ i := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Fin.snoc
        (positiveWordEquiv I n (positiveWordConst i n)) i = fun _ ↦ i
      rw [ih]
      funext position
      refine Fin.lastCases ?_ (fun j ↦ ?_) position
      · simp
      · simp

/-- Function-word representation commutes with letterwise mapping. -/
theorem positiveWordEquiv_map {J : Type*} (f : I → J) (n : ℕ)
    (q : PositiveWord I n) :
    positiveWordEquiv J n (positiveWordMap f n q) =
      f ∘ positiveWordEquiv I n q := by
  induction n with
  | zero =>
      funext i
      fin_cases i
      rfl
  | succ n ih =>
      rw [positiveWordEquiv_succ_apply, positiveWordMap_succ,
        positiveWordEquiv_succ_apply]
      funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp
      · simpa [Function.comp_def] using congrFun (ih q.1) j

/-- Concatenate two nonempty recursively parenthesized words.  A word with parameters `n` and
`m` contains `(n + 1) + (m + 1)` letters, so the result has parameter `n + m + 1`. -/
def positiveWordAppend (left : PositiveWord I n) :
    (m : ℕ) → PositiveWord I m → PositiveWord I (n + m + 1)
  | 0, right => (left, right)
  | m + 1, right => (positiveWordAppend left m right.1, right.2)

/-- Function-word form of recursive positive-word concatenation.  The length equality is made
explicit because the recursive-word parameter counts additional letters rather than letters. -/
theorem positiveWordEquiv_append (left : PositiveWord I n) (right : PositiveWord I m) :
    positiveWordEquiv I (n + m + 1) (positiveWordAppend left m right) =
      Fin.append (positiveWordEquiv I n left) (positiveWordEquiv I m right) ∘
        Fin.cast (by omega) := by
  induction m with
  | zero =>
      rw [positiveWordEquiv_succ_apply]
      change (@Fin.snoc (n + 1) (fun _ ↦ I)
        (positiveWordEquiv I n left) right) = _
      rw [← Fin.append_right_eq_snoc
        (positiveWordEquiv I n left) (fun _ : Fin 1 ↦ right)]
      rfl
  | succ m ih =>
      rw [positiveWordEquiv_succ_apply, positiveWordEquiv_succ_apply]
      change (@Fin.snoc (n + m + 2) (fun _ ↦ I)
          (positiveWordEquiv I (n + m + 1) (positiveWordAppend left m right.1))
          right.2) = _
      rw [ih, Fin.append_snoc]
      funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · rw [Fin.snoc_last]
        change right.2 = @Fin.snoc ((n + 1) + (m + 1)) (fun _ ↦ I)
          (Fin.append (positiveWordEquiv I n left)
            (positiveWordEquiv I m right.1)) right.2 _
        have hlast : Fin.cast (by omega) (Fin.last (n + m + 2)) =
            Fin.last ((n + 1) + (m + 1)) := by
          apply Fin.ext
          simp
        rw [hlast, Fin.snoc_last]
      · simp [Function.comp_apply]

/-- Concatenation is a bijection between a pair of nonempty words and the combined word. -/
theorem positiveWordAppend_bijective (n m : ℕ) :
    Function.Bijective
      (fun q : PositiveWord I n × PositiveWord I m ↦
        positiveWordAppend q.1 m q.2) := by
  induction m with
  | zero =>
      constructor
      · intro a b h
        exact h
      · intro q
        exact ⟨q, rfl⟩
  | succ m ih =>
      constructor
      · rintro ⟨left, right, last⟩ ⟨left', right', last'⟩ h
        have hprefix : positiveWordAppend left m right =
            positiveWordAppend left' m right' := congrArg Prod.fst h
        have hlast : last = last' := congrArg Prod.snd h
        have hpairs : (left, right) = (left', right') := ih.1 hprefix
        cases hpairs
        cases hlast
        rfl
      · rintro ⟨head, last⟩
        obtain ⟨⟨left, right⟩, hprefix⟩ := ih.2 head
        change positiveWordAppend left m right = head at hprefix
        exact ⟨(left, (right, last)), by
          change (positiveWordAppend left m right, last) = (head, last)
          rw [hprefix]⟩

/-- Equivalence that splits or concatenates two consecutive nonempty word regions.

The inverse is defined recursively rather than chosen from bijectivity.  Consequently, splitting
an appended word computes, which is important when the word indexes a dependent block space. -/
def positiveWordAppendEquiv (I : Type w) (n : ℕ) :
    (m : ℕ) → PositiveWord I n × PositiveWord I m ≃ PositiveWord I (n + m + 1)
  | 0 => Equiv.refl _
  | m + 1 =>
      (Equiv.prodAssoc (PositiveWord I n) (PositiveWord I m) I).symm.trans
        (Equiv.prodCongr (positiveWordAppendEquiv I n m) (Equiv.refl I))

@[simp] theorem positiveWordAppendEquiv_apply
    (left : PositiveWord I n) (right : PositiveWord I m) :
    positiveWordAppendEquiv I n m (left, right) = positiveWordAppend left m right :=
  by
    induction m with
    | zero => rfl
    | succ m ih =>
        rcases right with ⟨right, last⟩
        change (positiveWordAppendEquiv I n m (left, right), last) =
          (positiveWordAppend left m right, last)
        rw [ih]

/-- Splitting immediately after concatenation recovers both source regions. -/
@[simp] theorem positiveWordAppendEquiv_symm_apply_append
    (left : PositiveWord I n) (right : PositiveWord I m) :
    (positiveWordAppendEquiv I n m).symm (positiveWordAppend left m right) =
      (left, right) := by
  rw [← positiveWordAppendEquiv_apply]
  exact (positiveWordAppendEquiv I n m).symm_apply_apply (left, right)

/-- Letterwise mapping preserves injectivity. -/
theorem positiveWordMap_injective {J : Type*} {f : I → J}
    (hf : Function.Injective f) (n : ℕ) :
    Function.Injective (positiveWordMap f n) := by
  intro left right h
  apply (positiveWordEquiv I n).injective
  funext i
  apply hf
  have hi := congrFun (congrArg (positiveWordEquiv J n) h) i
  simpa [positiveWordEquiv_map, Function.comp_def] using hi

variable {I : Type w} [Fintype I]

/-- Package the leg spaces of a finite indexed direct sum. -/
@[reducible] noncomputable def indexedDirectSumFamily
    (W : I → LegModuleFamily.{u, v} K) : LegModuleFamily.{u, max v w} K where
  Space c := IndexedDirectSumSpace K (fun i ↦ (W i).Space) c

/-- Packaged leg spaces selected by a recursively parenthesized word. -/
@[reducible] def positiveWordFamily (W : I → LegModuleFamily.{u, v} K) :
    (n : ℕ) → PositiveWord I n → LegModuleFamily.{u, v} K
  | 0, i => W i
  | n + 1, q => (positiveWordFamily W n q.1).external (W q.2)

/-- The external product selected by one recursive word. -/
def positiveWordTensor (W : I → LegModuleFamily.{u, v} K)
    (T : ∀ i, Tensor3 K (W i).Space) :
    (n : ℕ) → (q : PositiveWord I n) → Tensor3 K (positiveWordFamily W n q).Space
  | 0, i => T i
  | n + 1, q => external (positiveWordTensor W T n q.1) (T q.2)

omit [Fintype I] in
@[simp] theorem positiveWordTensor_zero (W : I → LegModuleFamily.{u, v} K)
    (T : ∀ i, Tensor3 K (W i).Space) (i : I) :
    positiveWordTensor W T 0 i = T i := rfl

omit [Fintype I] in
@[simp] theorem positiveWordTensor_succ (W : I → LegModuleFamily.{u, v} K)
    (T : ∀ i, Tensor3 K (W i).Space) (n : ℕ) (q : PositiveWord I (n + 1)) :
    positiveWordTensor W T (n + 1) q =
      external (positiveWordTensor W T n q.1) (T q.2) := rfl

omit [Fintype I] in
/-- Reassociate the block spaces selected by two consecutive nonempty words into the block space
selected by their concatenation. -/
def positiveWordFamilyAppendEquiv
    (W : I → LegModuleFamily.{u, v} K) (left : PositiveWord I n) :
    (m : ℕ) → (right : PositiveWord I m) → (c : Leg) →
      TensorProduct K
          ((positiveWordFamily W n left).Space c)
          ((positiveWordFamily W m right).Space c) ≃ₗ[K]
        ((positiveWordFamily W (n + m + 1)
          (positiveWordAppend left m right)).Space c)
  | 0, _right, _c => LinearEquiv.refl K _
  | m + 1, right, c =>
      (TensorProduct.assoc K
        ((positiveWordFamily W n left).Space c)
        ((positiveWordFamily W m right.1).Space c)
        ((W right.2).Space c)).symm.trans
      (TensorProduct.congr
        (positiveWordFamilyAppendEquiv W left m right.1 c)
        (LinearEquiv.refl K ((W right.2).Space c)))

omit [Fintype I] in
/-- The block-space reassociator carries the external product selected by two words to the tensor
selected by their concatenation. -/
theorem map_positiveWordFamilyAppendEquiv_external
    (W : I → LegModuleFamily.{u, v} K)
    (T : ∀ i, Tensor3 K (W i).Space)
    (left : PositiveWord I n) (right : PositiveWord I m) :
    map (fun c ↦
        (positiveWordFamilyAppendEquiv W left m right c).toLinearMap)
      (external (positiveWordTensor W T n left) (positiveWordTensor W T m right)) =
    positiveWordTensor W T (n + m + 1) (positiveWordAppend left m right) := by
  induction m with
  | zero =>
      change map (fun _c ↦ LinearMap.id)
          (external (positiveWordTensor W T n left) (T right)) =
        external (positiveWordTensor W T n left) (T right)
      rw [map_id]
      exact LinearMap.id_apply _
  | succ m ih =>
      rcases right with ⟨right, last⟩
      rw [positiveWordTensor_succ]
      change map (fun c ↦
          ((TensorProduct.assoc K
            ((positiveWordFamily W n left).Space c)
            ((positiveWordFamily W m right).Space c)
            ((W last).Space c)).symm.trans
          (TensorProduct.congr
            (positiveWordFamilyAppendEquiv W left m right c)
            (LinearEquiv.refl K ((W last).Space c)))).toLinearMap)
        (external (positiveWordTensor W T n left)
          (external (positiveWordTensor W T m right) (T last))) = _
      change map (fun c ↦
          (TensorProduct.congr
            (positiveWordFamilyAppendEquiv W left m right c)
            (LinearEquiv.refl K ((W last).Space c))).toLinearMap ∘ₗ
          (TensorProduct.assoc K
            ((positiveWordFamily W n left).Space c)
            ((positiveWordFamily W m right).Space c)
            ((W last).Space c)).symm.toLinearMap)
        (external (positiveWordTensor W T n left)
          (external (positiveWordTensor W T m right) (T last))) = _
      rw [map_comp]
      simp only [LinearMap.comp_apply]
      rw [map_external_assoc_symm]
      change map (fun c ↦ TensorProduct.map
          (positiveWordFamilyAppendEquiv W left m right c).toLinearMap
          (LinearMap.id (R := K) (M := ((W last).Space c))))
        (external
          (external (positiveWordTensor W T n left)
            (positiveWordTensor W T m right))
          (T last)) = _
      rw [map_external, ih]
      rw [map_id]
      rfl

namespace Isomorphic

/-- A positive left-associated external power is canonically isomorphic to the corresponding
Mathlib `TensorPower`.  This bridge lets finite word extraction use the optimized ranks that
define `asymptoticRank`. -/
theorem power_positive_iteratedExternal
    (A : LegModuleFamily.{u, v} K) (T : Tensor3 K A.Space) (n : ℕ) :
    Isomorphic (Tensor.power T (n + 1)) (Tensor.iteratedExternal A T n) := by
  have hone : Isomorphic T (Tensor.powerOne T) :=
    Isomorphic.map T
      (fun c => (powerOneEquiv (K := K) (V := A.Space) c).symm)
  induction n with
  | zero =>
      rw [power_one_eq_powerOne]
      exact hone.symm
  | succ n ih =>
      have hmul : Isomorphic
          (Tensor.external (Tensor.power T (n + 1)) (Tensor.powerOne T))
          (Tensor.powerMul (n + 1) 1
            (Tensor.power T (n + 1)) (Tensor.powerOne T)) :=
        Isomorphic.map _
          (powerMulEquiv (K := K) (V := A.Space) (n + 1) 1)
      change Isomorphic
        (Tensor.powerMul (n + 1) 1
          (Tensor.power T (n + 1)) (Tensor.powerOne T))
        (Tensor.external (Tensor.iteratedExternal A T n) T)
      exact hmul.symm.trans (Isomorphic.external ih hone.symm)

/-- Positive left-associated external powers commute with a permutation of the three tensor legs.

Proof sketch: induct over the additional-factor count.  At each successor, use the induction
hypothesis on the accumulated product, the identity isomorphism on the final factor, and
`permute_external` to move the leg permutation across the external product. -/
theorem iteratedExternal_permute
    (A : LegModuleFamily.{u, v} K) (T : Tensor3 K A.Space)
    (n : ℕ) (e : Orientation) :
    Isomorphic
      (Tensor.iteratedExternal (A.permute e) (Tensor.permute e T) n)
      (Tensor.permute e (Tensor.iteratedExternal A T n)) := by
  induction n with
  | zero => exact Isomorphic.refl _
  | succ n ih =>
      change Isomorphic
        (Tensor.external
          (Tensor.iteratedExternal (A.permute e) (Tensor.permute e T) n)
          (Tensor.permute e T))
        (Tensor.permute e (Tensor.external (Tensor.iteratedExternal A T n) T))
      exact (ih.external (Isomorphic.refl _)).trans
        (Isomorphic.of_eq (Tensor.permute_external e
          (Tensor.iteratedExternal A T n) T).symm)

/-- A positive canonical power of a leg-permuted tensor is isomorphic to the corresponding leg
permutation of the canonical power.

Proof sketch: transport both canonical powers to left-associated positive external products, use
`iteratedExternal_permute`, and transport the target back. -/
theorem power_permute_positive
    (A : LegModuleFamily.{u, v} K) (T : Tensor3 K A.Space)
    (n : ℕ) (e : Orientation) :
    Isomorphic
      (Tensor.power (Tensor.permute e T) (n + 1))
      (Tensor.permute e (Tensor.power T (n + 1))) :=
  (Isomorphic.power_positive_iteratedExternal (A.permute e)
      (Tensor.permute e T) n).trans
    ((Isomorphic.iteratedExternal_permute A T n e).trans
      ((Isomorphic.power_positive_iteratedExternal A T n).permute_legs e).symm)

/-- A positive external power of an indexed direct sum is an actual indexed direct sum of all
word tensors.  Unlike a formal expansion as a sum in one ambient space, this theorem preserves
the independence of the word blocks on every tensor leg. -/
theorem iteratedExternal_indexedDirectSum
    (W : I → LegModuleFamily.{u, v} K)
    (T : ∀ i, Tensor3 K (W i).Space) (n : ℕ) :
    Isomorphic
      (Tensor.iteratedExternal (indexedDirectSumFamily W) (Tensor.indexedDirectSum T) n)
      (Tensor.indexedDirectSum (Tensor.positiveWordTensor W T n)) := by
  induction n with
  | zero =>
      refine ⟨fun _ ↦ LinearEquiv.refl K _, ?_⟩
      change Tensor.map (fun c ↦ LinearMap.id (R := K)
        (M := IndexedDirectSumSpace K (fun i ↦ (W i).Space) c))
          (Tensor.indexedDirectSum T) = _
      rw [Tensor.map_id]
      rfl
  | succ n ih =>
      have hproduct := Isomorphic.external ih
        (Isomorphic.refl (K := K) (Tensor.indexedDirectSum T))
      exact hproduct.trans
        (Isomorphic.external_indexedDirectSum
          (Tensor.positiveWordTensor W T n) T)

end Isomorphic

namespace RankLE

/-- Transport an optimized rank certificate for a canonical positive tensor power to the
left-associated representation used by word-type extraction. -/
theorem iteratedExternal_of_power
    {A : LegModuleFamily.{u, v} K} {T : Tensor3 K A.Space} {n r : ℕ}
    (h : RankLE r (Tensor.power T (n + 1))) :
    RankLE r (Tensor.iteratedExternal A T n) :=
  (RankLE.isomorphic (Isomorphic.power_positive_iteratedExternal A T n)).mp h

end RankLE

namespace BorderRankLE

/-- A border-rank-`r` certificate gives an `r^(n+1)` certificate for the positive external
power with `n + 1` factors. -/
theorem iteratedExternal {A : LegModuleFamily.{u, v} K} {r : ℕ}
    {T : Tensor3 K A.Space} (h : BorderRankLE r T) (n : ℕ) :
    BorderRankLE (r ^ (n + 1)) (Tensor.iteratedExternal A T n) := by
  induction n with
  | zero =>
      simpa [Tensor.iteratedExternal, LegModuleFamily.iterated] using h
  | succ n ih =>
      change BorderRankLE (r ^ (n + 2))
        (Tensor.external (Tensor.iteratedExternal A T n) T)
      simpa [pow_succ] using ih.external h

end BorderRankLE

end AlgebraicComplexity.Tensor
