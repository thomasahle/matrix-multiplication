/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Partitioned

/-!
# Shared-leg C-tensor core

A C-tensor is a finite family of constituents with independent X and Y blocks and one shared Z
block.  This lightweight module defines its block spaces, diagonal support, and partitioned
realization.  Cyclic products, the antidiagonal degeneration, and counting live in later modules,
so clients that only need the shared-leg realization do not load their tactic-heavy arithmetic.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

namespace CTensor

/-- Block labels of an `h`-constituent C-tensor: X and Y have one block per constituent, while Z
has one shared block. -/
abbrev BlockIndex (h : ℕ) : Leg → Type
  | .X => Fin h
  | .Y => Fin h
  | .Z => Unit

/-- The C-tensor block labels have decidable equality on every leg. -/
instance (h : ℕ) (c : Leg) : DecidableEq (BlockIndex h c) := by
  cases c <;> simp only [BlockIndex] <;> infer_instance

/-- The C-tensor block labels are finite on every leg. -/
instance (h : ℕ) (c : Leg) : Fintype (BlockIndex h c) := by
  cases c <;> simp only [BlockIndex] <;> infer_instance

/-- Uniform block spaces for a C-tensor.  The label selects a copy of a space but does not alter
the space's type. -/
abbrev BlockSpace (X Y Z : Type v) (h : ℕ) :
    ∀ c, BlockIndex h c → Type v
  | .X, _ => X
  | .Y, _ => Y
  | .Z, _ => Z

/-- Additive structure on a uniform C-tensor block is inherited from its underlying leg space. -/
instance blockSpaceAddCommMonoid
    {X Y Z : Type v} [AddCommMonoid X] [AddCommMonoid Y] [AddCommMonoid Z]
    (h : ℕ) (c : Leg) (a : BlockIndex h c) : AddCommMonoid (BlockSpace X Y Z h c a) := by
  cases c <;> simp only [BlockSpace] <;> infer_instance

/-- Scalar multiplication on a uniform C-tensor block is inherited from its underlying leg
space. -/
instance blockSpaceModule
    {K : Type u} [Semiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    (h : ℕ) (c : Leg) (a : BlockIndex h c) : Module K (BlockSpace X Y Z h c a) := by
  cases c <;> simp only [BlockSpace] <;> infer_instance

/-- The common three constituent spaces of a uniform C-tensor. -/
abbrev ConstituentSpace (X Y Z : Type v) : Leg → Type v
  | .X => X
  | .Y => Y
  | .Z => Z

/-- Additive structure on the common constituent family is inherited legwise. -/
instance constituentSpaceAddCommMonoid
    {X Y Z : Type v} [AddCommMonoid X] [AddCommMonoid Y] [AddCommMonoid Z]
    (c : Leg) : AddCommMonoid (ConstituentSpace X Y Z c) := by
  cases c <;> simp only [ConstituentSpace] <;> infer_instance

/-- Scalar multiplication on the common constituent family is inherited legwise. -/
instance constituentSpaceModule
    {K : Type u} [Semiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    (c : Leg) : Module K (ConstituentSpace X Y Z c) := by
  cases c <;> simp only [ConstituentSpace] <;> infer_instance

/-- Retype the common constituent spaces as the blocks at an arbitrary C-tensor address.  Since
the block-space type ignores its label, these equivalences are legwise identities. -/
noncomputable def constituentToBlockEquiv
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {h : ℕ} (s : BlockAddress (BlockIndex h)) : ∀ c,
    ConstituentSpace X Y Z c ≃ₗ[K] BlockSpace X Y Z h c (s c) := by
  intro c
  cases c <;> exact LinearEquiv.refl K _

/-- Linear-map form of `constituentToBlockEquiv`. -/
noncomputable def constituentToBlock
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {h : ℕ} (s : BlockAddress (BlockIndex h)) : ∀ c,
    ConstituentSpace X Y Z c →ₗ[K] BlockSpace X Y Z h c (s c) :=
  fun c ↦ (constituentToBlockEquiv s c).toLinearMap

/-- The block address occupied by constituent `i`: its X and Y labels are `i`, and its Z label is
the unique shared label. -/
def address {h : ℕ} (i : Fin h) : BlockAddress (BlockIndex h) :=
  ofLegs i i ()

/-- Distinct C-tensor constituents have distinct full block addresses. -/
def addressEmbedding (h : ℕ) : Fin h ↪ BlockAddress (BlockIndex h) where
  toFun := address
  inj' := by
    intro i j hij
    exact congrFun hij .X

/-- The diagonal support of the uniform `h`-constituent C-tensor. -/
def support (h : ℕ) : Finset (BlockAddress (BlockIndex h)) :=
  Finset.univ.map (addressEmbedding h)

/-- A C-tensor certificate built from `h` uniformly typed constituents.  Values of the
constituent family away from the recorded diagonal support are irrelevant to realization. -/
noncomputable def partitioned
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {h : ℕ} (T : Fin h → Tensor3 K (ConstituentSpace X Y Z)) :
    PartitionedTensor (K := K) (A := BlockIndex h) (BlockSpace X Y Z h) where
  support := support h
  constituent s := map (constituentToBlock s) (T (s .X))

/-- The C-tensor support has exactly `h` addresses. -/
@[simp] theorem card_support (h : ℕ) : (support h).card = h := by
  simp [support]

/-- A C-tensor support address is exactly `address i` for a unique index `i`. -/
theorem mem_support_iff {h : ℕ} (s : BlockAddress (BlockIndex h)) :
    s ∈ support h ↔ ∃ i : Fin h, address i = s := by
  constructor
  · intro hs
    rcases Finset.mem_map.mp hs with ⟨i, _, hi⟩
    exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- At a supported address, the recorded constituent is canonically isomorphic to the source
constituent carrying that index. -/
theorem partitioned_constituent_address_isomorphic
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {h : ℕ} (T : Fin h → Tensor3 K (ConstituentSpace X Y Z)) (i : Fin h) :
    Isomorphic (T i) ((partitioned T).constituent (address i)) := by
  refine ⟨constituentToBlockEquiv (K := K) (X := X) (Y := Y) (Z := Z) (address i), ?_⟩
  rfl

end CTensor

end AlgebraicComplexity
