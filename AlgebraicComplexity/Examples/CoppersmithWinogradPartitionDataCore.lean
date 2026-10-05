/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSupportCore
import AlgebraicComplexity.Tensor.PartitionedCore

/-!
# Exact finite partition data for the Coppersmith--Winograd tensor

This module defines the CW block spaces, explicit six-support constituents, and their partitioned
tensor certificate.  It deliberately excludes the direct-sum equivalence realizing that partition
inside the usual CW coordinate space; that semantic layer lives in
`CoppersmithWinogradPartitionCore` and re-exports this file.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- Coordinate indices carried by one CW partition block. -/
def CWBlockIndex (q : ℕ) : CWBlock → Type
  | .zero => Unit
  | .middle => Fin q
  | .last => Unit

instance (q : ℕ) (a : CWBlock) : Fintype (CWBlockIndex q a) := by
  cases a <;> simp [CWBlockIndex] <;> infer_instance

instance (q : ℕ) (a : CWBlock) : DecidableEq (CWBlockIndex q a) := by
  cases a <;> simp [CWBlockIndex] <;> infer_instance

/-- The disjoint union of the three block index sets is the original CW coordinate index. -/
def cwBlockIndexEquiv (q : ℕ) : (Σ a : CWBlock, CWBlockIndex q a) ≃ CWIndex q where
  toFun
    | ⟨.zero, _⟩ => .zero
    | ⟨.middle, i⟩ => .middle i
    | ⟨.last, _⟩ => .last
  invFun
    | .zero => ⟨.zero, ()⟩
    | .middle i => ⟨.middle, i⟩
    | .last => ⟨.last, ()⟩
  left_inv x := by
    rcases x with ⟨a, i⟩
    cases a
    · cases i
      rfl
    · rfl
    · cases i
      rfl
  right_inv x := by cases x <;> rfl

/-- Vector space carried by block `a` on a CW tensor leg. -/
abbrev CWPartitionBlockSpace (K : Type u) (q : ℕ) (_c : Leg) (a : CWBlock) :=
  CWBlockIndex q a → K

/-- Standard coordinate vector inside one CW block. -/
def cwBlockBasis (K : Type u) [Zero K] [One K]
    (q : ℕ) (a : CWBlock) (i : CWBlockIndex q a) : CWBlockIndex q a → K :=
  Pi.single i 1

@[simp] theorem cwBlockBasis_apply (K : Type u) [Zero K] [One K]
    (q : ℕ) (a : CWBlock) (i j : CWBlockIndex q a) :
    cwBlockBasis K q a i j = if j = i then 1 else 0 := by
  exact Pi.single_apply i 1 j

section

variable (K : Type u) [CommRing K]
variable (q : ℕ)

/-- Constituent associated to three explicit block labels, with zero outside the six-address
support. -/
noncomputable def cwConstituentOfBlocks (x y z : CWBlock) :
    Tensor3 K (fun c ↦ CWPartitionBlockSpace K q c
      (ofLegs (V := fun _ : Leg ↦ CWBlock) x y z c)) :=
  match x, y, z with
  | .last, .zero, .zero => pure (K := K) (ofLegs
      (cwBlockBasis K q .last ())
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .zero ()))
  | .zero, .last, .zero => pure (K := K) (ofLegs
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .last ())
      (cwBlockBasis K q .zero ()))
  | .zero, .zero, .last => pure (K := K) (ofLegs
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .last ()))
  | .zero, .middle, .middle => ∑ i : Fin q, pure (K := K) (ofLegs
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .middle i)
      (cwBlockBasis K q .middle i))
  | .middle, .zero, .middle => ∑ i : Fin q, pure (K := K) (ofLegs
      (cwBlockBasis K q .middle i)
      (cwBlockBasis K q .zero ())
      (cwBlockBasis K q .middle i))
  | .middle, .middle, .zero => ∑ i : Fin q, pure (K := K) (ofLegs
      (cwBlockBasis K q .middle i)
      (cwBlockBasis K q .middle i)
      (cwBlockBasis K q .zero ()))
  | _, _, _ => 0

/-- Transport a typed constituent along equality of its three block labels. -/
noncomputable def cwTransportConstituent {s t : CWBlockAddress} (h : s = t)
    (T : Tensor3 K (fun c ↦ CWPartitionBlockSpace K q c (s c))) :
    Tensor3 K (fun c ↦ CWPartitionBlockSpace K q c (t c)) := by
  subst t
  exact T

@[simp] theorem cwTransportConstituent_self {s : CWBlockAddress} (h : s = s)
    (T : Tensor3 K (fun c ↦ CWPartitionBlockSpace K q c (s c))) :
    cwTransportConstituent K q h T = T := by
  have hh : h = rfl := Subsingleton.elim _ _
  rw [hh]
  rfl

/-- Extend the six supported constituents by zero to every ambient block address. -/
noncomputable def cwPartitionConstituent (s : CWBlockAddress) :
    Tensor3 K (fun c ↦ CWPartitionBlockSpace K q c (s c)) :=
  cwTransportConstituent K q (ofLegs_eta s)
    (cwConstituentOfBlocks K q (s .X) (s .Y) (s .Z))

/-- The typed constituent at one of the six supported CW block addresses. -/
noncomputable def cwSupportedConstituent (s : cwBlockSupport) :
    Tensor3 K (fun c ↦ CWPartitionBlockSpace K q c (s.1 c)) :=
  cwPartitionConstituent K q s.1

@[simp] theorem cwPartitionConstituent_ofLegs (x y z : CWBlock) :
    cwPartitionConstituent K q
        (ofLegs (V := fun _ : Leg ↦ CWBlock) x y z) =
      cwConstituentOfBlocks K q x y z := by
  unfold cwPartitionConstituent
  change cwTransportConstituent K q
    (_ : ofLegs (V := fun _ : Leg ↦ CWBlock) x y z = ofLegs x y z) _ = _
  apply cwTransportConstituent_self

/-- The full CW tensor as a typed six-constituent partitioned tensor. -/
noncomputable def cwPartitionedTensor :
    PartitionedTensor (K := K) (A := fun _ : Leg ↦ CWBlock)
      (CWPartitionBlockSpace K q) where
  support := cwBlockSupport
  constituent := cwPartitionConstituent K q

@[simp] theorem cwPartitionedTensor_constituent (s : cwBlockSupport) :
    (cwPartitionedTensor K q).constituent s.1 = cwSupportedConstituent K q s := by
  rfl

end

end AlgebraicComplexity.Examples
