/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.HoleRepair

set_option autoImplicit false

/-!
# Transporting structure relabelings across partition reindexing

A `PartitionedTensor.StructureRelabeling` records a block-label permutation together with
dependent linear equivalences which preserve the whole partitioned tensor.  This file proves that
such relabelings may be transported in both directions across an exact legwise reindexing.  The
resulting label permutations are exposed as explicit conjugates; no tensor invariance or
constituent isomorphism is assumed beyond the relabeling being transported.

The construction is useful when a partition has a convenient flattened presentation.  One may
build a position relabeling in that presentation and pull it back to the original recursively
grouped block labels.
-/

namespace AlgebraicComplexity.Tensor

universe u v w x y

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type v} {W : ∀ c, B c → Type y}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable [∀ c b, AddCommMonoid (W c b)] [∀ c b, Module K (W c b)]

/-! ## Cancelling an exact reindexing -/

/-- Mapping a constituent by the pointwise casts induced by an address equality transports it to
the constituent at the target address. -/
private theorem map_constituent_cast
    (P : PartitionedTensor (K := K) (A := A) V)
    {source target : BlockAddress A} (h : source = target) :
    map (fun c ↦
        (LinearEquiv.cast (R := K) (M := V c) (congrFun h c)).toLinearMap)
        (P.constituent source) =
      P.constituent target := by
  subst target
  change
    map (fun c ↦ LinearMap.id (R := K) (M := V c (source c)))
        (P.constituent source) =
      P.constituent source
  rw [Tensor.map_id]
  rfl

/-- The inverse local block map, including the dependent cast which identifies
`e⁻¹ (e a)` with `a`. -/
noncomputable def reindexSymmBlockEquiv
    (e : ∀ c, A c ≃ B c)
    (f : ∀ c b, V c ((e c).symm b) ≃ₗ[K] W c b)
    (c : Leg) (a : A c) : W c (e c a) ≃ₗ[K] V c a :=
  (f c (e c a)).symm.trans
    (LinearEquiv.cast (R := K) ((e c).symm_apply_apply a))

/-- Reindexing a partition and then reindexing by the inverse label and block equivalences
recovers the original partitioned tensor exactly. -/
theorem PartitionedTensor.reindex_symm
    (P : PartitionedTensor (K := K) (A := A) V)
    (e : ∀ c, A c ≃ B c)
    (f : ∀ c b, V c ((e c).symm b) ≃ₗ[K] W c b) :
    (P.reindex e f).reindex (fun c ↦ (e c).symm)
        (reindexSymmBlockEquiv e f) = P := by
  classical
  have hinverseAddress :
      (blockAddressCongr (fun c ↦ (e c).symm)).symm = blockAddressCongr e := by
    apply Equiv.ext
    intro address
    funext c
    simp
  apply PartitionedTensor.ext
  · ext address
    simp [PartitionedTensor.reindex, hinverseAddress]
  · funext address
    simp only [PartitionedTensor.reindex_constituent]
    change
      map (fun c ↦ (reindexSymmBlockEquiv e f c (address c)).toLinearMap)
          (map (fun c ↦ (f c (e c (address c))).toLinearMap)
            (P.constituent (fun c ↦ (e c).symm (e c (address c))))) =
        P.constituent address
    have haddress :
        (fun c ↦ (e c).symm (e c (address c))) = address := by
      funext c
      exact (e c).symm_apply_apply (address c)
    rw [← LinearMap.comp_apply, ← map_comp]
    simpa [reindexSymmBlockEquiv, LinearEquiv.trans_symm_cancel_left] using
      map_constituent_cast P haddress

/-! ## Pullback and pushforward -/

namespace PartitionedTensor.StructureRelabeling

variable {P : PartitionedTensor (K := K) (A := A) V}

/-- Dependent block equivalence underlying `ofReindex`.  Its parenthesization follows the two
successive applications of `PartitionedTensor.reindex_trans`. -/
noncomputable def ofReindexBlockEquiv
    (e : ∀ c, A c ≃ B c)
    (f : ∀ c b, V c ((e c).symm b) ≃ₗ[K] W c b)
    (r : (P.reindex e f).StructureRelabeling)
    (c : Leg) (a : A c) :
    V c (((((e c).trans (r.partEquiv c)).trans (e c).symm).symm) a) ≃ₗ[K]
      V c a :=
  ((f c ((r.partEquiv c).symm (e c a))).trans
      (r.blockEquiv c (e c a))).trans
    (reindexSymmBlockEquiv e f c a)

/-- Core pullback when the target partition is definitionally `P.reindex e f`. -/
private noncomputable def ofReindexSelf
    (e : ∀ c, A c ≃ B c)
    (f : ∀ c b, V c ((e c).symm b) ≃ₗ[K] W c b)
    (r : (P.reindex e f).StructureRelabeling) :
    P.StructureRelabeling where
  partEquiv := fun c ↦
    ((e c).trans (r.partEquiv c)).trans (e c).symm
  blockEquiv := ofReindexBlockEquiv e f r
  invariant := by
    classical
    let t : ∀ c, Equiv.Perm (A c) := fun c ↦
      ((e c).trans (r.partEquiv c)).trans (e c).symm
    let h : ∀ c a, V c ((t c).symm a) ≃ₗ[K] V c a := fun c a ↦
      ofReindexBlockEquiv e f r c a
    change P.reindex t h = P
    let er : ∀ c, A c ≃ B c := fun c ↦ (e c).trans (r.partEquiv c)
    let fb : ∀ c b, V c ((er c).symm b) ≃ₗ[K] W c b := fun c b ↦
      (f c ((r.partEquiv c).symm b)).trans (r.blockEquiv c b)
    have hfirst := P.reindex_trans e f r.partEquiv r.blockEquiv
    have hsecond := P.reindex_trans er fb
      (fun c ↦ (e c).symm) (reindexSymmBlockEquiv e f)
    have hlifted := congrArg
      (fun Q ↦ Q.reindex (fun c ↦ (e c).symm) (reindexSymmBlockEquiv e f))
      hfirst
    calc
      P.reindex t h =
          ((P.reindex e f).reindex r.partEquiv r.blockEquiv).reindex
            (fun c ↦ (e c).symm) (reindexSymmBlockEquiv e f) := by
        simpa [t, h, er, fb, ofReindexBlockEquiv] using
          hsecond.symm.trans hlifted.symm
      _ = (P.reindex e f).reindex
          (fun c ↦ (e c).symm) (reindexSymmBlockEquiv e f) := by
        rw [r.invariant]
      _ = P := P.reindex_symm e f

/-- Pull a structure relabeling back across an exact reindex equality.  The source and target
block-label families may live in independent universes. -/
noncomputable def ofReindex
    {Q : PartitionedTensor (K := K) (A := B) W}
    (e : ∀ c, A c ≃ B c)
    (f : ∀ c b, V c ((e c).symm b) ≃ₗ[K] W c b)
    (hPQ : P.reindex e f = Q) (s : Q.StructureRelabeling) :
    P.StructureRelabeling := by
  subst Q
  exact ofReindexSelf e f s

@[simp] theorem ofReindex_partEquiv
    {Q : PartitionedTensor (K := K) (A := B) W}
    (e : ∀ c, A c ≃ B c)
    (f : ∀ c b, V c ((e c).symm b) ≃ₗ[K] W c b)
    (hPQ : P.reindex e f = Q) (s : Q.StructureRelabeling)
    (c : Leg) :
    (ofReindex e f hPQ s).partEquiv c =
      (e c).trans ((s.partEquiv c).trans (e c).symm) := by
  subst Q
  change ((e c).trans (s.partEquiv c)).trans (e c).symm = _
  apply Equiv.ext
  intro a
  rfl

/-- Push a structure relabeling forward across an exact reindex equality.  This is the inverse-
reindex specialization of `ofReindex`; the dependent inverse block transport is supplied by
`reindexSymmBlockEquiv`. -/
noncomputable def toReindex
    {Q : PartitionedTensor (K := K) (A := B) W}
    (e : ∀ c, A c ≃ B c)
    (f : ∀ c b, V c ((e c).symm b) ≃ₗ[K] W c b)
    (hPQ : P.reindex e f = Q) (r : P.StructureRelabeling) :
    Q.StructureRelabeling := by
  subst Q
  exact ofReindex (fun c ↦ (e c).symm)
    (reindexSymmBlockEquiv e f) (P.reindex_symm e f) r

@[simp] theorem toReindex_partEquiv
    {Q : PartitionedTensor (K := K) (A := B) W}
    (e : ∀ c, A c ≃ B c)
    (f : ∀ c b, V c ((e c).symm b) ≃ₗ[K] W c b)
    (hPQ : P.reindex e f = Q) (r : P.StructureRelabeling)
    (c : Leg) :
    (toReindex e f hPQ r).partEquiv c =
      (e c).symm.trans ((r.partEquiv c).trans (e c)) := by
  subst Q
  change
    (ofReindex (fun c ↦ (e c).symm)
      (reindexSymmBlockEquiv e f) (P.reindex_symm e f) r).partEquiv c = _
  simp only [ofReindex_partEquiv, Equiv.symm_symm]

end PartitionedTensor.StructureRelabeling
end AlgebraicComplexity.Tensor
