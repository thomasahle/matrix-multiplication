/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.AggregateMarkedHashing
import AlgebraicComplexity.MatrixMultiplication.ModeledMarkedHashingModel

set_option autoImplicit false

/-!
# Product constructions for native marked-hashing models

This module concatenates a finite heterogeneous family of `PartitionModel`s over a sigma word.
The adapter from the heavier partitioned-power hashing API lives separately in
`ModeledMarkedHashingPartitionedPower`, so clients of this generic product construction do not
pay that import or elaboration cost.

The construction is the heterogeneous finite-family form of the block products used in
[coppersmith1990matrix, Sections 6--7].

## Reference

- [coppersmith1990matrix] Don Coppersmith and Shmuel Winograd,
  *Matrix Multiplication via Arithmetic Progressions*.
-/

namespace AlgebraicComplexity

universe u v w

namespace ProgressionHash.LegalTriple.PartitionModel

variable {R : Type u} [Field R]
variable {target : R}

/-- Restrict an aggregate legal triple to one sigma component. -/
def aggregateFactor
    {E : Type v} {ι : E → Type w}
    (triple : LegalTriple R (Sigma ι) target) (e : E) :
    LegalTriple R (ι e) target where
  xIndex i := triple.xIndex ⟨e, i⟩
  yIndex i := triple.yIndex ⟨e, i⟩
  zIndex i := triple.zIndex ⟨e, i⟩
  legal i := triple.legal ⟨e, i⟩

@[simp] theorem aggregateFactor_aggregate
    {E : Type v} [Fintype E] [DecidableEq E]
    {ι : E → Type w} [∀ e, Fintype (ι e)]
    (factors : ∀ e, LegalTriple R (ι e) target) (e : E) :
    aggregateFactor (aggregate factors) e = factors e := by
  apply LegalTriple.ext <;> rfl

/-- Product of native partition models, represented on the sigma-concatenated hashing word.

The native block on each tensor leg is a product of the factor blocks, while the hashing word is
their concatenation over `Sigma ι`. -/
noncomputable def aggregateModel
    {E : Type v} [Fintype E] [DecidableEq E]
    {ι : E → Type w} [∀ e, Fintype (ι e)]
    {A : E → Tensor.Leg → Type w}
    (ambient : ∀ e, Finset (LegalTriple R (ι e) target))
    (models : ∀ e, ProgressionHash.LegalTriple.PartitionModel
      (R := R) (ι := ι e) (target := target) (A := A e) (ambient e)) :
    ProgressionHash.LegalTriple.PartitionModel
      (R := R) (ι := Sigma ι) (target := target)
      (A := fun c ↦ ∀ e, A e c) (aggregateTargets ambient) where
  encode c blocks position := (models position.1).encode c (blocks position.1) position.2
  address triple c e := (models e).address (aggregateFactor triple e) c
  encode_address triple htriple c := by
    obtain ⟨factors, hfactors, rfl⟩ := (mem_aggregateTargets ambient triple).mp htriple
    funext position
    rcases position with ⟨e, i⟩
    simpa only [aggregateFactor_aggregate, aggregate_legIndex_apply] using
      congrFun ((models e).encode_address (factors e) (hfactors e) c) i

/-- Product model followed by an arbitrary legwise relabelling of the product block alphabet.

This is the structural adapter used when the native target partition stores concatenated words
rather than dependent functions of factor blocks. -/
noncomputable def aggregateModelReindex
    {E : Type v} [Fintype E] [DecidableEq E]
    {ι : E → Type w} [∀ e, Fintype (ι e)]
    {A : E → Tensor.Leg → Type w} {B : Tensor.Leg → Type w}
    (ambient : ∀ e, Finset (LegalTriple R (ι e) target))
    (models : ∀ e, ProgressionHash.LegalTriple.PartitionModel
      (R := R) (ι := ι e) (target := target) (A := A e) (ambient e))
    (join : ∀ c, (∀ e, A e c) ≃ B c) :
    ProgressionHash.LegalTriple.PartitionModel
      (R := R) (ι := Sigma ι) (target := target)
      (A := B) (aggregateTargets ambient) :=
  (aggregateModel ambient models).reindex join

end ProgressionHash.LegalTriple.PartitionModel

end AlgebraicComplexity
