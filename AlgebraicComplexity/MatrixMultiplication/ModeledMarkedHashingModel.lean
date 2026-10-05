/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.MarkedLegwiseHashingExtraction

set_option autoImplicit false

/-!
# Native partition models for marked hashing

The legal-triple hashing API labels a tensor leg by a field-valued word. Concrete tensor powers
usually retain their native block labels and merely encode them for hashing. This module records
that encoding and transports finite support and local-filter facts to the native partition
labels.  The two tensor-semantic isolation corollaries live in
`ModeledMarkedHashingIsolation`, and extraction is kept in `ModeledMarkedHashingExtraction`, so
the combinatorial dictionary remains cheap to import.

This API abstracts the native block labels and affine filtering in
[coppersmith1990matrix, Sections 5--7].

## Reference

- [coppersmith1990matrix] Don Coppersmith and Shmuel Winograd,
  *Matrix Multiplication via Arithmetic Progressions*.
-/

namespace AlgebraicComplexity

universe u v w x

namespace ProgressionHash.LegalTriple

variable {R : Type u} [Field R]
variable {ι : Type v} [Fintype ι]
variable {target : R}
variable {A : Tensor.Leg → Type w}
variable {domain : Finset (LegalTriple R ι target)}

/-- A representation of legal triples by the native blocks of a partitioned tensor.

The only coherence law says that hashing a modeled block reads exactly the legal triple's word
on that leg. It implies injectivity of `address`, because all three legal-triple words determine
the triple. -/
structure PartitionModel (domain : Finset (LegalTriple R ι target)) where
  encode : ∀ c, A c → ι → R
  address : LegalTriple R ι target → ∀ c, A c
  encode_address : ∀ triple ∈ domain, ∀ c,
    encode c (address triple c) = triple.legIndex c

namespace PartitionModel

/-- Relabel every native block alphabet by a legwise equivalence.  The represented legal triples
and their hashing words are unchanged. -/
def reindex
    {B : Tensor.Leg → Type x}
    (model : PartitionModel (R := R) (ι := ι) (target := target) (A := A) domain)
    (e : ∀ c, A c ≃ B c) :
    PartitionModel (R := R) (ι := ι) (target := target) (A := B) domain where
  encode c block := model.encode c ((e c).symm block)
  address triple c := e c (model.address triple c)
  encode_address triple htriple c := by
    simpa using model.encode_address triple htriple c

/-- Restrict a native model to a smaller represented legal-target family. -/
def onSubset
    (model : PartitionModel (R := R) (ι := ι) (target := target) (A := A) domain)
    {smaller : Finset (LegalTriple R ι target)} (hsmaller : smaller ⊆ domain) :
    PartitionModel (R := R) (ι := ι) (target := target) (A := A) smaller where
  encode := model.encode
  address := model.address
  encode_address triple htriple := model.encode_address triple (hsmaller htriple)

/-- Transport a native model across an equality of represented finite families. -/
def castDomain
    (model : PartitionModel (R := R) (ι := ι) (target := target) (A := A) domain)
    {other : Finset (LegalTriple R ι target)} (h : domain = other) :
    PartitionModel (R := R) (ι := ι) (target := target) (A := A) other := by
  subst other
  exact model

/-- Modeled block addresses determine their legal triples inside the represented domain. -/
theorem address_injectiveOn (model : PartitionModel (R := R) (ι := ι)
    (target := target) (A := A) domain) :
    Set.InjOn model.address domain := by
  intro left hleft right hright haddress
  apply LegalTriple.ext <;> funext i
  · calc
      left.xIndex i = model.encode .X (model.address left .X) i :=
        (congrFun (model.encode_address left hleft .X) i).symm
      _ = model.encode .X (model.address right .X) i :=
        congrArg (fun block ↦ model.encode .X block i) (congrFun haddress .X)
      _ = right.xIndex i := congrFun (model.encode_address right hright .X) i
  · calc
      left.yIndex i = model.encode .Y (model.address left .Y) i :=
        (congrFun (model.encode_address left hleft .Y) i).symm
      _ = model.encode .Y (model.address right .Y) i :=
        congrArg (fun block ↦ model.encode .Y block i) (congrFun haddress .Y)
      _ = right.yIndex i := congrFun (model.encode_address right hright .Y) i
  · calc
      left.zIndex i = model.encode .Z (model.address left .Z) i :=
        (congrFun (model.encode_address left hleft .Z) i).symm
      _ = model.encode .Z (model.address right .Z) i :=
        congrArg (fun block ↦ model.encode .Z block i) (congrFun haddress .Z)
      _ = right.zIndex i := congrFun (model.encode_address right hright .Z) i

/-- Image of a legal-target family in the native partition block labels. -/
noncomputable def modeledTargets
    (model : PartitionModel (R := R) (ι := ι) (target := target) (A := A) domain)
    (targets : Finset (LegalTriple R ι target)) :
    Finset (∀ c, A c) := by
  classical
  exact targets.image model.address

@[simp] theorem card_modeledTargets
    (model : PartitionModel (R := R) (ι := ι) (target := target) (A := A) domain)
    (targets : Finset (LegalTriple R ι target)) (htargets : targets ⊆ domain) :
    (model.modeledTargets targets).card = targets.card := by
  classical
  unfold modeledTargets
  exact Finset.card_image_of_injOn (model.address_injectiveOn.mono htargets)

/-- Modeled addresses of the marked targets isolated by one affine seed. -/
noncomputable def modeledMarkedLegwiseIsolatedAddresses
    (model : PartitionModel (R := R) (ι := ι) (target := target) (A := A) domain)
    (marked : Finset (LegalTriple R ι target)) (B : Finset R)
    (seed : ProgressionHash.Seed R ι) : Finset (∀ c, A c) :=
  model.modeledTargets (markedLegwiseIsolatedTargets domain marked B seed)

@[simp] theorem card_modeledMarkedLegwiseIsolatedAddresses
    (model : PartitionModel (R := R) (ι := ι) (target := target) (A := A) domain)
    (marked : Finset (LegalTriple R ι target)) (hmarked : marked ⊆ domain)
    (B : Finset R)
    (seed : ProgressionHash.Seed R ι) :
    (model.modeledMarkedLegwiseIsolatedAddresses marked B seed).card =
      (markedLegwiseIsolatedTargets domain marked B seed).card := by
  exact model.card_modeledTargets _
    ((markedLegwiseIsolatedTargets_subset_marked domain marked B seed).trans hmarked)

/-- Modeled addresses surviving only the three affine hash tests. -/
noncomputable def modeledFilteredAddresses
    (model : PartitionModel (R := R) (ι := ι) (target := target) (A := A) domain)
    (B : Finset R)
    (seed : ProgressionHash.Seed R ι) : Finset (∀ c, A c) :=
  model.modeledTargets (filteredTargets domain B seed)

/-- Marked isolated modeled addresses survive the ordinary hash filter. -/
theorem modeledMarked_subset_modeledFiltered [NeZero (2 : R)]
    (model : PartitionModel (R := R) (ι := ι) (target := target) (A := A) domain)
    (marked : Finset (LegalTriple R ι target))
    (hmarked : marked ⊆ domain) (B : Finset R)
    (seed : ProgressionHash.Seed R ι) :
    model.modeledMarkedLegwiseIsolatedAddresses marked B seed ⊆
      model.modeledFilteredAddresses B seed := by
  classical
  exact Finset.image_mono model.address
    (markedLegwiseIsolatedTargets_subset_filteredTargets
      domain marked hmarked B seed)

/-- Hash membership read directly from a native partition block through its field-word
encoding. -/
noncomputable def hashKeepBlock
    (model : PartitionModel (R := R) (ι := ι) (target := target) (A := A) domain)
    (B : Finset R) (seed : ProgressionHash.Seed R ι) : ∀ c, A c → Prop
  | .X => fun block ↦ seed.xHash (model.encode .X block) ∈ B
  | .Y => fun block ↦ seed.yHash (model.encode .Y block) ∈ B
  | .Z => fun block ↦ seed.zHash target (model.encode .Z block) ∈ B

noncomputable local instance
    (model : PartitionModel (R := R) (ι := ι) (target := target) (A := A) domain)
    (B : Finset R) (seed : ProgressionHash.Seed R ι)
    (c : Tensor.Leg) (block : A c) :
    Decidable (model.hashKeepBlock B seed c block) :=
  Classical.propDecidable _

/-- A modeled legal triple passes the three block-local tests exactly when it passes the bundled
affine hash filter. -/
theorem hashKeepBlock_address_iff
    (model : PartitionModel (R := R) (ι := ι) (target := target) (A := A) domain)
    (B : Finset R) (seed : ProgressionHash.Seed R ι)
    (triple : LegalTriple R ι target) (htriple : triple ∈ domain) :
    (∀ c, model.hashKeepBlock B seed c (model.address triple c)) ↔
      SurvivesHashFilter (B : Set R) seed triple := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa [hashKeepBlock, model.encode_address triple htriple] using h .X
    · simpa [hashKeepBlock, model.encode_address triple htriple] using h .Y
    · simpa [hashKeepBlock, model.encode_address triple htriple] using h .Z
  · rintro ⟨hx, hy, hz⟩ c
    cases c with
    | X => simpa [hashKeepBlock, model.encode_address triple htriple] using hx
    | Y => simpa [hashKeepBlock, model.encode_address triple htriple] using hy
    | Z => simpa [hashKeepBlock, model.encode_address triple htriple] using hz

/-- Leg-local filtering of all modeled ambient targets is exactly the modeled bundled hash
filter. -/
theorem filter_modeledTargets_hashKeepBlock_eq
    (model : PartitionModel (R := R) (ι := ι) (target := target) (A := A) domain)
    (B : Finset R)
    (seed : ProgressionHash.Seed R ι) :
    (model.modeledTargets domain).filter
        (fun address ↦ ∀ c, model.hashKeepBlock B seed c (address c)) =
      model.modeledFilteredAddresses B seed := by
  classical
  ext address
  constructor
  · intro haddress
    obtain ⟨hambient, hkeep⟩ := Finset.mem_filter.mp haddress
    unfold modeledTargets at hambient
    obtain ⟨triple, htriple, rfl⟩ := Finset.mem_image.mp hambient
    unfold modeledFilteredAddresses modeledTargets filteredTargets
    apply Finset.mem_image.mpr
    refine ⟨triple, Finset.mem_filter.mpr ⟨htriple, ?_⟩, rfl⟩
    exact (model.hashKeepBlock_address_iff B seed triple htriple).mp hkeep
  · intro haddress
    unfold modeledFilteredAddresses modeledTargets filteredTargets at haddress
    obtain ⟨triple, htriple, rfl⟩ := Finset.mem_image.mp haddress
    obtain ⟨hambient, hsurvives⟩ := Finset.mem_filter.mp htriple
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨triple, hambient, rfl⟩, ?_⟩
    exact (model.hashKeepBlock_address_iff B seed triple hambient).mpr hsurvives

end PartitionModel
end ProgressionHash.LegalTriple
end AlgebraicComplexity
