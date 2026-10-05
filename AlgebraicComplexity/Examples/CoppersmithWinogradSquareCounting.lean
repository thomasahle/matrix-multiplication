/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSquare
import AlgebraicComplexity.MatrixMultiplication.MarkedPartitionedPowerHashing
import AlgebraicComplexity.Tensor.TypeExtraction

/-!
# Exact global types for the Coppersmith--Winograd tensor square

The coarsened square has fifteen addresses in four permutation classes: `004`, `013`, `022`, and
`112`, with orbit sizes `3, 6, 3, 3`.  This module records a symmetric integral joint profile
with one count per class and proves the five-coordinate marginal formula from the 1990 paper.

It then distinguishes the exact marked joint type from the ambient family determined only by
those three marginals.  This distinction is the source of the classical combination-loss factor
and is why the marked hashing API is required downstream.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

/-- Equality of square addresses is coordinatewise equality of their three displayed degrees. -/
@[simp] theorem cwSquareAddress_eq_iff (x y z x' y' z' : Fin 5) :
    cwSquareAddress x y z = cwSquareAddress x' y' z' ↔
      x = x' ∧ y = y' ∧ z = z' := by
  constructor
  · intro h
    exact ⟨congrFun h .X, congrFun h .Y, congrFun h .Z⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- The three orientations of constituent class `004`. -/
def cwSquare004Orbit : Finset CWSquareAddress :=
  {cwSquareAddress 0 0 4, cwSquareAddress 0 4 0, cwSquareAddress 4 0 0}

/-- The six orientations of constituent class `013`. -/
def cwSquare013Orbit : Finset CWSquareAddress :=
  {cwSquareAddress 0 1 3, cwSquareAddress 0 3 1,
    cwSquareAddress 1 0 3, cwSquareAddress 1 3 0,
    cwSquareAddress 3 0 1, cwSquareAddress 3 1 0}

/-- The three orientations of constituent class `022`. -/
def cwSquare022Orbit : Finset CWSquareAddress :=
  {cwSquareAddress 0 2 2, cwSquareAddress 2 0 2, cwSquareAddress 2 2 0}

/-- The three orientations of the exceptional constituent class `112`. -/
def cwSquare112Orbit : Finset CWSquareAddress :=
  {cwSquareAddress 1 1 2, cwSquareAddress 1 2 1, cwSquareAddress 2 1 1}

/-- The four permutation classes are pairwise disjoint and exhaust the coarsened square support. -/
theorem cwSquareSupport_eq_classOrbits :
    cwSquareSupport =
      cwSquare004Orbit ∪ cwSquare013Orbit ∪ cwSquare022Orbit ∪ cwSquare112Orbit := by
  rw [cwSquareSupport_eq_antidiagonal]
  decide

/-- Convenient finite alphabet of the fifteen supported square addresses. -/
abbrev CWSquareSupport := {s // s ∈ cwSquareSupport}

/-- Embed one of the five square-block degrees into a coefficient field. -/
def cwSquareFieldValue {R : Type*} [NatCast R] (i : Fin 5) : R := i.val

/-- The degree-four antidiagonal is a constant-sum hashing support over any field in which the
five degree labels remain distinct.  Keeping injectivity explicit makes the characteristic
restriction precise; the final finite-field client will discharge it by choosing modulus at
least five. -/
def cwSquarePartitionHashEncoding {R : Type*} [Field R]
    (hinjective : Function.Injective (cwSquareFieldValue (R := R))) :
    PartitionHashEncoding (R := R) cwSquareSupport where
  encode _ := cwSquareFieldValue
  target := 4
  support_nonempty := ⟨cwSquare004, by
    rw [cwSquareSupport_eq_antidiagonal]
    decide⟩
  encode_injective _ := hinjective
  legal s hs := by
    have hsum := cwSquareAntidiagonal_degree_sum s (by
      rwa [← cwSquareSupport_eq_antidiagonal])
    unfold cwSquareFieldValue
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      congrArg (fun n : ℕ ↦ (n : R)) hsum

/-- Symmetric per-address count before multiplying by the proportional repetition `k`. -/
def cwSquareClassCount (a b c d : ℕ) (s : CWSquareAddress) : ℕ :=
  if s ∈ cwSquare004Orbit then a
  else if s ∈ cwSquare013Orbit then b
  else if s ∈ cwSquare022Orbit then c
  else if s ∈ cwSquare112Orbit then d
  else 0

/-- Integral marked joint profile at proportional repetition `k`. -/
def cwSquareNaturalType (a b c d k : ℕ) : CWSquareSupport → ℕ :=
  fun s ↦ cwSquareClassCount a b c d s.1 * k

/-- Total number of square constituents in one unscaled symmetric profile. -/
def cwSquareStride (a b c d : ℕ) : ℕ := 3 * a + 6 * b + 3 * c + 3 * d

/-- The symmetric joint profile has total mass
`(3a + 6b + 3c + 3d)k`.

Proof sketch: enumerate the fifteen antidiagonal addresses and count the four permutation orbits. -/
theorem sum_cwSquareNaturalType (a b c d k : ℕ) :
    (∑ s : CWSquareSupport, cwSquareNaturalType a b c d k s) =
      cwSquareStride a b c d * k := by
  calc
    (∑ s : CWSquareSupport, cwSquareNaturalType a b c d k s) =
        ∑ s ∈ cwSquareSupport, cwSquareClassCount a b c d s * k :=
      (Finset.sum_subtype cwSquareSupport (fun _ ↦ Iff.rfl)
        (fun s ↦ cwSquareClassCount a b c d s * k)).symm
    _ = cwSquareStride a b c d * k := by
      rw [cwSquareSupport_eq_antidiagonal]
      unfold cwSquareAntidiagonal
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton]
      simp [cwSquareClassCount, cwSquare004Orbit, cwSquareAddress_eq_iff,
        cwSquare013Orbit, cwSquare022Orbit, cwSquare112Orbit, cwSquareStride]
      ring

/-- The five common one-leg marginal counts of a symmetric square profile.

These are the paper's values
`A₀=2a+2b+c`, `A₁=2b+2d`, `A₂=2c+d`, `A₃=2b`, and `A₄=a`, scaled by `k`. -/
def cwSquareMarginalType (a b c d k : ℕ) : Fin 5 → ℕ
  | 0 => (2 * a + 2 * b + c) * k
  | 1 => (2 * b + 2 * d) * k
  | 2 => (2 * c + d) * k
  | 3 => (2 * b) * k
  | 4 => a * k

/-- Pushing the joint profile to any one tensor leg gives the same five-coordinate marginal.

Proof sketch: enumerate the fifteen addresses.  Symmetry makes the three leg cases identical up
to permutation; each coordinate then reduces to the displayed orbit count. -/
theorem cwSquare_mappedType_eq_marginal
    (a b c d k : ℕ) (leg : Leg) :
    WordType.mappedType (fun s : CWSquareSupport ↦ s.1 leg)
      (cwSquareNaturalType a b c d k) = cwSquareMarginalType a b c d k := by
  funext block
  unfold WordType.mappedType WordType.letterFiber
  simp only [Finset.sum_filter]
  change (∑ s : CWSquareSupport,
    if s.1 leg = block then cwSquareClassCount a b c d s.1 * k else 0) = _
  rw [show (∑ s : CWSquareSupport,
      if s.1 leg = block then cwSquareClassCount a b c d s.1 * k else 0) =
      ∑ s ∈ cwSquareSupport,
        if s leg = block then cwSquareClassCount a b c d s * k else 0 by
    exact (Finset.sum_subtype cwSquareSupport (fun _ ↦ Iff.rfl)
      (fun s ↦ if s leg = block then cwSquareClassCount a b c d s * k else 0)).symm]
  rw [cwSquareSupport_eq_antidiagonal]
  unfold cwSquareAntidiagonal
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  cases leg <;> fin_cases block <;>
    simp [cwSquareClassCount, cwSquare004Orbit, cwSquareAddress_eq_iff,
      cwSquare013Orbit, cwSquare022Orbit, cwSquare112Orbit,
      cwSquareMarginalType] <;> ring

/-- The marginal profile has the same mass as the joint profile. -/
theorem sum_cwSquareMarginalType (a b c d k : ℕ) :
    ∑ i, cwSquareMarginalType a b c d k i = cwSquareStride a b c d * k := by
  rw [show (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} by decide]
  simp [cwSquareMarginalType, cwSquareStride]
  ring

/-! ## Marked and ambient word families -/

/-- Recursive power depth for a proportional symmetric square profile.  A positive word at this
depth has `cwSquareStride a b c d * k` letters. -/
def cwSquareDepth (a b c d k : ℕ) : ℕ := cwSquareStride a b c d * k - 1

/-- For a nonzero proportional repetition of a nonempty profile, the recursive power depth has
the advertised successor.

Proof sketch: positivity ensures that truncated subtraction by one is exact. -/
theorem cwSquareDepth_add_one {a b c d k : ℕ}
    (hstride : 0 < cwSquareStride a b c d) (hk : 0 < k) :
    cwSquareDepth a b c d k + 1 = cwSquareStride a b c d * k := by
  unfold cwSquareDepth
  have hproduct : 0 < cwSquareStride a b c d * k := Nat.mul_pos hstride hk
  omega

/-- The proportional symmetric joint profile is a valid word type whenever its total mass is
positive. -/
theorem cwSquareNaturalType_mem_types {a b c d k : ℕ}
    (hstride : 0 < cwSquareStride a b c d) (hk : 0 < k) :
    cwSquareNaturalType a b c d k ∈
      WordType.types CWSquareSupport (cwSquareDepth a b c d k + 1) := by
  rw [WordType.mem_types, sum_cwSquareNaturalType,
    cwSquareDepth_add_one hstride hk]

/-- Words of the exact symmetric joint type.  These are the *marked* targets whose constituent
value is retained after hashing. -/
noncomputable def cwSquareMarkedWords (a b c d k : ℕ) :
    Finset (PositiveWord CWSquareSupport (cwSquareDepth a b c d k)) :=
  positiveTypeClass CWSquareSupport (cwSquareDepth a b c d k)
    (cwSquareNaturalType a b c d k)

/-- Legwise predicate selecting a word with the prescribed five-coordinate marginal type. -/
noncomputable def cwSquareKeepMarginal (a b c d k : ℕ) (_leg : Leg)
    (word : PositiveWord (Fin 5) (cwSquareDepth a b c d k)) : Prop :=
  WordType.multiplicity
    (positiveWordEquiv (Fin 5) (cwSquareDepth a b c d k) word) =
      cwSquareMarginalType a b c d k

noncomputable instance cwSquareKeepMarginal_decidable (a b c d k : ℕ) (leg : Leg)
    (word : PositiveWord (Fin 5) (cwSquareDepth a b c d k)) :
    Decidable (cwSquareKeepMarginal a b c d k leg word) := by
  classical
  unfold cwSquareKeepMarginal
  infer_instance

/-- All supported square words with the prescribed type on each of the three legs.  This is the
ambient family obtainable by legwise block zeroing.  Unlike `cwSquareMarkedWords`, it may contain
several different joint types with those marginals. -/
noncomputable def cwSquareAmbientWords (a b c d k : ℕ) :
    Finset (PositiveWord CWSquareSupport (cwSquareDepth a b c d k)) :=
  Finset.univ.filter fun word ↦
    ∀ leg, cwSquareKeepMarginal a b c d k leg
      (PartitionHashEncoding.supportWordAddress
        (A := fun _ : Leg ↦ Fin 5) (support := cwSquareSupport)
        (cwSquareDepth a b c d k) word leg)

/-- Membership in the ambient family is exactly the conjunction of the three legwise marginal
conditions used for semantic block zeroing. -/
theorem mem_cwSquareAmbientWords_iff_keepMarginals (a b c d k : ℕ)
    (word : PositiveWord CWSquareSupport (cwSquareDepth a b c d k)) :
    word ∈ cwSquareAmbientWords a b c d k ↔
      ∀ leg, cwSquareKeepMarginal a b c d k leg
        (PartitionHashEncoding.supportWordAddress
          (A := fun _ : Leg ↦ Fin 5) (support := cwSquareSupport)
          (cwSquareDepth a b c d k) word leg) := by
  classical
  simp [cwSquareAmbientWords]

/-- Every word of the marked joint type belongs to the ambient marginal fiber.

Proof sketch: multiplicity commutes with projecting a support word to one leg, and the exact
joint profile pushes forward to `cwSquareMarginalType` on every leg. -/
theorem cwSquareMarkedWords_subset_ambientWords (a b c d k : ℕ) :
    cwSquareMarkedWords a b c d k ⊆ cwSquareAmbientWords a b c d k := by
  classical
  intro word hword
  rw [cwSquareAmbientWords, Finset.mem_filter]
  refine ⟨Finset.mem_univ word, ?_⟩
  intro leg
  unfold cwSquareKeepMarginal
  rw [PartitionHashEncoding.positiveWordEquiv_supportWordAddress
    (A := fun _ : Leg ↦ Fin 5) (support := cwSquareSupport)]
  change WordType.multiplicity
    ((fun s : CWSquareSupport ↦ s.1 leg) ∘
      positiveWordEquiv CWSquareSupport (cwSquareDepth a b c d k) word) = _
  rw [WordType.multiplicity_comp_eq_mappedType,
    mem_positiveTypeClass.mp hword, cwSquare_mappedType_eq_marginal]

/-- The exact marked type class is nonempty for every positive proportional profile. -/
theorem cwSquareMarkedWords_nonempty {a b c d k : ℕ}
    (hstride : 0 < cwSquareStride a b c d) (hk : 0 < k) :
    (cwSquareMarkedWords a b c d k).Nonempty := by
  rw [← Finset.card_pos]
  unfold cwSquareMarkedWords
  rw [card_positiveTypeClass]
  exact Finset.card_pos.mpr
    (WordType.typeClass_nonempty _ (cwSquareNaturalType_mem_types hstride hk))

/-- The ambient three-marginal word family is invariant under a simultaneous permutation of all
word positions.

Proof sketch: every defining condition is a multiplicity equation, and multiplicity is unchanged
by reindexing positions. -/
theorem cwSquareAmbientWords_reindex_mem_iff (a b c d k : ℕ)
    (e : Equiv.Perm (Fin (cwSquareDepth a b c d k + 1)))
    (word : PositiveWord CWSquareSupport (cwSquareDepth a b c d k)) :
    word ∈ cwSquareAmbientWords a b c d k ↔
      PartitionHashEncoding.positiveWordReindex
        (cwSquareDepth a b c d k) e word ∈
          cwSquareAmbientWords a b c d k := by
  classical
  have forward : ∀ (permutation : Equiv.Perm
      (Fin (cwSquareDepth a b c d k + 1)))
      (source : PositiveWord CWSquareSupport (cwSquareDepth a b c d k)),
      source ∈ cwSquareAmbientWords a b c d k →
        PartitionHashEncoding.positiveWordReindex
            (cwSquareDepth a b c d k) permutation source ∈
          cwSquareAmbientWords a b c d k := by
    intro permutation source hsource
    rw [cwSquareAmbientWords, Finset.mem_filter] at hsource ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    intro leg
    have hleg := hsource.2 leg
    unfold cwSquareKeepMarginal at hleg ⊢
    have hreindex :=
      PartitionHashEncoding.positiveWordEquiv_supportWordAddress_reindex
        (A := fun _ : Leg ↦ Fin 5) (support := cwSquareSupport)
        (cwSquareDepth a b c d k) permutation source leg
    calc
      WordType.multiplicity
          (positiveWordEquiv (Fin 5) (cwSquareDepth a b c d k)
            (PartitionHashEncoding.supportWordAddress
              (cwSquareDepth a b c d k)
              (PartitionHashEncoding.positiveWordReindex
                (cwSquareDepth a b c d k) permutation source) leg)) =
        WordType.multiplicity
          (positiveWordEquiv (Fin 5) (cwSquareDepth a b c d k)
              (PartitionHashEncoding.supportWordAddress
                (cwSquareDepth a b c d k) source leg) ∘ permutation.symm) :=
          congrArg WordType.multiplicity hreindex
      _ = WordType.multiplicity
          (positiveWordEquiv (Fin 5) (cwSquareDepth a b c d k)
            (PartitionHashEncoding.supportWordAddress
              (cwSquareDepth a b c d k) source leg)) :=
          WordType.multiplicity_reindex permutation _
      _ = cwSquareMarginalType a b c d k := hleg
  constructor
  · exact forward e word
  · intro hword
    have hback := forward e.symm
      (PartitionHashEncoding.positiveWordReindex
        (cwSquareDepth a b c d k) e word) hword
    simpa using hback

/-- Ambient source-word fibers over two leg words with the prescribed marginal type have the
same cardinality. -/
theorem card_cwSquareAmbient_sourceWordLegFiber_eq
    (a b c d k : ℕ) (leg : Leg)
    (left right : PositiveWord (Fin 5) (cwSquareDepth a b c d k))
    (hmultiplicity :
      WordType.multiplicity
          (positiveWordEquiv (Fin 5) (cwSquareDepth a b c d k) left) =
        WordType.multiplicity
          (positiveWordEquiv (Fin 5) (cwSquareDepth a b c d k) right)) :
    (PartitionHashEncoding.sourceWordLegFiber
        (cwSquareDepth a b c d k) (cwSquareAmbientWords a b c d k) leg left).card =
      (PartitionHashEncoding.sourceWordLegFiber
        (cwSquareDepth a b c d k) (cwSquareAmbientWords a b c d k) leg right).card := by
  apply PartitionHashEncoding.card_sourceWordLegFiber_eq_of_multiplicity_eq
  · intro e word
    exact cwSquareAmbientWords_reindex_mem_iff a b c d k e word
  · exact hmultiplicity

/-- Division-free exact factorization of the ambient marginal family into equal leg fibers.

For any target block word of the prescribed five-coordinate marginal type,
`#(marginal type) * #(its ambient source fiber) = #(ambient words)`.  This is the finite identity
behind the outer CW combination-loss ratio. -/
theorem cwSquareMarginalCard_mul_ambientFiber
    (a b c d k : ℕ) (leg : Leg)
    (target : PositiveWord (Fin 5) (cwSquareDepth a b c d k))
    (htarget : positiveWordEquiv (Fin 5) (cwSquareDepth a b c d k) target ∈
      WordType.typeClass (cwSquareDepth a b c d k + 1)
        (cwSquareMarginalType a b c d k)) :
    (WordType.typeClass (cwSquareDepth a b c d k + 1)
        (cwSquareMarginalType a b c d k)).card *
      (PartitionHashEncoding.sourceWordLegFiber
        (cwSquareDepth a b c d k) (cwSquareAmbientWords a b c d k)
        leg target).card =
      (cwSquareAmbientWords a b c d k).card := by
  classical
  symm
  calc
    (cwSquareAmbientWords a b c d k).card =
        ∑ targetWord ∈ WordType.typeClass (cwSquareDepth a b c d k + 1)
            (cwSquareMarginalType a b c d k),
          ((cwSquareAmbientWords a b c d k).filter fun word ↦
            positiveWordEquiv (Fin 5) (cwSquareDepth a b c d k)
                (PartitionHashEncoding.supportWordAddress
                  (A := fun _ : Leg ↦ Fin 5) (support := cwSquareSupport)
                  (cwSquareDepth a b c d k) word leg) = targetWord).card := by
      exact Finset.card_eq_sum_card_fiberwise (fun word hword ↦ by
        have hambient := Finset.mem_filter.mp
          (show word ∈ cwSquareAmbientWords a b c d k from hword)
        exact WordType.mem_typeClass.mpr (hambient.2 leg))
    _ = ∑ targetWord ∈ WordType.typeClass (cwSquareDepth a b c d k + 1)
            (cwSquareMarginalType a b c d k),
          (PartitionHashEncoding.sourceWordLegFiber
            (cwSquareDepth a b c d k) (cwSquareAmbientWords a b c d k) leg
            ((positiveWordEquiv (Fin 5) (cwSquareDepth a b c d k)).symm
              targetWord)).card := by
      apply Finset.sum_congr rfl
      intro targetWord _
      apply congrArg Finset.card
      ext word
      simp only [PartitionHashEncoding.sourceWordLegFiber, Finset.mem_filter]
      constructor
      · rintro ⟨hword, heq⟩
        refine ⟨hword, ?_⟩
        apply (positiveWordEquiv (Fin 5) (cwSquareDepth a b c d k)).injective
        simpa using heq
      · rintro ⟨hword, heq⟩
        refine ⟨hword, ?_⟩
        simpa only [Equiv.apply_symm_apply] using
          congrArg (positiveWordEquiv (Fin 5) (cwSquareDepth a b c d k)) heq
    _ = ∑ _targetWord ∈ WordType.typeClass (cwSquareDepth a b c d k + 1)
            (cwSquareMarginalType a b c d k),
          (PartitionHashEncoding.sourceWordLegFiber
            (cwSquareDepth a b c d k) (cwSquareAmbientWords a b c d k)
            leg target).card := by
      apply Finset.sum_congr rfl
      intro targetWord htargetWord
      apply card_cwSquareAmbient_sourceWordLegFiber_eq
      rw [WordType.mem_typeClass] at htargetWord htarget
      simpa using htargetWord.trans htarget.symm
    _ = (WordType.typeClass (cwSquareDepth a b c d k + 1)
            (cwSquareMarginalType a b c d k)).card *
          (PartitionHashEncoding.sourceWordLegFiber
            (cwSquareDepth a b c d k) (cwSquareAmbientWords a b c d k)
            leg target).card := by simp

/-- The common five-coordinate marginal is itself a valid word type for every positive
proportional profile. -/
theorem cwSquareMarginalType_mem_types {a b c d k : ℕ}
    (hstride : 0 < cwSquareStride a b c d) (hk : 0 < k) :
    cwSquareMarginalType a b c d k ∈
      WordType.types (Fin 5) (cwSquareDepth a b c d k + 1) := by
  rw [WordType.mem_types, sum_cwSquareMarginalType,
    cwSquareDepth_add_one hstride hk]

/-- Common size of an ambient source-word fiber, expressed as the exact quotient of the ambient
family by its marginal type class. -/
noncomputable def cwSquareAmbientFiberSize (a b c d k : ℕ) : ℕ :=
  (cwSquareAmbientWords a b c d k).card /
    (WordType.typeClass (cwSquareDepth a b c d k + 1)
      (cwSquareMarginalType a b c d k)).card

/-- Every ambient fiber over a correctly typed leg word has the quotient size
`cwSquareAmbientFiberSize`.

Proof sketch: divide the preceding exact product identity by the nonzero marginal type-class
cardinality. -/
theorem card_cwSquareAmbient_sourceWordLegFiber
    {a b c d k : ℕ} (hstride : 0 < cwSquareStride a b c d) (hk : 0 < k)
    (leg : Leg) (target : PositiveWord (Fin 5) (cwSquareDepth a b c d k))
    (htarget : positiveWordEquiv (Fin 5) (cwSquareDepth a b c d k) target ∈
      WordType.typeClass (cwSquareDepth a b c d k + 1)
        (cwSquareMarginalType a b c d k)) :
    (PartitionHashEncoding.sourceWordLegFiber
      (cwSquareDepth a b c d k) (cwSquareAmbientWords a b c d k)
      leg target).card = cwSquareAmbientFiberSize a b c d k := by
  unfold cwSquareAmbientFiberSize
  exact Nat.eq_div_of_mul_eq_left
    (Finset.card_ne_zero.mpr
      (WordType.typeClass_nonempty _
        (cwSquareMarginalType_mem_types hstride hk)))
    (by
      simpa [Nat.mul_comm] using
        cwSquareMarginalCard_mul_ambientFiber a b c d k leg target htarget)

/-- Every encoded ambient target has the prescribed marginal type on each tensor leg. -/
theorem cwSquareAmbientTarget_legWord_mem_marginalTypeClass
    {R : Type*} [Field R]
    (H : PartitionHashEncoding (R := R) cwSquareSupport)
    (a b c d k : ℕ)
    {triple : ProgressionHash.LegalTriple R
      (Fin (cwSquareDepth a b c d k + 1)) H.target}
    (htriple : triple ∈ H.legalTargets (cwSquareDepth a b c d k)
      (cwSquareAmbientWords a b c d k)) (leg : Leg) :
    positiveWordEquiv (Fin 5) (cwSquareDepth a b c d k)
        (H.modeledAddress (cwSquareDepth a b c d k) triple leg) ∈
      WordType.typeClass (cwSquareDepth a b c d k + 1)
        (cwSquareMarginalType a b c d k) := by
  let source := H.sourceWordOfLegalTriple (cwSquareDepth a b c d k) triple
  have hsource : source ∈ cwSquareAmbientWords a b c d k :=
    H.sourceWordOfLegalTriple_mem_of_mem _ _ htriple
  have hambient := Finset.mem_filter.mp hsource
  apply WordType.mem_typeClass.mpr
  have hleg := hambient.2 leg
  unfold cwSquareKeepMarginal at hleg
  simpa [source, PartitionHashEncoding.modeledAddress] using hleg

/-- Exact ambient hashing-target fiber size on every leg.  This transports the division-free
source-word factorization through the injective legal-triple encoding. -/
theorem card_cwSquareAmbientTarget_legFiber
    {R : Type*} [Field R]
    (H : PartitionHashEncoding (R := R) cwSquareSupport)
    {a b c d k : ℕ} (hstride : 0 < cwSquareStride a b c d) (hk : 0 < k)
    {triple : ProgressionHash.LegalTriple R
      (Fin (cwSquareDepth a b c d k + 1)) H.target}
    (htriple : triple ∈ H.legalTargets (cwSquareDepth a b c d k)
      (cwSquareAmbientWords a b c d k)) (leg : Leg) :
    (ProgressionHash.LegalTriple.legFiber
      (H.legalTargets (cwSquareDepth a b c d k)
        (cwSquareAmbientWords a b c d k)) triple leg).card =
      cwSquareAmbientFiberSize a b c d k := by
  rw [H.card_legFiber_legalTargets_eq_card_sourceWordLegFiber _ _ htriple]
  exact card_cwSquareAmbient_sourceWordLegFiber hstride hk leg _
    (cwSquareAmbientTarget_legWord_mem_marginalTypeClass H a b c d k htriple leg)

/-- The union of the three ambient leg-competitor sets is at most three times the common ambient
fiber size. -/
theorem card_cwSquareAmbientTarget_legwiseCompetitors_le
    {R : Type*} [Field R]
    (H : PartitionHashEncoding (R := R) cwSquareSupport)
    {a b c d k : ℕ} (hstride : 0 < cwSquareStride a b c d) (hk : 0 < k)
    {triple : ProgressionHash.LegalTriple R
      (Fin (cwSquareDepth a b c d k + 1)) H.target}
    (htriple : triple ∈ H.legalTargets (cwSquareDepth a b c d k)
      (cwSquareAmbientWords a b c d k)) :
    (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
      (H.legalTargets (cwSquareDepth a b c d k)
        (cwSquareAmbientWords a b c d k)) triple).card ≤
      3 * cwSquareAmbientFiberSize a b c d k := by
  apply ProgressionHash.LegalTriple.card_legwiseCompetitorYIndices_le_three_mul
  intro leg
  exact (card_cwSquareAmbientTarget_legFiber H hstride hk htriple leg).le

/-- Exact marked-target hashing theorem for the outer CW square.

The marked joint type is isolated against every word in the ambient marginal fiber.  A field of
size at least twelve times the common ambient leg-fiber size suffices: three leg fibers contribute
the factor three, and the affine-hashing deletion estimate contributes the factor four. -/
theorem exists_seed_many_cwSquareMarkedIsolatedPowerAddresses
    {R : Type*} [Field R] [Fintype R] [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) cwSquareSupport)
    {a b c d k : ℕ} (hstride : 0 < cwSquareStride a b c d) (hk : 0 < k)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hfield : 12 * cwSquareAmbientFiberSize a b c d k ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (cwSquareDepth a b c d k + 1)),
      3 * (cwSquareMarkedWords a b c d k).card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (H.markedLegwiseIsolatedPowerAddresses
              (cwSquareDepth a b c d k)
              (cwSquareAmbientWords a b c d k)
              (cwSquareMarkedWords a b c d k) B seed).card ∧
        H.markedLegwiseIsolatedPowerAddresses
            (cwSquareDepth a b c d k)
            (cwSquareAmbientWords a b c d k)
            (cwSquareMarkedWords a b c d k) B seed ⊆
          H.filteredPowerAddresses (cwSquareDepth a b c d k)
            (cwSquareAmbientWords a b c d k) B seed ∧
        IsLegwiseInjective
          (H.markedLegwiseIsolatedPowerAddresses
            (cwSquareDepth a b c d k)
            (cwSquareAmbientWords a b c d k)
            (cwSquareMarkedWords a b c d k) B seed) := by
  apply H.exists_seed_many_markedLegwiseIsolatedPowerAddresses
    (cwSquareDepth a b c d k)
    (cwSquareAmbientWords a b c d k) (cwSquareMarkedWords a b c d k)
    (cwSquareMarkedWords_subset_ambientWords a b c d k) B hB
  intro triple htriple
  have hambient : triple ∈ H.legalTargets (cwSquareDepth a b c d k)
      (cwSquareAmbientWords a b c d k) :=
    H.legalTargets_mono _ (cwSquareMarkedWords_subset_ambientWords a b c d k)
      htriple
  calc
    4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (H.legalTargets (cwSquareDepth a b c d k)
          (cwSquareAmbientWords a b c d k)) triple).card ≤
      4 * (3 * cwSquareAmbientFiberSize a b c d k) :=
        Nat.mul_le_mul_left 4
          (card_cwSquareAmbientTarget_legwiseCompetitors_le
            H hstride hk hambient)
    _ = 12 * cwSquareAmbientFiberSize a b c d k := by ring
    _ ≤ Fintype.card R := hfield

end AlgebraicComplexity.Examples
