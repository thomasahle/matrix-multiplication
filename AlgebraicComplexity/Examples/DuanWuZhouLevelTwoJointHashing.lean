/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStageFamily
import AlgebraicComplexity.MatrixMultiplication.PartitionedSymmetrizedHashing
import AlgebraicComplexity.MatrixMultiplication.CompatibilityIsolationIncidenceMono
import AlgebraicComplexity.MatrixMultiplication.PartitionedSymmetrizedCompatibility

/-!
# The joint six-orientation hash of `[DuanWuZhou2022]` section 6

Layer 4 (`AlgebraicComplexity/Examples/`).  `Tensor/PartitionedSymmetrization.lean` makes `sym₆`
of the level-two source a `PartitionedTensor`, and
`Examples/DuanWuZhouLevelTwoStageFamily.lean` composes that bridge with the section 6 assembly
`Tensor.Restricts.partitionedYZCompatibilityCleanup_to_repairedRestrictedSplittingDirectSum`,
leaving its premises as named hypotheses.  This module discharges the *hashing* half of those
premises for the level-two instance:

* `hselect` --- `dwz63_restricts_positivePower_jointRetained`,
* `hX` --- `dwz63_x_injOn_jointRetained`,
* `batch` / `hbatch` --- `uniformBatch` and `uniformBatch_surjective`,
* `hbudget` --- `dwz63_holeBudget_uniformBatch`, from
  `AsymmetricGlobal.holeBudget_of_eight_mul_card_le`.

## One seed for all six orientations

`dwz63SymSixPartition` has block labels `15 ^ 6 = 11390625` six-tuples of coarse
Coppersmith--Winograd square addresses.  Hashing them by one seed needs a `PartitionHashEncoding`
of the *composite* support, which no field-valued construction can assemble from the factors: a
sum of six field labels is not injective in the six-tuple.  `NatBlockEncoding` of
`MatrixMultiplication/PartitionedSymmetrizedHashing.lean` composes in `ℕ` instead, reading the six
orientations as six base-five digits, and casts once at the end:

`dwz63SquareNatEncoding` (radix `5`, constant sum `4`, the degree-four antidiagonal) composes by
`NatBlockEncoding.permute` and `NatBlockEncoding.external` into `dwz63SymSixNatEncoding`, of radix
`5 ^ 6 = 15625` and constant sum `15624`.  Any field of characteristic at least `15625` then
carries the joint encoding `dwz63SymSixHashEncoding`.  **That constant is independent of the word
length**, so `Combinatorics/PrimeFieldSizing.lean`'s characteristic floor absorbs it with no
exponential cost --- exactly as `[DuanWuZhou2022]` needs, since the hashing modulus itself grows
with the word length.

## The retained support, as a definition

The count-side lane bounds the size of `Tensor.compatibilityIsolatedSupport` on the family this
hash leaves, so that family is exposed as the definition `dwz63JointRetainedSupport`, not as an
existential: it is `PartitionHashEncoding.markedXYIsolatedPowerAddresses` of the joint encoding, at
ambient family `Finset.univ` and a client-supplied marked family.  Its three structural facts are

* `dwz63JointRetainedSupport_subset` --- it is a sub-support of the six-orientation positive
  power, which is exactly the hypothesis
  `Tensor.isCompatibilitySound_symSixPowerCompatible_of_subset` consumes, so both compatibility
  obligations follow for any legwise source model;
* `card_dwz63JointRetainedSupport` --- its cardinality is the retained *marked* target count, the
  quantity the copy-count estimate bounds from below;
* `exists_seed_dwz63JointRetained` --- one seed realizes the marked count up to
  `[DuanWuZhou2022]`'s hash loss `4|R|²/(3|B|)`, under the modulus condition `8d ≤ |R|` on the
  common ambient leg-fiber degree.

## What is *not* discharged here

`Q`, the word length `m`, the split restriction `α`, the per-address `holes` and the factorwise
`hleaf` are the leaf lane's; the marked family `markedWords`, the progression-free set `B` and the
fiber degree `d` are the count lane's.  Every one of them is an explicit hypothesis below.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, §6.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u v

/-! ## The base mixed-radix encoding of the coarse Coppersmith--Winograd square -/

/-- **The fifteen coarse square addresses, in base five.**  A coarse address is a triple of
degrees in `{0,…,4}` summing to four (`cwSquareAntidiagonal_degree_sum`), so the degree itself is
an injective label below the radix `5` with constant sum `4`. -/
def cwSquareNatEncoding : NatBlockEncoding (A := fun _ : Leg ↦ Fin 5) cwSquareSupport where
  code _ a := (a : ℕ)
  alphabet := 5
  natTarget := 4
  support_nonempty := ⟨cwSquare004, by rw [cwSquareSupport_eq_antidiagonal]; decide⟩
  code_lt _ a := a.isLt
  code_injective _ := Fin.val_injective
  code_sum s hs :=
    cwSquareAntidiagonal_degree_sum s (cwSquareSupport_eq_antidiagonal ▸ hs)

@[simp] theorem cwSquareNatEncoding_alphabet : cwSquareNatEncoding.alphabet = 5 := rfl

@[simp] theorem cwSquareNatEncoding_natTarget : cwSquareNatEncoding.natTarget = 4 := rfl

/-- The base encoding read at the level-two square partition's own support. -/
noncomputable def dwz63SquareNatEncoding (K : Type u) [CommRing K] :
    NatBlockEncoding ((cwSquarePartitionedTensor K dwz63Q).support) :=
  cwSquareNatEncoding.copy (cwSquarePartitionedTensor_support (K := K) (q := dwz63Q)).symm

/-! ## The joint six-orientation encoding -/

/-- **One mixed-radix encoding of all six orientations.**  The six orientations of the level-two
source enter as the six base-five digits of a single numeral, so a single hashing seed acts on the
whole six-tuple.  This is the object `[DuanWuZhou2022]` section 6's joint hash needs and that no
field-valued composition can build. -/
noncomputable def dwz63SymSixNatEncoding (K : Type u) [CommRing K] :
    NatBlockEncoding ((dwz63SymSixPartition K).support) :=
  (((dwz63SquareNatEncoding K).external ((dwz63SquareNatEncoding K).permute cycle)).external
      ((dwz63SquareNatEncoding K).permute cycle.symm)).external
    ((((dwz63SquareNatEncoding K).permute swapXY).external
        ((dwz63SquareNatEncoding K).permute (cycle.trans swapXY))).external
      ((dwz63SquareNatEncoding K).permute (cycle.symm.trans swapXY)))

set_option maxRecDepth 40000 in
/-- **The joint alphabet is `5 ^ 6 = 15625`**, a constant in the word length. -/
@[simp] theorem dwz63SymSixNatEncoding_alphabet (K : Type u) [CommRing K] :
    (dwz63SymSixNatEncoding K).alphabet = 15625 := by
  rfl

set_option maxRecDepth 40000 in
/-- **The joint constant target is `15624`**, the base-five repunit-like numeral with all six
digits equal to four. -/
@[simp] theorem dwz63SymSixNatEncoding_natTarget (K : Type u) [CommRing K] :
    (dwz63SymSixNatEncoding K).natTarget = 15624 := by
  rfl

/-- **The joint hashing encoding of the six-orientation partition.**  Any field of characteristic
at least `15625` carries it; the bound is a constant, so the prime-field sizing pays no
exponential price for it. -/
noncomputable def dwz63SymSixHashEncoding (K : Type u) [CommRing K]
    (R : Type v) [Field R] {p : ℕ} [CharP R p] (hp : 15625 ≤ p) :
    PartitionHashEncoding (R := R) ((dwz63SymSixPartition K).support) :=
  (dwz63SymSixNatEncoding K).toPartitionHashEncoding (R := R) (p := p)
    (by rw [dwz63SymSixNatEncoding_alphabet]; exact hp)

/-! ## The retained support -/

/-- **The block-label family of the level-two six-orientation partition.**  Every leg carries one
coarse Coppersmith--Winograd square degree per leg permutation, in the association of
`PartitionedTensor.symSixPartition`; the leg permutations do not change the alphabet because the
coarse square's three legs share it. -/
abbrev DwzSymSixBlock (_c : Leg) : Type :=
  ((Fin 5 × Fin 5) × Fin 5) × ((Fin 5 × Fin 5) × Fin 5)

/-- **The family the joint hash retains, as a definition.**

`[DuanWuZhou2022]` section 6's counting happens on this `Finset`: the marked block-word addresses
of the six-orientation positive power that survive one affine seed and are isolated on the `X` and
`Y` legs against the whole ambient family, with the `Z` leg deliberately unconstrained so the
compatibility zero-outs downstream still see repeated `Z` words. -/
noncomputable def dwz63JointRetainedSupport (K : Type u) [CommRing K]
    {R : Type v} [Field R] {p : ℕ} [CharP R p] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Finset (BlockAddress fun c ↦ PositiveWord (DwzSymSixBlock c) n) :=
  (dwz63SymSixHashEncoding K R hp).markedXYIsolatedPowerAddresses n Finset.univ markedWords B seed

variable {R : Type v} [Field R] {p : ℕ} [CharP R p]

/-- **`hselect`.**  The six-orientation positive power restricts onto the retained
subpartition. -/
theorem dwz63_restricts_positivePower_jointRetained [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Restricts ((dwz63SymSixPartition K).positivePower n).realize
      (((dwz63SymSixPartition K).positivePower n).withSupport
        (dwz63JointRetainedSupport K hp n markedWords B seed)).realize :=
  PartitionHashEncoding.restricts_positivePower_to_markedXYIsolated
    (dwz63SymSixPartition K) (dwz63SymSixHashEncoding K R hp) n markedWords B hB seed

/-- **`hX`.**  The retained family has pairwise distinct `X` block words. -/
theorem dwz63_x_injOn_jointRetained [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Set.InjOn (fun address : BlockAddress (fun c ↦ PositiveWord (DwzSymSixBlock c) n) ↦
        address .X)
      (dwz63JointRetainedSupport K hp n markedWords B seed : Set _) :=
  PartitionHashEncoding.x_injOn_markedXYIsolated_positivePower
    (dwz63SymSixHashEncoding K R hp) n markedWords B hB seed

/-- **The retained family is a sub-support of the six-orientation positive power.**  This is the
hypothesis `Tensor.isCompatibilitySound_symSixPowerCompatible_of_subset` consumes, so the
compatibility lane's two soundness obligations hold on it for any legwise source model. -/
theorem dwz63JointRetainedSupport_subset [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    dwz63JointRetainedSupport K hp n markedWords B seed ⊆
      ((dwz63SymSixPartition K).positivePower n).support :=
  PartitionHashEncoding.markedXYIsolatedPowerAddresses_subset_positivePower_support
    (dwz63SymSixPartition K) (dwz63SymSixHashEncoding K R hp) n markedWords B seed

/-- **The retained count is the retained marked target count.**  This is the cardinality the
copy-count estimate bounds from below; nothing coarser is stored. -/
theorem card_dwz63JointRetainedSupport
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    (dwz63JointRetainedSupport K hp n markedWords B seed).card =
      (ProgressionHash.LegalTriple.markedXYIsolatedTargets
        ((dwz63SymSixHashEncoding K R hp).legalTargets n Finset.univ)
        ((dwz63SymSixHashEncoding K R hp).legalTargets n markedWords) B seed).card :=
  (dwz63SymSixHashEncoding K R hp).card_markedXYIsolatedPowerAddresses n Finset.univ
    markedWords (Finset.subset_univ _) B seed

/-- **The good seed.**  One affine seed retains a marked family whose count realizes the marked
count up to `[DuanWuZhou2022]`'s hash loss, and simultaneously delivers `hselect` and `hX`.  The
hypothesis is exactly the paper's modulus condition `8 · d ≤ |R|` on the common ambient
`X`- and `Y`-leg fiber degree `d` of the marked targets. -/
theorem exists_seed_dwz63JointRetained [Fintype R] [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (hB : ThreeAPFree (B : Set R)) (d : ℕ)
    (hXfiber : ∀ triple ∈ (dwz63SymSixHashEncoding K R hp).legalTargets n markedWords,
      (ProgressionHash.LegalTriple.legFiber
        ((dwz63SymSixHashEncoding K R hp).legalTargets n Finset.univ) triple .X).card ≤ d)
    (hYfiber : ∀ triple ∈ (dwz63SymSixHashEncoding K R hp).legalTargets n markedWords,
      (ProgressionHash.LegalTriple.legFiber
        ((dwz63SymSixHashEncoding K R hp).legalTargets n Finset.univ) triple .Y).card ≤ d)
    (hmodulus : 8 * d ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (n + 1)),
      3 * markedWords.card * B.card ≤
        4 * (Fintype.card R * Fintype.card R) *
          (dwz63JointRetainedSupport K hp n markedWords B seed).card := by
  obtain ⟨seed, hcount, _hsubset, _hinjX, _hinjY⟩ :=
    (dwz63SymSixHashEncoding K R hp).exists_seed_many_markedXYIsolatedPowerAddresses_of_modulus
      n Finset.univ markedWords (Finset.subset_univ _) B hB d hXfiber hYfiber hmodulus
  exact ⟨seed, hcount⟩

/-! ## Batching and the Hole-Lemma budget -/

section Budget

variable {Bidx : Leg → Type} [∀ c, Fintype (Bidx c)] [∀ c, DecidableEq (Bidx c)]

/-- **`hbudget` for uniform batches.**  `[DuanWuZhou2022]`'s Hole Lemma inequality holds for every
batch as soon as every broken copy misses at most an eighth of the available small `Z`-blocks and
every batch has at least `k` copies with `8(ℓ(m+1) + 1) ≤ 7k`.  The batches are
`uniformBatch`'s, so `batch` and `hbatch` are definitions rather than existentials. -/
theorem dwz63_holeBudget_uniformBatch
    (m : ℕ) (α : Bidx Leg.Z → ℕ) (l : ℕ)
    (hl : Fintype.card (Bidx Leg.Z) ≤ 2 ^ l)
    (hpos : 0 < Fintype.card (AvailableWord (Bidx Leg.Z) m α))
    {ι : Type*} [Fintype ι]
    (holes : ι → Finset (AvailableWord (Bidx Leg.Z) m α))
    (hholes : ∀ a, 8 * (holes a).card ≤ Fintype.card (AvailableWord (Bidx Leg.Z) m α))
    {k batches : ℕ} (hk : 0 < k) (hbatches : 0 < batches)
    (hfit : batches * k ≤ Fintype.card ι)
    (hcopies : 8 * (l * (m + 1) + 1) ≤ 7 * k) (b : Fin batches) :
    Fintype.card (AvailableWord (Bidx Leg.Z) m α) *
        ∏ a : {a : ι // uniformBatch k hbatches a = b}, (holes a.1).card <
      Fintype.card (AvailableWord (Bidx Leg.Z) m α) ^
        Fintype.card {a : ι // uniformBatch k hbatches a = b} := by
  refine AsymmetricGlobal.holeBudget_of_eight_mul_card_le
    (fun a : {a : ι // uniformBatch k hbatches a = b} ↦ holes a.1) (l * (m + 1)) hpos
    (AsymmetricGlobal.card_availableWord_le_two_pow_mul hl m α)
    (fun a ↦ hholes a.1) ?_
  exact hcopies.trans (Nat.mul_le_mul_left 7 (le_card_uniformBatch_fiber hk hbatches hfit b))

/-- **Uniform batching relabelled through an enumeration of the batch type.**  The engine's batch
index may have to live in a prescribed universe --- the level-two endpoint asks for the field's ---
while `uniformBatch` produces `Fin batches`.  A client supplies the enumeration `e` and gets the
batching in its own index type. -/
noncomputable def relabeledUniformBatch {ι : Type*} [Fintype ι] (k : ℕ) {batches : ℕ}
    (hbatches : 0 < batches) {β : Type*} (e : β ≃ Fin batches) (a : ι) : β :=
  e.symm (uniformBatch k hbatches a)

/-- **`hbatch` for the relabelled batching.** -/
theorem relabeledUniformBatch_surjective {ι : Type*} [Fintype ι] {k batches : ℕ}
    (hk : 0 < k) (hbatches : 0 < batches) (hfit : batches * k ≤ Fintype.card ι)
    {β : Type*} (e : β ≃ Fin batches) :
    Function.Surjective (relabeledUniformBatch (ι := ι) k hbatches e) := by
  intro b
  obtain ⟨a, ha⟩ := uniformBatch_surjective hk hbatches hfit (e b)
  exact ⟨a, by simp [relabeledUniformBatch, ha]⟩

/-- Relabelling does not move the batches: the fibers correspond. -/
def relabeledUniformBatch_fiber_equiv {ι : Type*} [Fintype ι] (k : ℕ) {batches : ℕ}
    (hbatches : 0 < batches) {β : Type*} (e : β ≃ Fin batches) (b : β) :
    {a : ι // relabeledUniformBatch k hbatches e a = b} ≃
      {a : ι // uniformBatch k hbatches a = e b} where
  toFun a := ⟨a.1, e.symm_apply_eq.mp a.2⟩
  invFun a := ⟨a.1, e.symm_apply_eq.mpr a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **`hbudget` for the relabelled batching.** -/
theorem dwz63_holeBudget_relabeledUniformBatch
    (m : ℕ) (α : Bidx Leg.Z → ℕ) (l : ℕ)
    (hl : Fintype.card (Bidx Leg.Z) ≤ 2 ^ l)
    (hpos : 0 < Fintype.card (AvailableWord (Bidx Leg.Z) m α))
    {ι : Type*} [Fintype ι]
    (holes : ι → Finset (AvailableWord (Bidx Leg.Z) m α))
    (hholes : ∀ a, 8 * (holes a).card ≤ Fintype.card (AvailableWord (Bidx Leg.Z) m α))
    {k batches : ℕ} (hk : 0 < k) (hbatches : 0 < batches)
    (hfit : batches * k ≤ Fintype.card ι)
    (hcopies : 8 * (l * (m + 1) + 1) ≤ 7 * k)
    {β : Type*} [DecidableEq β] (e : β ≃ Fin batches) (b : β) :
    Fintype.card (AvailableWord (Bidx Leg.Z) m α) *
        ∏ a : {a : ι // relabeledUniformBatch k hbatches e a = b}, (holes a.1).card <
      Fintype.card (AvailableWord (Bidx Leg.Z) m α) ^
        Fintype.card {a : ι // relabeledUniformBatch k hbatches e a = b} := by
  have hprod : (∏ a : {a : ι // relabeledUniformBatch k hbatches e a = b}, (holes a.1).card)
      = ∏ a : {a : ι // uniformBatch k hbatches a = e b}, (holes a.1).card :=
    Fintype.prod_equiv (relabeledUniformBatch_fiber_equiv (ι := ι) k hbatches e b) _ _ fun _ ↦ rfl
  have hcard : Fintype.card {a : ι // relabeledUniformBatch k hbatches e a = b}
      = Fintype.card {a : ι // uniformBatch k hbatches a = e b} :=
    Fintype.card_congr (relabeledUniformBatch_fiber_equiv (ι := ι) k hbatches e b)
  rw [hprod, hcard]
  exact dwz63_holeBudget_uniformBatch m α l hl hpos holes hholes hk hbatches hfit hcopies (e b)

end Budget

/-! ## The assembled level-two stage -/

section Assembly

/-- **The retained subpartition of the six-orientation positive power.**  Its support is
`dwz63JointRetainedSupport` and its constituents are those of the positive power, untouched. -/
noncomputable def dwz63JointRetained (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1))) :=
  ((dwz63SymSixPartition K).positivePower n).withSupport
    (dwz63JointRetainedSupport K hp n markedWords B seed)

/-- **The doubly compatibility-isolated retained support**, the family `[DuanWuZhou2022]`
section 6.3's copy count is a count of: the joint hash's retained addresses that survive the `Y`
and then the `Z` compatibility zero-out for a legwise source model `compat`. -/
noncomputable def dwz63JointIsolatedSupport (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop) :=
  compatibilityIsolatedSupport
    (compatibilityIsolatedSupport (dwz63JointRetainedSupport K hp n markedWords B seed) .Y
      (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Y n))
    .Z (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Z n)

variable {Bidx : Leg → Type} [∀ c, Fintype (Bidx c)] [∀ c, DecidableEq (Bidx c)]

/-- **`[DuanWuZhou2022]` section 6's `hstage` at the level-two source, for one word length, with
every hashing and batching premise discharged.**

What is supplied here: the joint six-orientation hash (`hselect`, `hX`), the two compatibility
soundness statements for an arbitrary legwise source model (via
`Tensor.isCompatibilitySound_symSixPowerCompatible_of_subset` on the retained sub-support), the
uniform batching (`batch`, `hbatch`) and the Hole-Lemma budget (`hbudget`).

What remains a hypothesis, and whose it is: `Q`, the leaf word length `m`, the split restriction
`α`, the per-address `holes` and the factorwise `hleaf` belong to the leaf lane; `markedWords`,
`B`, `compat` and the batch parameters `k`, `batches` belong to the count lane, together with the
inequalities `hfit` (the isolated support is big enough to fill `batches` batches of `k`) and
`hcopies` (`[DuanWuZhou2022]`'s `8(ℓ(m+1) + 1) ≤ 7k`).

The number of retained copies is `batches`, so the count lane's copy-count estimate is a lower
bound on `batches` --- and `hfit` says exactly that `batches ≤ |isolated support| / k`. -/
theorem dwz63_restricts_power_symSix_of_jointHash [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop)
    (hcompat : ∀ leg : Leg,
      IsCompatibilitySound (cwSquarePartitionedTensor K dwz63Q).support leg (compat leg))
    {W : ∀ c, Bidx c → Type u} [∀ c b, AddCommMonoid (W c b)] [∀ c b, Module K (W c b)]
    (Q : PartitionedTensor (K := K) (A := Bidx) W) (m : ℕ) (α : Bidx Leg.Z → ℕ)
    (holes : (dwz63JointIsolatedSupport K hp n markedWords B seed compat) →
      Finset (AvailableWord (Bidx Leg.Z) m α))
    (hleaf : ∀ address : (dwz63JointIsolatedSupport K hp n markedWords B seed compat),
      Restricts ((dwz63JointRetained K hp n markedWords B seed).constituent address.1)
        ((Q.restrictedSplittingPower m (SplitRestriction.ofLeg Leg.Z α)).holeSelect Leg.Z
          fun word ↦ word ∈ (holes address).image Subtype.val).realize)
    (l : ℕ) (hl : Fintype.card (Bidx Leg.Z) ≤ 2 ^ l)
    (hpos : 0 < Fintype.card (AvailableWord (Bidx Leg.Z) m α))
    (hholes : ∀ a, 8 * (holes a).card ≤ Fintype.card (AvailableWord (Bidx Leg.Z) m α))
    {k batches : ℕ} (hk : 0 < k) (hbatches : 0 < batches)
    (hfit : batches * k ≤ (dwz63JointIsolatedSupport K hp n markedWords B seed compat).card)
    (hcopies : 8 * (l * (m + 1) + 1) ≤ 7 * k)
    {β : Type*} [Fintype β] [DecidableEq β] (e : β ≃ Fin batches) :
    Restricts (Tensor.power (symSix K (dwz63Source K)) (n + 1))
      (Tensor.indexedDirectSum
        (V := fun _ : β ↦ PartitionedSpace K (PositivePowerBlockSpace K W m))
        fun _ ↦ (Q.restrictedSplittingPower m (SplitRestriction.ofLeg Leg.Z α)).realize) := by
  classical
  have hcard : Fintype.card
      (dwz63JointIsolatedSupport K hp n markedWords B seed compat)
      = (dwz63JointIsolatedSupport K hp n markedWords B seed compat).card :=
    Fintype.card_coe _
  have hfit' : batches * k ≤ Fintype.card
      (dwz63JointIsolatedSupport K hp n markedWords B seed compat) := by
    rw [hcard]; exact hfit
  have hsubset := dwz63JointRetainedSupport_subset K hp n markedWords B seed
  refine PartitionedTensor.restricts_power_symSix_to_repairedRestrictedSplittingDirectSum
    (cwSquarePartitionedTensor K dwz63Q) n (dwz63JointRetained K hp n markedWords B seed)
    (dwz63_restricts_positivePower_jointRetained K hp n markedWords B hB seed)
    (dwz63_x_injOn_jointRetained K hp n markedWords B hB seed)
    (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Y n)
    (isCompatibilitySound_symSixPowerCompatible_of_subset
      (cwSquarePartitionedTensor K dwz63Q) compat .Y n hsubset hcompat)
    (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Z n)
    (isCompatibilitySound_compatibilityIsolatedSupport
      (isCompatibilitySound_symSixPowerCompatible_of_subset
        (cwSquarePartitionedTensor K dwz63Q) compat .Z n hsubset hcompat))
    Q m α (relabeledUniformBatch k hbatches e)
    (relabeledUniformBatch_surjective hk hbatches hfit' e) holes hleaf ?_
  intro b
  exact dwz63_holeBudget_relabeledUniformBatch m α l hl hpos holes hholes hk hbatches hfit'
    hcopies e b

end Assembly

/-! ## The no-holes route -/

section NoHoles

/-- **The joint hash and the two compatibility zero-outs, stopped before hole repair.**

This is the first half of
`AsymmetricGlobal.Tensor.Restricts.partitionedYZCompatibilityCleanup_to_repairedRestrictedSplittingDirectSum`'s
own proof, reused rather than re-derived: the committed
`Tensor.Restricts.partitionedYZCompatibilityCleanup_to_indexedDirectSum` already composes
`X`-isolation with the sound `Y`- and `Z`-compatibility zero-outs and concludes with a genuine
indexed direct sum.  **No extra hypothesis on `compat` is needed for the legwise injectivity**:
that theorem derives it internally from `hX` and the two
`compatibilityIsolatedSupport_hasUniqueLegFibers` certificates, via
`isLegwiseInjective_of_uniqueAmbientFibers`.

The summands vary with the index --- each is the constituent of the six-orientation positive power
at one retained, doubly isolated address --- so this is not yet the constant family
`dwzLevelTwoCountingStage_of_stageFamily` consumes; `dwz63_stage_of_uniformLeaf` below closes that
last step from one per-constituent restriction.

Compared with `dwz63_restricts_power_symSix_of_jointHash` this drops `Q`, `m`, `α`, `holes`,
`hleaf`, `l`, `hl`, `hpos`, `hholes`, `k`, `batches`, `hk`, `hbatches`, `hfit`, `hcopies`, `β` and
`e` --- and with them the batching loss: the copy count is the full isolated support, not
`|isolated support| / k`. -/
theorem dwz63_restricts_power_symSix_to_isolatedDirectSum [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop)
    (hcompat : ∀ leg : Leg,
      IsCompatibilitySound (cwSquarePartitionedTensor K dwz63Q).support leg (compat leg)) :
    Restricts (Tensor.power (symSix K (dwz63Source K)) (n + 1))
      (Tensor.indexedDirectSum
        (fun a : (dwz63JointIsolatedSupport K hp n markedWords B seed compat) ↦
          (dwz63JointRetained K hp n markedWords B seed).constituent a.1)) :=
  (dwz63_restricts_power_symSix K n).trans
    ((dwz63_restricts_positivePower_jointRetained K hp n markedWords B hB seed).trans
      (Tensor.Restricts.partitionedYZCompatibilityCleanup_to_indexedDirectSum
        (dwz63JointRetained K hp n markedWords B seed)
        (dwz63_x_injOn_jointRetained K hp n markedWords B hB seed)
        (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Y n)
        (isCompatibilitySound_symSixPowerCompatible_of_subset
          (cwSquarePartitionedTensor K dwz63Q) compat .Y n
          (dwz63JointRetainedSupport_subset K hp n markedWords B seed) hcompat)
        (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Z n)
        (isCompatibilitySound_compatibilityIsolatedSupport
          (isCompatibilitySound_symSixPowerCompatible_of_subset
            (cwSquarePartitionedTensor K dwz63Q) compat .Z n
            (dwz63JointRetainedSupport_subset K hp n markedWords B seed) hcompat))))

/-- **`hstage` in exactly the endpoint's shape, with no hole repair at all.**

`dwzLevelTwoCountingStage_of_stageFamily` consumes a *constant* indexed direct sum, and
`HasTauWeight.indexedDirectSum_const` then adds the copies' weights.  So the leaf lane's whole
remaining obligation on this route is one restriction per retained, doubly isolated constituent
onto a single common leaf --- no `AvailableWord`, no `holes`, no `SplitRestriction`, and in
particular none of the backwards `hleaf` the hole-repair route asks for.

`e` relabels the retained index into the universe the endpoint needs (take
`β := ULift.{u} _` when the field does not live in `Type 0`); `card_dwz63JointIsolated_of_equiv`
records that the copy count is unchanged. -/
theorem dwz63_stage_of_uniformLeaf [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop)
    (hcompat : ∀ leg : Leg,
      IsCompatibilitySound (cwSquarePartitionedTensor K dwz63Q).support leg (compat leg))
    {Wleaf : Leg → Type u} [∀ c, AddCommMonoid (Wleaf c)] [∀ c, Module K (Wleaf c)]
    (leaf : Tensor3 K Wleaf)
    (hleaf : ∀ a : (dwz63JointIsolatedSupport K hp n markedWords B seed compat),
      Restricts ((dwz63JointRetained K hp n markedWords B seed).constituent a.1) leaf)
    {β : Type*} [Fintype β] [DecidableEq β]
    (e : (dwz63JointIsolatedSupport K hp n markedWords B seed compat) ≃ β) :
    Restricts (Tensor.power (symSix K (dwz63Source K)) (n + 1))
      (Tensor.indexedDirectSum (V := fun _ : β ↦ Wleaf) fun _ ↦ leaf) :=
  ((dwz63_restricts_power_symSix_to_isolatedDirectSum K hp n markedWords B hB seed compat
      hcompat).trans (Tensor.Restricts.indexedDirectSum hleaf)).trans
    (Tensor.Restricts.indexedDirectSum_const_equiv e leaf)

/-- **The copy count of the no-holes route** is the full doubly isolated retained support: the
relabelling `e` moves no copies.  This is the cardinality the count lane must bound below by
`dwz63TrueCopyRate ^ (6(n+1)) / loss (n+1)`. -/
theorem card_dwz63JointIsolated_of_equiv
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop)
    {β : Type*} [Fintype β]
    (e : (dwz63JointIsolatedSupport K hp n markedWords B seed compat) ≃ β) :
    Fintype.card β = (dwz63JointIsolatedSupport K hp n markedWords B seed compat).card :=
  (Fintype.card_congr e.symm).trans (Fintype.card_coe _)

end NoHoles

/-! ## The isolation floor at the level-two instance -/

section Floor

/-- **The support left by the first (`Y`) compatibility zero-out.**  Named so that the second
stage's competitor budget can be stated on the family it actually runs on, which is what
`Tensor.card_le_card_YZCompatibilityIsolatedSupport_add_budgets` measures. -/
noncomputable def dwz63JointYIsolatedSupport (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop) :=
  compatibilityIsolatedSupport (dwz63JointRetainedSupport K hp n markedWords B seed) .Y
    (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Y n)

/-- **The exact isolation floor at the level-two instance.**

`Tensor.card_le_card_YZCompatibilityIsolatedSupport_add_incidences` --- committed at HEAD in
`MatrixMultiplication/CompatibilityIsolationCounting.lean`, together with its conditional
method-of-types adapter --- applied to the family the joint hash retains.  No hypothesis: the
two zero-outs lose exactly their directed competitor incidences. -/
theorem card_dwz63JointRetainedSupport_le_card_jointIsolated_add_incidences
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop) :
    (dwz63JointRetainedSupport K hp n markedWords B seed).card ≤
      (dwz63JointIsolatedSupport K hp n markedWords B seed compat).card +
        compatibilityCompetitorIncidence (dwz63JointRetainedSupport K hp n markedWords B seed) .Y
          (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Y n) +
        compatibilityCompetitorIncidence
          (dwz63JointYIsolatedSupport K hp n markedWords B seed compat) .Z
          (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Z n) := by
  have h := card_le_card_YZCompatibilityIsolatedSupport_add_incidences
    (dwz63JointRetainedSupport K hp n markedWords B seed)
    (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Y n)
    (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Z n)
  dsimp only at h
  exact h

/-- **The tight budget form.**  The `Y` budget is measured on the retained family, the `Z` budget
on what the `Y` zero-out leaves. -/
theorem card_dwz63JointRetainedSupport_le_card_jointIsolated_add_budgets
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop)
    (budgetY budgetZ : ℕ)
    (hbudgetY : compatibilityCompetitorIncidence
      (dwz63JointRetainedSupport K hp n markedWords B seed) .Y
      (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Y n) ≤ budgetY)
    (hbudgetZ : compatibilityCompetitorIncidence
      (dwz63JointYIsolatedSupport K hp n markedWords B seed compat) .Z
      (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Z n) ≤ budgetZ) :
    (dwz63JointRetainedSupport K hp n markedWords B seed).card ≤
      (dwz63JointIsolatedSupport K hp n markedWords B seed compat).card
        + budgetY + budgetZ := by
  have h := card_le_card_YZCompatibilityIsolatedSupport_add_budgets
    (dwz63JointRetainedSupport K hp n markedWords B seed)
    (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Y n)
    (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Z n)
    budgetY budgetZ hbudgetY hbudgetZ
  dsimp only at h
  exact h

/-- **Both budgets on the retained family.**  The convenient form: neither hypothesis mentions the
intermediate `Y`-isolated stage, at the cost of the weaker (monotone) `Z` bound.  This is the
statement the count lane feeds. -/
theorem card_dwz63JointRetainedSupport_le_card_jointIsolated_add_ambientBudgets
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop)
    (budgetY budgetZ : ℕ)
    (hbudgetY : compatibilityCompetitorIncidence
      (dwz63JointRetainedSupport K hp n markedWords B seed) .Y
      (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Y n) ≤ budgetY)
    (hbudgetZ : compatibilityCompetitorIncidence
      (dwz63JointRetainedSupport K hp n markedWords B seed) .Z
      (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Z n) ≤ budgetZ) :
    (dwz63JointRetainedSupport K hp n markedWords B seed).card ≤
      (dwz63JointIsolatedSupport K hp n markedWords B seed compat).card
        + budgetY + budgetZ := by
  have h := card_le_card_YZCompatibilityIsolatedSupport_add_ambientBudgets
    (dwz63JointRetainedSupport K hp n markedWords B seed)
    (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Y n)
    (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Z n)
    budgetY budgetZ hbudgetY hbudgetZ
  dsimp only at h
  exact h

/-- **Half the retained family survives both zero-outs** once the two competitor budgets together
consume at most half of it.  With `dwz63_stage_of_uniformLeaf` the copy count is then at least
`|retained| / 2`, so the count lane loses only a constant factor. -/
theorem card_dwz63JointRetainedSupport_le_two_mul_card_jointIsolated
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop)
    (budgetY budgetZ : ℕ)
    (hbudgetY : compatibilityCompetitorIncidence
      (dwz63JointRetainedSupport K hp n markedWords B seed) .Y
      (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Y n) ≤ budgetY)
    (hbudgetZ : compatibilityCompetitorIncidence
      (dwz63JointRetainedSupport K hp n markedWords B seed) .Z
      (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Z n) ≤ budgetZ)
    (hhalf : 2 * (budgetY + budgetZ) ≤
      (dwz63JointRetainedSupport K hp n markedWords B seed).card) :
    (dwz63JointRetainedSupport K hp n markedWords B seed).card ≤
      2 * (dwz63JointIsolatedSupport K hp n markedWords B seed compat).card := by
  have h := card_dwz63JointRetainedSupport_le_card_jointIsolated_add_ambientBudgets
    K hp n markedWords B seed compat budgetY budgetZ hbudgetY hbudgetZ
  omega

end Floor

end AlgebraicComplexity.Examples
