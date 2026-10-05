/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.MoreAsymmetryCompatibilityInterface
import AlgebraicComplexity.Probability.EntropyChainRule
import AlgebraicComplexity.Probability.Reindex
import AlgebraicComplexity.Tensor.HoleRepair

/-!
# Bijective gauges for complete-split interfaces

An implementation may enumerate the complete-split words in each aggregate-weight row in any
order.  Such a choice is a *gauge*: a weight-preserving equivalence of split words.  Changing a
gauge is semantically harmless provided every table is transported through the equivalence.

In particular, independently gauged source and target rows use the conjugated complement

`target ∘ complementSplitWord ∘ source⁻¹`.

This differs essentially from a noninjective quotient: gauges preserve entropy, exact profiles,
type-class cardinalities, compatibility soundness, box cardinalities, and tensor realizations.
The final theorem shows that any restriction between partition boxes—including a compiled
hole-repair restriction—transports across a block-label gauge.
-/

open scoped BigOperators

namespace AlgebraicComplexity

open Tensor
open MoreAsymmetryCompatibility

structure CompleteSplitGauge (depth : ℕ) where
  toEquiv : Equiv.Perm (SplitWord depth)
  weight_eq : ∀ word, splitWordWeight (toEquiv word) = splitWordWeight word

namespace CompleteSplitGauge

variable {depth : ℕ}

/-- The identity gauge. -/
def refl (depth : ℕ) : CompleteSplitGauge depth where
  toEquiv := Equiv.refl _
  weight_eq _ := rfl

/-- Reverse a complete-split gauge. -/
def symm (gauge : CompleteSplitGauge depth) : CompleteSplitGauge depth where
  toEquiv := gauge.toEquiv.symm
  weight_eq word := by
    have h := gauge.weight_eq (gauge.toEquiv.symm word)
    simpa using h.symm

/-- Compose two complete-split gauges. -/
def trans (left right : CompleteSplitGauge depth) : CompleteSplitGauge depth where
  toEquiv := left.toEquiv.trans right.toEquiv
  weight_eq word := by
    rw [Equiv.trans_apply, right.weight_eq, left.weight_eq]

def complementEquiv (depth : ℕ) : Equiv.Perm (SplitWord depth) where
  toFun := complementSplitWord
  invFun := complementSplitWord
  left_inv := complementSplitWord_complementSplitWord
  right_inv := complementSplitWord_complementSplitWord

def transportedComplement (source target : CompleteSplitGauge depth) :
    Equiv.Perm (SplitWord depth) :=
  source.toEquiv.symm.trans ((complementEquiv depth).trans target.toEquiv)

@[simp] theorem transportedComplement_apply_relabel
    (source target : CompleteSplitGauge depth) (word : SplitWord depth) :
    transportedComplement source target (source.toEquiv word) =
      target.toEquiv (complementSplitWord word) := by
  simp [transportedComplement, complementEquiv]

@[simp] theorem transportedComplement_target_source
    (source target : CompleteSplitGauge depth) (word : SplitWord depth) :
    transportedComplement target source (transportedComplement source target word) = word := by
  simp [transportedComplement, complementEquiv]

end CompleteSplitGauge

theorem splitWordWeight_complement_add {depth : ℕ} (word : SplitWord depth) :
    splitWordWeight (complementSplitWord word) + splitWordWeight word = 2 ^ (depth + 1) := by
  classical
  unfold splitWordWeight
  rw [← Finset.sum_add_distrib]
  simp only [complementSplitWord, Fin.val_rev]
  have hterm : ∀ i : Fin (2 ^ depth),
      3 - ((word i : ℕ) + 1) + (word i : ℕ) = 2 := by
    intro i
    have hi := (word i).isLt
    omega
  calc
    (∑ i, (3 - ((word i : ℕ) + 1) + (word i : ℕ))) =
        ∑ _i : Fin (2 ^ depth), 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact hterm i
    _ = 2 ^ (depth + 1) := by simp [pow_succ]

/-- Complete-split words in one fixed aggregate-weight row. -/
abbrev FixedWeightSplitWord (depth total : ℕ) :=
  {word : SplitWord depth // splitWordWeight word = total}

namespace CompleteSplitGauge

/-- A weight-preserving gauge restricts to a permutation of each aggregate-weight row. -/
def fixedWeightEquiv (gauge : CompleteSplitGauge depth) (total : ℕ) :
    FixedWeightSplitWord depth total ≃ FixedWeightSplitWord depth total where
  toFun word := ⟨gauge.toEquiv word.1, (gauge.weight_eq word.1).trans word.2⟩
  invFun word := ⟨gauge.toEquiv.symm word.1, by
    have h := gauge.weight_eq (gauge.toEquiv.symm word.1)
    have h' : splitWordWeight (gauge.toEquiv.symm word.1) =
        splitWordWeight word.1 := by
      simpa using h.symm
    exact h'.trans word.2⟩
  left_inv word := by simp
  right_inv word := by simp

/-- Conjugated complementation sends a fixed-weight source row bijectively to the complementary
target row.  This is the semantic complement table for independently permuted slot orderings. -/
def transportedComplementFixedWeightEquiv
    (source target : CompleteSplitGauge depth) (total : ℕ)
    (htotal : total ≤ 2 ^ (depth + 1)) :
    FixedWeightSplitWord depth total ≃
      FixedWeightSplitWord depth (2 ^ (depth + 1) - total) where
  toFun word := ⟨transportedComplement source target word.1, by
    have hsum := splitWordWeight_complement_add
      (source.toEquiv.symm word.1)
    have hsource : splitWordWeight (source.toEquiv.symm word.1) = total := by
      have hg := source.weight_eq (source.toEquiv.symm word.1)
      have hg' : splitWordWeight (source.toEquiv.symm word.1) =
          splitWordWeight word.1 := by
        simpa using hg.symm
      exact hg'.trans word.2
    change splitWordWeight
      (target.toEquiv (complementSplitWord (source.toEquiv.symm word.1))) = _
    rw [target.weight_eq]
    rw [hsource] at hsum
    omega⟩
  invFun word := ⟨transportedComplement target source word.1, by
    have hsum := splitWordWeight_complement_add
      (target.toEquiv.symm word.1)
    have htarget : splitWordWeight (target.toEquiv.symm word.1) =
        2 ^ (depth + 1) - total := by
      have hg := target.weight_eq (target.toEquiv.symm word.1)
      have hg' : splitWordWeight (target.toEquiv.symm word.1) =
          splitWordWeight word.1 := by
        simpa using hg.symm
      exact hg'.trans word.2
    change splitWordWeight
      (source.toEquiv (complementSplitWord (target.toEquiv.symm word.1))) = _
    rw [source.weight_eq]
    rw [htarget] at hsum
    omega⟩
  left_inv word := by
    apply Subtype.ext
    exact transportedComplement_target_source source target word.1
  right_inv word := by
    apply Subtype.ext
    exact transportedComplement_target_source target source word.1

end CompleteSplitGauge


namespace WordType

theorem multiplicity_comp_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (word : Fin n → I) (letter : J) :
    multiplicity (e ∘ word) letter = multiplicity word (e.symm letter) := by
  classical
  unfold multiplicity
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
  constructor
  · intro h
    rw [← h]
    simp
  · intro h
    rw [h]
    simp

end WordType

namespace CompleteSplitProfile

noncomputable def relabel (beta : CompleteSplitProfile depth total samples)
    (gauge : CompleteSplitGauge depth) :
    CompleteSplitProfile depth total samples where
  counts word := beta.counts (gauge.toEquiv.symm word)
  isType := by
    classical
    rw [WordType.mem_types]
    rw [gauge.toEquiv.symm.sum_comp beta.counts]
    exact beta.sum_counts
  supported := by
    intro word hword
    have hsource := beta.supported (gauge.toEquiv.symm word) hword
    rw [← gauge.weight_eq (gauge.toEquiv.symm word),
      gauge.toEquiv.apply_symm_apply] at hsource
    exact hsource

@[simp] theorem relabel_counts (beta : CompleteSplitProfile depth total samples)
    (gauge : CompleteSplitGauge depth) (word : SplitWord depth) :
    (beta.relabel gauge).counts word = beta.counts (gauge.toEquiv.symm word) :=
  rfl

theorem relabel_isConsistent_relabelSequence_iff
    (beta : CompleteSplitProfile depth total samples)
    (gauge : CompleteSplitGauge depth) (sequence : Fin samples → SplitWord depth) :
    (beta.relabel gauge).IsConsistent (gauge.toEquiv ∘ sequence) ↔
      beta.IsConsistent sequence := by
  unfold IsConsistent
  constructor <;> intro h
  · funext word
    have hw := congrFun h (gauge.toEquiv word)
    rw [WordType.multiplicity_comp_equiv] at hw
    simpa using hw
  · funext word
    rw [WordType.multiplicity_comp_equiv]
    simpa using congrFun h (gauge.toEquiv.symm word)

theorem relabelSequence_mem_typeClass_iff
    (beta : CompleteSplitProfile depth total samples)
    (gauge : CompleteSplitGauge depth) (sequence : Fin samples → SplitWord depth) :
    gauge.toEquiv ∘ sequence ∈ (beta.relabel gauge).typeClass ↔
      sequence ∈ beta.typeClass := by
  rw [← (beta.relabel gauge).isConsistent_iff_mem_typeClass,
    ← beta.isConsistent_iff_mem_typeClass]
  exact relabel_isConsistent_relabelSequence_iff beta gauge sequence

noncomputable def typeClassRelabelEquiv
    (beta : CompleteSplitProfile depth total samples)
    (gauge : CompleteSplitGauge depth) :
    {sequence // sequence ∈ beta.typeClass} ≃
      {sequence // sequence ∈ (beta.relabel gauge).typeClass} where
  toFun sequence := ⟨gauge.toEquiv ∘ sequence.1,
    (beta.relabelSequence_mem_typeClass_iff gauge sequence.1).2 sequence.2⟩
  invFun sequence := ⟨gauge.toEquiv.symm ∘ sequence.1, by
    have h := (beta.relabelSequence_mem_typeClass_iff gauge
      (gauge.toEquiv.symm ∘ sequence.1)).1
    apply h
    simpa [Function.comp_def] using sequence.2⟩
  left_inv sequence := by
    apply Subtype.ext
    funext i
    simp [Function.comp_def]
  right_inv sequence := by
    apply Subtype.ext
    funext i
    simp [Function.comp_def]

theorem card_typeClass_relabel
    (beta : CompleteSplitProfile depth total samples)
    (gauge : CompleteSplitGauge depth) :
    (beta.relabel gauge).typeClass.card = beta.typeClass.card := by
  classical
  simpa using Fintype.card_congr (beta.typeClassRelabelEquiv gauge).symm

theorem toDistribution_relabel_probability
    (beta : CompleteSplitProfile depth total samples)
    (gauge : CompleteSplitGauge depth) (hsamples : 0 < samples) :
    ((beta.relabel gauge).toDistribution hsamples).probability =
      (beta.toDistribution hsamples).probability.reindex gauge.toEquiv := by
  apply ProbabilityVector.ext
  funext word
  rfl

theorem entropyBits_toDistribution_relabel
    (beta : CompleteSplitProfile depth total samples)
    (gauge : CompleteSplitGauge depth) (hsamples : 0 < samples) :
    ((beta.relabel gauge).toDistribution hsamples).probability.entropyBits =
      (beta.toDistribution hsamples).probability.entropyBits := by
  rw [toDistribution_relabel_probability, ProbabilityVector.entropyBits_reindex]

end CompleteSplitProfile

namespace CompleteSplitProfile

/-- Complementary exact profiles remain complementary after independent gauges, with literal
complement replaced by its conjugate between the two slot alphabets. -/
theorem relabel_counts_complement
    (left right : CompleteSplitProfile depth total samples)
    (source target : CompleteSplitGauge depth)
    (hcomplement : ∀ word,
      right.counts word = left.counts (complementSplitWord word))
    (word : SplitWord depth) :
    (right.relabel target).counts word =
      (left.relabel source).counts
        (CompleteSplitGauge.transportedComplement target source word) := by
  rw [relabel_counts, relabel_counts, hcomplement]
  congr 1
  simp [CompleteSplitGauge.transportedComplement,
    CompleteSplitGauge.complementEquiv]

end CompleteSplitProfile

namespace MoreAsymmetryCompatibility

theorem cellMultiplicity_comp_equiv
    {I Cell Symbol Target : Type*} [Fintype I]
    [DecidableEq Cell] [DecidableEq Symbol] [DecidableEq Target]
    (cellOf : I → Cell) (sequence : I → Symbol) (e : Symbol ≃ Target)
    (cell : Cell) (symbol : Target) :
    cellMultiplicity cellOf (e ∘ sequence) cell symbol =
      cellMultiplicity cellOf sequence cell (e.symm symbol) := by
  classical
  unfold cellMultiplicity
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨hcell, hsymbol⟩
    refine ⟨hcell, ?_⟩
    rw [← hsymbol]
    simp
  · rintro ⟨hcell, hsymbol⟩
    refine ⟨hcell, ?_⟩
    rw [hsymbol]
    simp

/-- Exact complement-profile transport when the source and target alphabets use independent
bijection gauges. -/
theorem cellMultiplicity_transportedComplement
    {I Cell : Type*} [Fintype I] [DecidableEq Cell]
    {depth : ℕ} (cellOf : I → Cell)
    (left right : I → SplitWord depth) (cell : Cell)
    (source target : CompleteSplitGauge depth)
    (hcomplement : ∀ position, cellOf position = cell →
      right position = complementSplitWord (left position))
    (word : SplitWord depth) :
    cellMultiplicity cellOf (target.toEquiv ∘ right) cell word =
      cellMultiplicity cellOf (source.toEquiv ∘ left) cell
        (CompleteSplitGauge.transportedComplement target source word) := by
  rw [cellMultiplicity_comp_equiv, cellMultiplicity_complement cellOf left right cell
    hcomplement]
  rw [cellMultiplicity_comp_equiv]
  congr 1
  simp [CompleteSplitGauge.transportedComplement,
    CompleteSplitGauge.complementEquiv]

namespace CompatibilityModel

variable {A : Leg → Type*} {B : Leg → Type*} {Part : Type*}
variable {depth samples : ℕ}

/-- Rename the block labels of a compatibility model while decoding every new label through the
inverse equivalence.  The semantic split words and coarse addresses are unchanged. -/
def reindexLabels (model : CompatibilityModel A Part depth samples)
    (e : ∀ c, A c ≃ B c) : CompatibilityModel B Part depth samples where
  chunks c label := model.chunks c ((e c).symm label)
  coarse address := model.coarse ((blockAddressCongr e).symm address)

@[simp] theorem reindexLabels_chunks
    (model : CompatibilityModel A Part depth samples) (e : ∀ c, A c ≃ B c)
    (c : Leg) (label : B c) :
    (model.reindexLabels e).chunks c label = model.chunks c ((e c).symm label) :=
  rfl

@[simp] theorem reindexLabels_coarse
    (model : CompatibilityModel A Part depth samples) (e : ∀ c, A c ≃ B c)
    (address : BlockAddress B) :
    (model.reindexLabels e).coarse address =
      model.coarse ((blockAddressCongr e).symm address) :=
  rfl

theorem reindexLabels_isFineLegal_iff
    (model : CompatibilityModel A Part depth samples) (e : ∀ c, A c ≃ B c)
    (address : BlockAddress B) :
    (model.reindexLabels e).IsFineLegal address ↔
      model.IsFineLegal ((blockAddressCongr e).symm address) := by
  rfl

theorem reindexLabels_hasCoarseWeights_iff
    (model : CompatibilityModel A Part depth samples) (e : ∀ c, A c ≃ B c)
    (address : BlockAddress B) :
    (model.reindexLabels e).HasCoarseWeights address ↔
      model.HasCoarseWeights ((blockAddressCongr e).symm address) := by
  rfl

theorem reindexLabels_matchesExact_iff [DecidableEq Part]
    (model : CompatibilityModel A Part depth samples) (e : ∀ c, A c ≃ B c)
    (address : BlockAddress B) (c : Leg)
    (profile : CoarseIndex Part → SplitWord depth → ℕ) :
    (model.reindexLabels e).MatchesExact address c profile ↔
      model.MatchesExact ((blockAddressCongr e).symm address) c profile := by
  rfl

theorem reindexLabels_compatibleY_iff [DecidableEq Part]
    (model : CompatibilityModel A Part depth samples) (e : ∀ c, A c ≃ B c)
    (targets : CompatibilityTargets Part depth) (label : B .Y)
    (address : BlockAddress B) :
    (model.reindexLabels e).CompatibleY targets label address ↔
      model.CompatibleY targets ((e .Y).symm label)
        ((blockAddressCongr e).symm address) := by
  rfl

theorem reindexLabels_compatibleZ_iff [DecidableEq Part]
    (model : CompatibilityModel A Part depth samples) (e : ∀ c, A c ≃ B c)
    (targets : CompatibilityTargets Part depth) (label : B .Z)
    (address : BlockAddress B) :
    (model.reindexLabels e).CompatibleZ targets label address ↔
      model.CompatibleZ targets ((e .Z).symm label)
        ((blockAddressCongr e).symm address) := by
  rfl

theorem reindexLabels_passesYFirstZeroOut_iff [DecidableEq Part]
    (model : CompatibilityModel A Part depth samples) (e : ∀ c, A c ≃ B c)
    (targets : CompatibilityTargets Part depth) (address : BlockAddress B) :
    (model.reindexLabels e).PassesYFirstZeroOut targets address ↔
      model.PassesYFirstZeroOut targets ((blockAddressCongr e).symm address) := by
  rfl

theorem reindexLabels_passesZFirstZeroOut_iff [DecidableEq Part]
    (model : CompatibilityModel A Part depth samples) (e : ∀ c, A c ≃ B c)
    (targets : CompatibilityTargets Part depth) (address : BlockAddress B) :
    (model.reindexLabels e).PassesZFirstZeroOut targets address ↔
      model.PassesZFirstZeroOut targets ((blockAddressCongr e).symm address) := by
  rfl

end CompatibilityModel

/-- Relabel an encoded source support and decode its labels through the inverse equivalences. -/
def reindexedEncoding {A B : Leg → Type*} {depth : ℕ}
    (e : ∀ c, A c ≃ B c) (encode : ∀ c, A c → SplitWord depth) :
    ∀ c, B c → SplitWord depth :=
  fun c label ↦ encode c ((e c).symm label)

/-- Fine CW legality is invariant under bijective block-label reindexing when the new encoding
decodes back to the same semantic split words. -/
theorem isEncodedFineLegalOnSupport_reindex_iff
    {A B : Leg → Type*}
    [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
    {depth : ℕ} (support : Finset (BlockAddress A))
    (e : ∀ c, A c ≃ B c) (encode : ∀ c, A c → SplitWord depth) :
    IsEncodedFineLegalOnSupport
        (support.map (blockAddressCongr e).toEmbedding)
        (reindexedEncoding e encode) ↔
      IsEncodedFineLegalOnSupport support encode := by
  constructor
  · intro h address haddress position
    have hmapped : blockAddressCongr e address ∈
        support.map (blockAddressCongr e).toEmbedding := by
      simp [haddress]
    have hlegal := h (blockAddressCongr e address) hmapped position
    simpa [reindexedEncoding] using hlegal
  · intro h address haddress position
    have hsource : (blockAddressCongr e).symm address ∈ support := by
      simpa using haddress
    have hlegal := h ((blockAddressCongr e).symm address) hsource position
    simpa [reindexedEncoding] using hlegal

end MoreAsymmetryCompatibility

namespace Tensor

variable {A B : Leg → Type*}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]

/-- Transport a compatibility relation through a legwise bijection of block labels. -/
def reindexCompatibility (e : ∀ c, A c ≃ B c) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop) :
    B pivot → BlockAddress B → Prop :=
  fun label address ↦
    compatible ((e pivot).symm label) ((blockAddressCongr e).symm address)

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
/-- Compatibility soundness is unchanged by a bijective renaming of every block label. -/
theorem IsCompatibilitySound.reindex
    {ambient : Finset (BlockAddress A)} {pivot : Leg}
    {compatible : A pivot → BlockAddress A → Prop}
    (hsound : IsCompatibilitySound ambient pivot compatible)
    (e : ∀ c, A c ≃ B c) :
    IsCompatibilitySound (ambient.map (blockAddressCongr e).toEmbedding) pivot
      (reindexCompatibility e pivot compatible) := by
  intro address haddress
  have hsource : (blockAddressCongr e).symm address ∈ ambient := by
    simpa using haddress
  simpa [reindexCompatibility] using
    hsound ((blockAddressCongr e).symm address) hsource

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    [∀ c, Fintype (B c)] in
/-- Bijections preserve the number of labels in every box part exactly. -/
theorem card_relabelParts (e : ∀ c, A c ≃ B c)
    (parts : ∀ c, Finset (A c)) (c : Leg) :
    (relabelParts e parts c).card = (parts c).card := by
  classical
  unfold relabelParts
  exact Finset.card_image_of_injective _ (e c).injective

section TensorReindex

variable {K : Type*} [CommSemiring K]
variable {V : ∀ c, A c → Type*} {W : ∀ c, B c → Type*}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable [∀ c b, AddCommMonoid (W c b)] [∀ c b, Module K (W c b)]

/-- Any restriction between partition boxes transports through a bijective reindexing.  This is
the semantic reason an existing hole-repair result can consume gauge-renamed broken copies: both
its source and repaired target are merely tensor-isomorphic box encodings. -/
theorem Restricts.partitionedReindex_boxes
    (P : PartitionedTensor (K := K) (A := A) V)
    (e : ∀ c, A c ≃ B c)
    (f : ∀ c b, V c ((e c).symm b) ≃ₗ[K] W c b)
    (source target : ∀ c, Finset (A c))
    (h : Restricts (P.box source).realize (P.box target).realize) :
    Restricts
      ((P.reindex e f).box (relabelParts e source)).realize
      ((P.reindex e f).box (relabelParts e target)).realize := by
  have hsource := Isomorphic.partitionedReindex (P.box source) e f
  rw [P.reindex_box e f source] at hsource
  have htarget := Isomorphic.partitionedReindex (P.box target) e f
  rw [P.reindex_box e f target] at htarget
  exact hsource.symm.restricts.trans (h.trans htarget.restricts)

end TensorReindex

end Tensor

end AlgebraicComplexity
