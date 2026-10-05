import AlgebraicComplexity.Combinatorics.ConditionalWordTypeCore
import AlgebraicComplexity.MatrixMultiplication.PartitionedPowerHashing

/-!
# Leg-fiber counting under a coarse-word stabilizer

Fixing a coarse word destroys invariance under arbitrary permutations of word positions, but it
retains the Young subgroup that permutes positions carrying the same coarse symbol.  Its orbits
on one fine leg are exactly conditional type classes relative to the fixed coarse word.

This file proves the corresponding exact finite double count.  It is the conditional analogue of
`PermutationStableLegFiberCounting` and is the appropriate statement inside one already-isolated
coarse constituent.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

namespace PartitionHashEncoding

variable {R : Type u} [Field R]
variable {A : Leg → Type v} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {support : Finset (BlockAddress A)}
variable {U : Type w} [Fintype U]

/-- Source words whose chosen leg has one prescribed conditional type relative to a fixed coarse
word. -/
noncomputable def sourceWordsOfConditionalLegType
    (n : ℕ) (words : Finset (PositiveWord support n)) (c : Leg)
    (source : Fin (n + 1) → U) (jointType : U × A c → ℕ) :
    Finset (PositiveWord support n) :=
  words.filter fun word ↦
    WordType.multiplicity
      (WordType.jointWord source
        (positiveWordEquiv (A c) n (supportWordAddress n word c))) = jointType

@[simp] theorem mem_sourceWordsOfConditionalLegType
    (n : ℕ) (words : Finset (PositiveWord support n)) (c : Leg)
    (source : Fin (n + 1) → U) (jointType : U × A c → ℕ)
    (word : PositiveWord support n) :
    word ∈ sourceWordsOfConditionalLegType n words c source jointType ↔
      word ∈ words ∧
      WordType.multiplicity
        (WordType.jointWord source
          (positiveWordEquiv (A c) n (supportWordAddress n word c))) = jointType := by
  classical
  simp [sourceWordsOfConditionalLegType]

/-- Fibers over fine-leg words in the same conditional orbit have equal size whenever the source
family is invariant under every position permutation stabilizing the coarse word. -/
theorem card_sourceWordLegFiber_eq_of_conditionalMultiplicity_eq
    (n : ℕ) (words : Finset (PositiveWord support n)) (c : Leg)
    (source : Fin (n + 1) → U)
    (hstable : ∀ (e : Equiv.Perm (Fin (n + 1))) word,
      source ∘ e.symm = source →
        (word ∈ words ↔ positiveWordReindex n e word ∈ words))
    (left right : PositiveWord (A c) n)
    (hmultiplicity :
      WordType.multiplicity
          (WordType.jointWord source (positiveWordEquiv (A c) n left)) =
        WordType.multiplicity
          (WordType.jointWord source (positiveWordEquiv (A c) n right))) :
    (sourceWordLegFiber n words c left).card =
      (sourceWordLegFiber n words c right).card := by
  classical
  let leftJoint := WordType.jointWord source (positiveWordEquiv (A c) n left)
  let rightJoint := WordType.jointWord source (positiveWordEquiv (A c) n right)
  let e := WordType.positionPermOfSameMultiplicity leftJoint rightJoint hmultiplicity
  have he : rightJoint ∘ e = leftJoint :=
    WordType.positionPermOfSameMultiplicity_map leftJoint rightJoint hmultiplicity
  have heSource : source ∘ e = source := by
    funext i
    have hi := congrArg Prod.fst (congrFun he i)
    exact hi
  have heSourceSymm : source ∘ e.symm = source := by
    funext i
    have hi := congrFun heSource (e.symm i)
    simpa [Function.comp_apply] using hi.symm
  have heTarget : positiveWordEquiv (A c) n left ∘ e.symm =
      positiveWordEquiv (A c) n right := by
    funext i
    have hi := congrArg Prod.snd (congrFun he (e.symm i))
    simpa [leftJoint, rightJoint, WordType.jointWord, Function.comp_apply] using hi.symm
  have heTargetBack : positiveWordEquiv (A c) n right ∘ e =
      positiveWordEquiv (A c) n left := by
    funext i
    exact congrArg Prod.snd (congrFun he i)
  apply Finset.card_bij (fun word _ ↦ positiveWordReindex n e word)
  · intro word hword
    rw [sourceWordLegFiber, Finset.mem_filter] at hword ⊢
    refine ⟨(hstable e word heSourceSymm).mp hword.1, ?_⟩
    apply (positiveWordEquiv (A c) n).injective
    rw [positiveWordEquiv_supportWordAddress_reindex, hword.2, heTarget]
  · intro leftWord _ rightWord _ heq
    apply (positiveWordEquiv support n).injective
    have hfunctions := congrArg (positiveWordEquiv support n) heq
    simp only [positiveWordEquiv_positiveWordReindex] at hfunctions
    funext i
    have hi := congrFun hfunctions (e i)
    simpa [Function.comp_apply] using hi
  · intro word hword
    refine ⟨positiveWordReindex n e.symm word, ?_, ?_⟩
    · rw [sourceWordLegFiber, Finset.mem_filter] at hword ⊢
      refine ⟨(hstable e.symm word ?_).mp hword.1, ?_⟩
      · simpa using heSource
      · apply (positiveWordEquiv (A c) n).injective
        rw [positiveWordEquiv_supportWordAddress_reindex, hword.2]
        simpa only [Equiv.symm_symm] using heTargetBack
    · simpa using positiveWordReindex_symm_apply n e.symm word

/-- Exact conditional-orbit double count.  The right side is the portion of the source family
whose chosen leg lies in the target's conditional orbit. -/
theorem card_conditionalTypeClass_mul_card_sourceWordLegFiber
    (n : ℕ) (words : Finset (PositiveWord support n)) (c : Leg)
    (source : Fin (n + 1) → U)
    (hstable : ∀ (e : Equiv.Perm (Fin (n + 1))) word,
      source ∘ e.symm = source →
        (word ∈ words ↔ positiveWordReindex n e word ∈ words))
    (target : PositiveWord (A c) n) :
    let jointType := WordType.multiplicity
      (WordType.jointWord source (positiveWordEquiv (A c) n target))
    (WordType.conditionalTypeClass source jointType).card *
        (sourceWordLegFiber n words c target).card =
      (sourceWordsOfConditionalLegType n words c source jointType).card := by
  classical
  dsimp only
  let jointType := WordType.multiplicity
    (WordType.jointWord source (positiveWordEquiv (A c) n target))
  let orbitWords := sourceWordsOfConditionalLegType n words c source jointType
  calc
    (WordType.conditionalTypeClass source jointType).card *
        (sourceWordLegFiber n words c target).card =
      ∑ candidate ∈ WordType.conditionalTypeClass source jointType,
        (sourceWordLegFiber n words c
          ((positiveWordEquiv (A c) n).symm candidate)).card := by
            symm
            apply Finset.sum_const_nat
            intro candidate hcandidate
            apply card_sourceWordLegFiber_eq_of_conditionalMultiplicity_eq
              n words c source hstable
            simpa [jointType] using WordType.mem_conditionalTypeClass.mp hcandidate
    _ = ∑ candidate ∈ WordType.conditionalTypeClass source jointType,
        (orbitWords.filter fun word ↦
          positiveWordEquiv (A c) n (supportWordAddress n word c) = candidate).card := by
            apply Finset.sum_congr rfl
            intro candidate hcandidate
            apply congrArg Finset.card
            ext word
            rw [sourceWordLegFiber, Finset.mem_filter,
              Finset.mem_filter, mem_sourceWordsOfConditionalLegType]
            constructor
            · rintro ⟨hword, hleg⟩
              refine ⟨⟨hword, ?_⟩, ?_⟩
              · simpa [hleg] using
                  (WordType.mem_conditionalTypeClass.mp hcandidate)
              · simpa [hleg]
            · rintro ⟨⟨hword, _hconditional⟩, hleg⟩
              refine ⟨hword, ?_⟩
              apply (positiveWordEquiv (A c) n).injective
              simpa using hleg
    _ = orbitWords.card := by
      symm
      exact Finset.card_eq_sum_card_fiberwise (fun word hword ↦ by
        exact WordType.mem_conditionalTypeClass.mpr
          ((mem_sourceWordsOfConditionalLegType n words c source jointType word).mp hword).2)

/-- Division-free conditional upper bound for one source-side leg fiber. -/
theorem card_conditionalTypeClass_mul_card_sourceWordLegFiber_le
    (n : ℕ) (words : Finset (PositiveWord support n)) (c : Leg)
    (source : Fin (n + 1) → U)
    (hstable : ∀ (e : Equiv.Perm (Fin (n + 1))) word,
      source ∘ e.symm = source →
        (word ∈ words ↔ positiveWordReindex n e word ∈ words))
    (target : PositiveWord (A c) n) :
    let jointType := WordType.multiplicity
      (WordType.jointWord source (positiveWordEquiv (A c) n target))
    (WordType.conditionalTypeClass source jointType).card *
        (sourceWordLegFiber n words c target).card ≤ words.card := by
  dsimp only
  rw [card_conditionalTypeClass_mul_card_sourceWordLegFiber
    n words c source hstable target]
  exact Finset.card_le_card (Finset.filter_subset _ _)

end PartitionHashEncoding

end AlgebraicComplexity
