import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeafExtraction
import AlgebraicComplexity.Tensor.PartitionedCoarseningPower

/-!
# Fine typed leaves inside coarsened constituents

A noninjective block-label coarsening replaces one constituent by the sum of all fine
constituents in its fiber.  Projecting each of the three coarse direct-sum blocks to one chosen
fine block kills every other address in that fiber.  Consequently every coarse constituent
restricts to each of its fine source constituents.

There are two distinct safe interfaces below.

* At the constituent level, one coarse word projects to one explicitly chosen fine word.  This
  preserves that constituent's matrix dimensions but does **not** recover the cardinality of a
  fine type class.
* At the selected-tensor level, the entire tensor selected by pushed-forward coarse marginal
  types projects to the entire tensor selected by the original fine marginal types.  Its indexed
  form applies only when every indexed source is such a whole selected quotient tensor; it does
  **not** turn an isolated single coarse constituent into the global fine selected family.  A
  localized coarsening-fiber theorem is required after constituentwise hashing.

The final constituent theorems additionally discharge a one-word lift obligation when the
coarse support word has the full pushed-forward **joint** type.  Three separate coarse leg
marginals are intentionally not accepted as a substitute for that one-word hypothesis.

The constituent bridge is stated in restrict-then-compose form: the coarse constituent restricts
to whatever the fine blocks of the prescribed type restrict to
(`Restricts.coarsenedPositivePower_constituent_of_mappedType`, and its typed-leaf specialization
`RationalTypedLeaf.coarsenedPositivePower_constituent_matrixMultiplication_of_mappedType_of_fineDegeneration`).
Nothing is assumed letterwise about the individual base constituents.  The letterwise theorems are
kept as corollaries because the Coppersmith--Winograd clients supply their leaf that way.
-/

namespace AlgebraicComplexity.WordType

universe u v

/-- Every target word of the pushed-forward type has at least one source word of the prescribed
fine type.  This is an existence consequence of the exact typed-fiber double count; it does not
charge the fiber cardinality as a second source of copies. -/
theorem typedWordMapFiber_nonempty
    {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (f : I → J) (a : I → ℕ) (target : Fin n → J)
    (ha : a ∈ types I n)
    (htarget : target ∈ typeClass n (mappedType f a)) :
    (typedWordMapFiber f a target).Nonempty := by
  rw [← Finset.card_pos]
  have hfactor := card_targetType_mul_card_typedWordMapFiber f a target htarget
  have hsource : 0 < (typeClass n a).card :=
    Finset.card_pos.mpr (typeClass_nonempty a ha)
  have hproduct :
      0 < (typeClass n (mappedType f a)).card *
        (typedWordMapFiber f a target).card := by
    rw [hfactor]
    exact hsource
  exact Nat.pos_of_mul_pos_left hproduct

/-- The conditional coordinate interfaces determine a joint type when, inside each coarse-shape
fiber, at least one coordinate label is injective.  The coordinate allowed to witness rigidity
may depend on the shape.  This is the exact finite abstraction for "fixed `alpha` plus all
conditional complete-split profiles". -/
theorem jointType_eq_of_conditionally_injective_coordinate
    {I : Type u} [Fintype I]
    {S : Type v} {A : Leg → Type*}
    (shape : I → S) (coordinate : ∀ c, I → A c)
    (hcoordinate : ∀ s, ∃ c, Set.InjOn (coordinate c) {i | shape i = s})
    (p q : I → ℕ)
    (hmarginal : ∀ c,
      mappedType (fun i ↦ (shape i, coordinate c i)) p =
        mappedType (fun i ↦ (shape i, coordinate c i)) q) :
    p = q := by
  classical
  funext i
  obtain ⟨c, hc⟩ := hcoordinate (shape i)
  have hrecover (a : I → ℕ) :
      mappedType (fun j ↦ (shape j, coordinate c j)) a
          (shape i, coordinate c i) = a i := by
    have hfiber :
        letterFiber (fun j ↦ (shape j, coordinate c j))
            (shape i, coordinate c i) = {i} := by
      ext j
      simp only [mem_letterFiber, Finset.mem_singleton]
      constructor
      · intro hj
        have hshape : shape j = shape i := congrArg Prod.fst hj
        have hcoord : coordinate c j = coordinate c i := congrArg Prod.snd hj
        exact hc hshape rfl hcoord
      · rintro rfl
        rfl
    unfold mappedType
    rw [hfiber]
    simp
  rw [← hrecover p, hmarginal c, hrecover q]

end AlgebraicComplexity.WordType

namespace AlgebraicComplexity.Tensor

universe u v w x y

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- If one legwise selection predicate implies another, selecting the weaker predicate first
does not change the realization obtained after the stronger selection. -/
theorem PartitionedTensor.select_select_realize_of_imp
    (P : PartitionedTensor (K := K) (A := A) V)
    (outer inner : ∀ c, A c → Prop)
    [∀ c a, Decidable (outer c a)] [∀ c a, Decidable (inner c a)]
    (himp : ∀ c a, inner c a → outer c a) :
    ((P.select outer).select inner).realize = (P.select inner).realize := by
  classical
  apply PartitionedTensor.realize_eq_of_support_eq
  · ext address
    simp only [PartitionedTensor.mem_select_support]
    constructor
    · rintro ⟨⟨hsource, _houter⟩, hinner⟩
      exact ⟨hsource, hinner⟩
    · rintro ⟨hsource, hinner⟩
      exact ⟨⟨hsource, fun c ↦ himp c (address c) (hinner c)⟩, hinner⟩
  · intro address _haddress
    rfl

/-- A selection on quotient labels restricts to any fine-label selection contained in its
legwise preimage.  This packages the two exact zeroings without unfolding a concrete type-class
predicate in the linear-algebra proof. -/
theorem Restricts.coarsen_select_to_select_of_imp
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c)
    (coarseKeep : ∀ c, B c → Prop) (fineKeep : ∀ c, A c → Prop)
    [∀ c b, Decidable (coarseKeep c b)] [∀ c a, Decidable (fineKeep c a)]
    (himp : ∀ c a, fineKeep c a → coarseKeep c (f c a)) :
    Restricts ((P.coarsen f).select coarseKeep).realize
      (P.select fineKeep).realize := by
  classical
  let preimageKeep : ∀ c, A c → Prop := fun c a ↦ coarseKeep c (f c a)
  have hback : Restricts ((P.coarsen f).select coarseKeep).realize
      (P.select preimageKeep).realize := by
    have h := (Isomorphic.partitionedCoarsen (P.select preimageKeep) f).symm.restricts
    have heq :
        ((P.select preimageKeep).coarsen f).realize =
          ((P.coarsen f).select coarseKeep).realize := by
      simpa [preimageKeep] using P.coarsen_select_preimage_realize f coarseKeep
    rw [← heq]
    exact h
  have hselect : Restricts (P.select preimageKeep).realize
      (P.select fineKeep).realize := by
    have h := Restricts.partitionedSelect (P.select preimageKeep) fineKeep
    rw [P.select_select_realize_of_imp preimageKeep fineKeep
      (fun c a ha ↦ himp c a ha)] at h
    exact h
  exact hback.trans hselect

/-- Coarsening after forming a positive power, then selecting the pushed-forward exact type on
each leg, restricts to the **entire** original fine type-selected tensor.  This is a global
variable projection, not a choice of one word.  It preserves a later inner type-class extraction
only when its source really is this whole selected quotient tensor.  In particular, it cannot be
applied to one coarse constituent isolated by hashing; that use requires a localized fiber
selection theorem.
-/
theorem Restricts.coarsenedPositivePowerSelectMappedTypes_to_fineTypes
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ) (fineType : ∀ c, A c → ℕ) :
    Restricts
      ((((P.positivePower n).coarsen
          (fun c ↦ positiveWordMap (f c) n)).select
        (fun c word ↦ word ∈ positiveTypeClass (B c) n
          (WordType.mappedType (f c) (fineType c)))).realize)
      (((P.positivePower n).select
        (fun c word ↦ word ∈ positiveTypeClass (A c) n (fineType c))).realize) := by
  classical
  apply Restricts.coarsen_select_to_select_of_imp
  intro c word hword
  exact positiveWordMap_mem_positiveTypeClass
    (f c) n (fineType c) word hword

/-- Indexed form of the selected-tensor bridge.  Every indexed source must be a copy of the whole
selected quotient tensor displayed in the theorem.  This is not a constituentwise localization
result and therefore cannot by itself preserve an inner `E2` family after coarse constituents
have been separated. -/
theorem Restricts.indexedDirectSum_coarsenedPositivePowerSelectMappedTypes_to_fineTypes
    {I : Type*} [Fintype I]
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ) (fineType : ∀ c, A c → ℕ) :
    Restricts
      (Tensor.indexedDirectSum (fun _i : I ↦
        (((P.positivePower n).coarsen
            (fun c ↦ positiveWordMap (f c) n)).select
          (fun c word ↦ word ∈ positiveTypeClass (B c) n
            (WordType.mappedType (f c) (fineType c)))).realize))
      (Tensor.indexedDirectSum (fun _i : I ↦
        ((P.positivePower n).select
          (fun c word ↦ word ∈ positiveTypeClass (A c) n (fineType c))).realize)) := by
  apply Restricts.indexedDirectSum
  intro _i
  exact Restricts.coarsenedPositivePowerSelectMappedTypes_to_fineTypes P f n fineType

/-- Quotient-first form of the whole-selected-tensor bridge.  The public constructor
`selectCoarsenedPositiveTypes` forms the power of the coarsened partition; power/coarsening
distributivity identifies it with the after-power coarsening used by
`coarsenedPositivePowerSelectMappedTypes_to_fineTypes`.  Consequently this restriction
preserves the **entire** fine-selected tensor.  The source is the whole selected quotient tensor,
not one of its isolated coarse constituents. -/
theorem Restricts.selectCoarsenedPositiveMappedTypes_to_fineTypes
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ) (fineType : ∀ c, A c → ℕ) :
    Restricts
      ((P.selectCoarsenedPositiveTypes f n
        (fun c ↦ WordType.mappedType (f c) (fineType c))).realize)
      (((P.positivePower n).select
        (fun c word ↦ word ∈ positiveTypeClass (A c) n (fineType c))).realize) := by
  exact
    (Isomorphic.selectCoarsenedPositiveTypes_to_afterPowerCoarsenedTypes
      P f n (fun c ↦ WordType.mappedType (f c) (fineType c))).restricts.trans
    (Restricts.coarsenedPositivePowerSelectMappedTypes_to_fineTypes
      P f n fineType)

/-- Indexed quotient-first bridge for copies of the whole selected quotient tensor.  The outer
index is untouched, but this statement does not apply to an indexed family of individual coarse
constituents. -/
theorem Restricts.indexedDirectSum_selectCoarsenedPositiveMappedTypes_to_fineTypes
    {I : Type*} [Fintype I]
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ) (fineType : ∀ c, A c → ℕ) :
    Restricts
      (Tensor.indexedDirectSum (fun _i : I ↦
        (P.selectCoarsenedPositiveTypes f n
          (fun c ↦ WordType.mappedType (f c) (fineType c))).realize))
      (Tensor.indexedDirectSum (fun _i : I ↦
        ((P.positivePower n).select
          (fun c word ↦ word ∈ positiveTypeClass (A c) n (fineType c))).realize)) := by
  apply Restricts.indexedDirectSum
  intro _i
  exact Restricts.selectCoarsenedPositiveMappedTypes_to_fineTypes P f n fineType

/-- Positive-word form of `WordType.typedWordMapFiber_nonempty`.  Every coarse word of the full
pushed-forward fine type admits a letterwise fine lift of exactly that fine type. -/
theorem exists_positiveWord_typed_lift
    {I : Type w} {J : Type x} [Fintype I] [Fintype J]
    (f : I → J) (n : ℕ) (a : I → ℕ) (target : PositiveWord J n)
    (ha : a ∈ WordType.types I (n + 1))
    (htarget : target ∈ positiveTypeClass J n (WordType.mappedType f a)) :
    ∃ source : PositiveWord I n,
      source ∈ positiveTypeClass I n a ∧ positiveWordMap f n source = target := by
  classical
  have htarget' : positiveWordEquiv J n target ∈
      WordType.typeClass (n + 1) (WordType.mappedType f a) := by
    rw [WordType.mem_typeClass]
    exact mem_positiveTypeClass.mp htarget
  obtain ⟨source, hsource⟩ :=
    WordType.typedWordMapFiber_nonempty f a (positiveWordEquiv J n target) ha htarget'
  have hsource' := WordType.mem_typedWordMapFiber.mp hsource
  let sourceWord : PositiveWord I n := (positiveWordEquiv I n).symm source
  refine ⟨sourceWord, ?_, ?_⟩
  · rw [mem_positiveTypeClass]
    simpa [sourceWord] using hsource'.1
  · apply (positiveWordEquiv J n).injective
    rw [positiveWordEquiv_map]
    simpa [sourceWord] using hsource'.2

namespace Restricts

private theorem coarsenedBlockComponentAt_comp_includeAt_of_ne
    (f : ∀ c, A c → B c)
    (chosen source : BlockAddress A) (target : BlockAddress B)
    (hchosen : coarsenBlockAddress f chosen = target)
    (hsource : coarsenBlockAddress f source = target)
    (c : Leg) (hne : source c ≠ chosen c) :
    coarsenedBlockComponentAt (K := K) (V := V) f chosen target hchosen c ∘ₗ
        coarsenedBlockIncludeAt (K := K) (V := V) f source target hsource c = 0 := by
  apply LinearMap.ext
  intro value
  simp only [coarsenedBlockComponentAt, coarsenedBlockIncludeAt,
    LinearMap.comp_apply]
  have hsubtype :
      (⟨source c, congrFun hsource c⟩ : BlockFiber f c (target c)) ≠
        ⟨chosen c, congrFun hchosen c⟩ := by
    intro h
    exact hne (congrArg Subtype.val h)
  simp [DirectSum.component.of, hsubtype]

/-- A constituent of a coarsened partition restricts to any chosen fine constituent in its
fiber.  Unlike `coarsenedTerm_of_eq`, this theorem starts from the whole fiber sum and proves
that the other fine addresses are annihilated by the three component projections. -/
theorem coarsen_constituent_of_eq
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (target : BlockAddress B)
    (source : BlockAddress A) (hsource : source ∈ P.support)
    (hmap : coarsenBlockAddress f source = target) :
    Restricts ((P.coarsen f).constituent target) (P.constituent source) := by
  classical
  refine ⟨coarsenedBlockComponentAt (K := K) (V := V) f source target hmap, ?_⟩
  rw [PartitionedTensor.coarsen_constituent]
  unfold coarsenedConstituent
  rw [map_sum]
  calc
    ∑ candidate ∈ P.support,
        map (coarsenedBlockComponentAt (K := K) (V := V) f source target hmap)
          (coarsenedTerm P f target candidate) =
        ∑ candidate ∈ P.support,
          if candidate = source then P.constituent source else 0 := by
      apply Finset.sum_congr rfl
      intro candidate hcandidate
      by_cases heq : candidate = source
      · subst candidate
        simp only [if_pos]
        unfold coarsenedTerm
        simp only [dif_pos hmap]
        exact map_coarsenedBlockComponentAt_includeAt
          f source target hmap (P.constituent source)
      · rw [if_neg heq]
        by_cases hcmap : coarsenBlockAddress f candidate = target
        · rw [coarsenedTerm_eq_map_of_eq P f target candidate hcmap]
          change
            (map (coarsenedBlockComponentAt (K := K) (V := V)
                f source target hmap) ∘ₗ
              map (coarsenedBlockIncludeAt (K := K) (V := V)
                f candidate target hcmap))
                (P.constituent candidate) = 0
          rw [← map_comp]
          have hcoord : ∃ c, candidate c ≠ source c := by
            by_contra h
            push Not at h
            exact heq (funext h)
          obtain ⟨c, hc⟩ := hcoord
          apply map_eq_zero_of_coord _ (P.constituent candidate) c
          exact coarsenedBlockComponentAt_comp_includeAt_of_ne
            f source candidate target hmap hcmap c hc
        · simp [coarsenedTerm, hcmap]
    _ = P.constituent source := by simp [hsource]

end Restricts

/-- Send a supported fine address to its supported coarse address. -/
def PartitionedTensor.coarsenSupportMap
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) : P.support → (P.coarsen f).support :=
  fun source ↦ ⟨coarsenBlockAddress f source.1,
    Finset.mem_image.mpr ⟨source.1, source.2, rfl⟩⟩

@[simp] theorem PartitionedTensor.coe_coarsenSupportMap
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (source : P.support) :
    (P.coarsenSupportMap f source).1 = coarsenBlockAddress f source.1 :=
  rfl

/-- Transposing a fine support word after mapping its letters to coarse support equals applying
the coarsening map to each of the three transposed leg words. -/
theorem PartitionedTensor.positiveSupportWordBlockAddress_coarsenSupportMap
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ) (word : PositiveWord P.support n) :
    positiveSupportWordBlockAddress (P.coarsen f).support n
        (positiveWordMap (P.coarsenSupportMap f) n word) =
      fun c ↦ positiveWordMap (f c) n
        (positiveSupportWordBlockAddress P.support n word c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rcases word with ⟨word, last⟩
      funext c
      change
        (positiveSupportWordBlockAddress (P.coarsen f).support n
            (positiveWordMap (P.coarsenSupportMap f) n word) c,
          f c (last.1 c)) =
        (positiveWordMap (f c) n
            (positiveSupportWordBlockAddress P.support n word c),
          f c (last.1 c))
      rw [congrFun (ih word) c]

namespace Restricts

/-- Universe-explicit positive support-word tensor for a coarsened block family. -/
noncomputable abbrev coarsenedPositiveSupportWordTensorSource
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ)
    (word : PositiveWord (P.coarsen f).support n) :=
  @PartitionedTensor.positiveSupportWordTensor.{u, max v w, x}
    K _ B _ _ (CoarsenedBlockSpace (V := V) f) _ _ (P.coarsen f) n word

/-- The coarse constituent tensor selected by a mapped support word restricts to the fine
constituent tensor selected by the original support word. -/
theorem coarsenedPositiveSupportWordTensor
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ) (word : PositiveWord P.support n) :
    Restricts
      (coarsenedPositiveSupportWordTensorSource P f n
        (positiveWordMap (P.coarsenSupportMap f) n word))
      (P.positiveSupportWordTensor n word) := by
  induction n with
  | zero =>
      exact coarsen_constituent_of_eq P f
        (coarsenBlockAddress f word.1) word.1 word.2 rfl
  | succ n ih =>
      rcases word with ⟨word, last⟩
      exact Restricts.external (ih word)
        (coarsen_constituent_of_eq P f
          (coarsenBlockAddress f last.1) last.1 last.2 rfl)

/-- Constituent-level coarse-to-fine bridge for positive powers.  The target address is written
as the legwise quotient of the chosen fine word, exactly as used by coarse hashing. -/
theorem coarsenedPositivePower_constituent_of_fineWord
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ) (word : PositiveWord P.support n) :
    Restricts
      ((P.coarsenedPositivePower f n).constituent
        (positiveSupportWordBlockAddress (P.coarsen f).support n
          (positiveWordMap (P.coarsenSupportMap f) n word)))
      ((P.positivePower n).constituent
        (positiveSupportWordBlockAddress P.support n word)) := by
  rw [PartitionedTensor.positivePower_constituent_positiveSupportWordBlockAddress,
    P.positivePower_constituent_positiveSupportWordBlockAddress]
  exact coarsenedPositiveSupportWordTensor P f n word

/-- **Restrict-then-compose form of the mapped coarse leaf.**  A coarse constituent whose word
has the pushed-forward fine type restricts to *whatever the fine blocks of that type restrict to*.

This is the weakest hypothesis under which the coarse-to-fine bridge produces a named target: the
only thing assumed about the fine side is the degeneration that is actually being transported,
required for the fine words of the prescribed type (one of which is the lift chosen here).  In
particular nothing is assumed letterwise about the individual base constituents of `P`, and
`P.support` need not be nonempty.

Both halves of the argument are already available: `exists_positiveWord_typed_lift` produces a
fine word of the prescribed type above the coarse word (integrality of the exact type is what
makes the lift exist), and `coarsenedPositivePower_constituent_of_fineWord` restricts the coarse
constituent to that fine block by projecting each leg of the coarse direct sum onto one fine
address.  Composing with the assumed fine degeneration finishes it. -/
theorem coarsenedPositivePower_constituent_of_mappedType
    {W : Leg → Type*} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) {r : ℕ}
    (fineType : P.support → ℕ)
    (coarseWord : PositiveWord (P.coarsen f).support r)
    {target : Tensor3 K W}
    (hlegal : fineType ∈ WordType.types P.support (r + 1))
    (hcoarse : coarseWord ∈ positiveTypeClass (P.coarsen f).support r
      (WordType.mappedType (P.coarsenSupportMap f) fineType))
    (hfine : ∀ fineWord ∈ positiveTypeClass P.support r fineType,
      Restricts
        ((P.positivePower r).constituent
          (positiveSupportWordBlockAddress P.support r fineWord))
        target) :
    Restricts
      ((P.coarsenedPositivePower f r).constituent
        (positiveSupportWordBlockAddress (P.coarsen f).support r coarseWord))
      target := by
  obtain ⟨fineWord, hfineType, hfineMap⟩ :=
    exists_positiveWord_typed_lift (P.coarsenSupportMap f) r fineType coarseWord hlegal hcoarse
  subst coarseWord
  exact (coarsenedPositivePower_constituent_of_fineWord P f r fineWord).trans
    (hfine fineWord hfineType)

/-- Copywise form of `coarsenedPositivePower_constituent_of_mappedType`: an indexed family of
coarse constituents of the pushed-forward type restricts, index set unchanged, to the indexed
direct sum of the common fine target.

`Tensor.indexedDirectSum` is the **external** direct sum, so no disjointness hypothesis is needed
*here*.  The paper's copywise sentence in `lem:mapped-coarse-leaf` is about an indexed family
realized inside one ambient tensor, and in that reading it is false without legwise disjointness:
two coarse constituents sharing an `X` label cannot receive different `X` projections.  The
disjointness that licenses the identification of this external sum with a subtensor of the ambient
tensor is the `Set.InjOn` hypothesis carried by `thm:coarse-fine-interface` and discharged through
`Tensor/CompatibilityZeroing.lean`; it is not weakened, hidden, or assumed by this statement. -/
theorem indexedDirectSum_coarsenedPositivePower_constituent_of_mappedType
    {I : Type*} [Fintype I]
    {W : Leg → Type*} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) {r : ℕ}
    (fineType : P.support → ℕ)
    (coarseWord : I → PositiveWord (P.coarsen f).support r)
    {target : Tensor3 K W}
    (hlegal : fineType ∈ WordType.types P.support (r + 1))
    (hcoarse : ∀ i, coarseWord i ∈ positiveTypeClass (P.coarsen f).support r
      (WordType.mappedType (P.coarsenSupportMap f) fineType))
    (hfine : ∀ fineWord ∈ positiveTypeClass P.support r fineType,
      Restricts
        ((P.positivePower r).constituent
          (positiveSupportWordBlockAddress P.support r fineWord))
        target) :
    Restricts
      (Tensor.indexedDirectSum (fun i ↦
        (P.coarsenedPositivePower f r).constituent
          (positiveSupportWordBlockAddress (P.coarsen f).support r (coarseWord i))))
      (Tensor.indexedDirectSum (fun _i : I ↦ target)) := by
  apply Restricts.indexedDirectSum
  intro i
  exact coarsenedPositivePower_constituent_of_mappedType P f fineType (coarseWord i)
    hlegal (hcoarse i) hfine

end Restricts

namespace RationalTypedLeaf

/-- A prescribed fine rational typed leaf can be selected inside the coarse constituent induced
by the same fine support word.  Matrix dimensions are definitionally the original fine-leaf
dimensions; coarsening costs no copy and contributes no extra entropy term. -/
theorem coarsenedPositivePower_constituent_matrixMultiplication_proportional
    {C : Leg → Type y} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (P : PartitionedTensor (K := K) (A := A) V)
    [Nonempty P.support]
    (f : ∀ c, A c → B c)
    (leaf : RationalTypedLeaf P.support C)
    (hconstituent : ∀ s : P.support,
      Restricts (P.constituent s.1)
        (matrixMultiplication (K := K)
          (leaf.dimension s .X) (leaf.dimension s .Y) (leaf.dimension s .Z)))
    {r k : ℕ} (word : PositiveWord P.support r)
    (hword : word ∈ positiveTypeClass P.support r
      (WordType.proportionalCounts leaf.profile.count k)) :
    Restricts
      ((P.coarsenedPositivePower f r).constituent
        (positiveSupportWordBlockAddress (P.coarsen f).support r
          (positiveWordMap (P.coarsenSupportMap f) r word)))
      (matrixMultiplication (K := K)
        (leaf.dimensionProduct .X ^ k)
        (leaf.dimensionProduct .Y ^ k)
        (leaf.dimensionProduct .Z ^ k)) :=
  (Restricts.coarsenedPositivePower_constituent_of_fineWord P f r word).trans
    (leaf.positivePower_constituent_matrixMultiplication_proportional
      P hconstituent word hword)

/-- **`lem:mapped-coarse-leaf` with the paper's own hypothesis.**  Every coarse support word of
the pushed-forward full joint profile contains a fine rational typed leaf with the original matrix
dimensions, assuming only that *the fine blocks of the prescribed proportional type already
degenerate* to those dimensions.

The paper hypothesizes a rational typed leaf that degenerates to `⟨A, B, C⟩`, not a degeneration of
every supported base constituent to its own `⟨A, B, C⟩`; the letterwise premise is a strictly
stronger statement about `P` that the argument never uses.  Weakening it is exactly the
restrict-then-compose step: restrict to the fine lift, then compose with the given degeneration,
which is closed under tensor powers.  `Nonempty P.support` is likewise not needed here.

`coarsenedPositivePower_constituent_matrixMultiplication_of_mappedType` below is the letterwise
corollary, kept because the Coppersmith--Winograd clients supply their leaf that way. -/
theorem coarsenedPositivePower_constituent_matrixMultiplication_of_mappedType_of_fineDegeneration
    {C : Leg → Type y} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c)
    (leaf : RationalTypedLeaf P.support C)
    {r k : ℕ}
    (coarseWord : PositiveWord (P.coarsen f).support r)
    (hlegal : WordType.proportionalCounts leaf.profile.count k ∈
      WordType.types P.support (r + 1))
    (hcoarse : coarseWord ∈ positiveTypeClass (P.coarsen f).support r
      (WordType.mappedType (P.coarsenSupportMap f)
        (WordType.proportionalCounts leaf.profile.count k)))
    (hfine : ∀ fineWord ∈ positiveTypeClass P.support r
        (WordType.proportionalCounts leaf.profile.count k),
      Restricts
        ((P.positivePower r).constituent
          (positiveSupportWordBlockAddress P.support r fineWord))
        (matrixMultiplication (K := K)
          (leaf.dimensionProduct .X ^ k)
          (leaf.dimensionProduct .Y ^ k)
          (leaf.dimensionProduct .Z ^ k))) :
    Restricts
      ((P.coarsenedPositivePower f r).constituent
        (positiveSupportWordBlockAddress (P.coarsen f).support r coarseWord))
      (matrixMultiplication (K := K)
        (leaf.dimensionProduct .X ^ k)
        (leaf.dimensionProduct .Y ^ k)
        (leaf.dimensionProduct .Z ^ k)) :=
  Restricts.coarsenedPositivePower_constituent_of_mappedType P f
    (WordType.proportionalCounts leaf.profile.count k) coarseWord hlegal hcoarse hfine

/-- Every coarse support word of the pushed-forward full joint profile contains a fine rational
typed leaf with the original matrix dimensions.  This is the exact theorem needed after coarse
hashing: the coarse word itself, rather than only its three block-label marginals, must have the
pushed-forward fine support type.

The letterwise premise `hconstituent` is stronger than the paper's hypothesis; see
`coarsenedPositivePower_constituent_matrixMultiplication_of_mappedType_of_fineDegeneration`, of
which this is the specialization obtained by proving the fine degeneration from `hconstituent`. -/
theorem coarsenedPositivePower_constituent_matrixMultiplication_of_mappedType
    {C : Leg → Type y} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (P : PartitionedTensor (K := K) (A := A) V)
    [Nonempty P.support]
    (f : ∀ c, A c → B c)
    (leaf : RationalTypedLeaf P.support C)
    (hconstituent : ∀ s : P.support,
      Restricts (P.constituent s.1)
        (matrixMultiplication (K := K)
          (leaf.dimension s .X) (leaf.dimension s .Y) (leaf.dimension s .Z)))
    {r k : ℕ}
    (coarseWord : PositiveWord (P.coarsen f).support r)
    (hlegal : WordType.proportionalCounts leaf.profile.count k ∈
      WordType.types P.support (r + 1))
    (hcoarse : coarseWord ∈ positiveTypeClass (P.coarsen f).support r
      (WordType.mappedType (P.coarsenSupportMap f)
        (WordType.proportionalCounts leaf.profile.count k))) :
    Restricts
      ((P.coarsenedPositivePower f r).constituent
        (positiveSupportWordBlockAddress (P.coarsen f).support r coarseWord))
      (matrixMultiplication (K := K)
        (leaf.dimensionProduct .X ^ k)
        (leaf.dimensionProduct .Y ^ k)
        (leaf.dimensionProduct .Z ^ k)) :=
  coarsenedPositivePower_constituent_matrixMultiplication_of_mappedType_of_fineDegeneration
    P f leaf coarseWord hlegal hcoarse
    (fun fineWord hfineWord ↦
      leaf.positivePower_constituent_matrixMultiplication_proportional P hconstituent
        fineWord hfineWord)

/-- Copy-count-preserving indexed form.  A family of extracted coarse constituents indexed by
`I` yields a direct sum of matrix-multiplication tensors indexed by the same `I`; no conditional
fiber cardinality is multiplied into the retained-copy count. -/
theorem indexedDirectSum_coarsenedPositivePower_constituent_matrixMultiplication_of_mappedType
    {I : Type*} [Fintype I]
    {C : Leg → Type y} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (P : PartitionedTensor (K := K) (A := A) V)
    [Nonempty P.support]
    (f : ∀ c, A c → B c)
    (leaf : RationalTypedLeaf P.support C)
    (hconstituent : ∀ s : P.support,
      Restricts (P.constituent s.1)
        (matrixMultiplication (K := K)
          (leaf.dimension s .X) (leaf.dimension s .Y) (leaf.dimension s .Z)))
    {r k : ℕ}
    (coarseWord : I → PositiveWord (P.coarsen f).support r)
    (hlegal : WordType.proportionalCounts leaf.profile.count k ∈
      WordType.types P.support (r + 1))
    (hcoarse : ∀ i, coarseWord i ∈ positiveTypeClass (P.coarsen f).support r
      (WordType.mappedType (P.coarsenSupportMap f)
        (WordType.proportionalCounts leaf.profile.count k))) :
    Restricts
      (Tensor.indexedDirectSum (fun i ↦
        (P.coarsenedPositivePower f r).constituent
          (positiveSupportWordBlockAddress (P.coarsen f).support r (coarseWord i))))
      (Tensor.indexedDirectSum (fun _i : I ↦
        matrixMultiplication (K := K)
          (leaf.dimensionProduct .X ^ k)
          (leaf.dimensionProduct .Y ^ k)
          (leaf.dimensionProduct .Z ^ k))) := by
  apply Restricts.indexedDirectSum
  intro i
  exact coarsenedPositivePower_constituent_matrixMultiplication_of_mappedType
    P f leaf hconstituent (coarseWord i) hlegal (hcoarse i)

end RationalTypedLeaf

end AlgebraicComplexity.Tensor
