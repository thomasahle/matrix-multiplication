/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ProgressionFree
import AlgebraicComplexity.Combinatorics.TwoLegHashingExtraction
import AlgebraicComplexity.Examples.CoppersmithWinograd112Partition
import AlgebraicComplexity.MatrixMultiplication.PartitionedPowerHashing
import AlgebraicComplexity.Tensor.TypeExtraction

/-!
# Type counting and two-leg hashing for the exceptional CW `112` constituent

The special Coppersmith--Winograd analysis of the `112` constituent takes an even tensor
power and retains words containing `L,L,G,G` copies of its four supported block addresses.
The X and Y marginal words both have type `(L + G, L + G)`, whereas the Z marginal has type
`(L,L,2G)`.  This asymmetry is essential: hashing must isolate X and Y words while allowing
many selected terms to share one Z word, thereby forming the C-tensors used in the value bound.

This file proves the exact finite type identities, packages the four-address support as a legal
constant-sum affine-hashing instance, and obtains a two-leg-isolated family from the reusable
hashing theorem.  It deliberately stops before assigning a value to the resulting shared-Z
groups; that tensor-theoretic C-tensor step belongs in a subsequent module.

The construction follows the proof on journal pages 270--272 of Coppersmith and Winograd,
"Matrix Multiplication via Arithmetic Progressions" (1990), stored locally as
`papers/MMult1987.pdf`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

/-- The four named elements of the supported `112` block alphabet. -/
abbrev cw112DiagonalFirstS : cw112BlockSupport :=
  ⟨cw112DiagonalFirstAddress, by decide⟩

abbrev cw112DiagonalSecondS : cw112BlockSupport :=
  ⟨cw112DiagonalSecondAddress, by decide⟩

abbrev cw112CrossFirstS : cw112BlockSupport :=
  ⟨cw112CrossFirstAddress, by decide⟩

abbrev cw112CrossSecondS : cw112BlockSupport :=
  ⟨cw112CrossSecondAddress, by decide⟩

/-- Expanding a sum over the four-element supported alphabet in its canonical order. -/
theorem sum_cw112BlockSupportSubtype (f : cw112BlockSupport → ℕ) :
    ∑ s, f s =
      f cw112DiagonalFirstS + f cw112DiagonalSecondS +
        f cw112CrossFirstS + f cw112CrossSecondS := by
  classical
  rw [show (Finset.univ : Finset cw112BlockSupport) =
    {cw112DiagonalFirstS, cw112DiagonalSecondS,
      cw112CrossFirstS, cw112CrossSecondS} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  omega

/-- Expanding a product over the four-element supported alphabet. -/
theorem prod_cw112BlockSupportSubtype (f : cw112BlockSupport → ℕ) :
    ∏ s, f s =
      f cw112DiagonalFirstS * f cw112DiagonalSecondS *
        f cw112CrossFirstS * f cw112CrossSecondS := by
  classical
  rw [show (Finset.univ : Finset cw112BlockSupport) =
    {cw112DiagonalFirstS, cw112DiagonalSecondS,
      cw112CrossFirstS, cw112CrossSecondS} by decide]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  ring

/-- Length-minus-one convention used by `PositiveWord`: the selected words have length
`2 * (L + G)`. -/
def cw112TypeDepth (L G : ℕ) : ℕ := 2 * (L + G) - 1

/-- For a nonempty selected type, converting back from the positive-word depth recovers the
paper's even word length. -/
theorem cw112TypeDepth_add_one {L G : ℕ} (hLG : 0 < L + G) :
    cw112TypeDepth L G + 1 = 2 * (L + G) := by
  unfold cw112TypeDepth
  omega

/-- Joint multiplicity type `L,L,G,G` on the four supported addresses.  The two grid addresses
are exactly the two entries assigned multiplicity `G`. -/
def cw112NaturalType (L G : ℕ) : cw112BlockSupport → ℕ :=
  fun s ↦ match s.1 .Z with
    | .firstCorner => L
    | .secondCorner => L
    | .grid => G

/-- X and Y both see the balanced binary marginal `(L + G, L + G)`. -/
def cw112SideMarginalType (L G : ℕ) : CW112Side → ℕ
  | .first => L + G
  | .second => L + G

/-- Z sees the three-part marginal `(L,L,2G)`. -/
def cw112ZMarginalType (L G : ℕ) : CW112ZBlock → ℕ
  | .firstCorner => L
  | .secondCorner => L
  | .grid => 2 * G

/-- Leg-dependent marginal type of the selected `112` address words. -/
def cw112MarginalType (L G : ℕ) : ∀ c, CW112Block c → ℕ
  | .X => cw112SideMarginalType L G
  | .Y => cw112SideMarginalType L G
  | .Z => cw112ZMarginalType L G

/-- The four joint multiplicities sum to the even word length.  Proof sketch: enumerate the
four-element support and simplify its two diagonal and two grid entries. -/
theorem cw112NaturalType_mem_types {L G : ℕ} (hLG : 0 < L + G) :
    cw112NaturalType L G ∈
      WordType.types cw112BlockSupport (cw112TypeDepth L G + 1) := by
  rw [WordType.mem_types, cw112TypeDepth_add_one hLG]
  rw [sum_cw112BlockSupportSubtype]
  simp [cw112NaturalType, cw112DiagonalFirstAddress,
    cw112DiagonalSecondAddress, cw112CrossFirstAddress, cw112CrossSecondAddress,
    cw112BlockAddress]
  omega

/-- Every leg marginal sums to the same even word length. -/
theorem cw112MarginalType_mem_types {L G : ℕ} (hLG : 0 < L + G) (c : Leg) :
    cw112MarginalType L G c ∈
      WordType.types (CW112Block c) (cw112TypeDepth L G + 1) := by
  rw [WordType.mem_types, cw112TypeDepth_add_one hLG]
  cases c with
  | X =>
      rw [show (Finset.univ : Finset CW112Side) = {.first, .second} by decide]
      simp [cw112MarginalType, cw112SideMarginalType]
      omega
  | Y =>
      rw [show (Finset.univ : Finset CW112Side) = {.first, .second} by decide]
      simp [cw112MarginalType, cw112SideMarginalType]
      omega
  | Z =>
      rw [show (Finset.univ : Finset CW112ZBlock) =
        {.firstCorner, .secondCorner, .grid} by decide]
      simp [cw112MarginalType, cw112ZMarginalType]
      omega

/-- Projecting the joint `L,L,G,G` type to any leg gives the stated marginal.  Proof sketch:
enumerate the four support addresses and inspect their label on the chosen leg. -/
theorem cw112_mappedType_eq_marginal (L G : ℕ) (c : Leg) :
    WordType.mappedType (fun s : cw112BlockSupport ↦ s.1 c)
      (cw112NaturalType L G) = cw112MarginalType L G c := by
  funext b
  unfold WordType.mappedType WordType.letterFiber
  simp only [Finset.sum_filter]
  change (∑ s : cw112BlockSupport,
    if s.1 c = b then cw112NaturalType L G s else 0) = _
  rw [sum_cw112BlockSupportSubtype]
  cases c with
  | X =>
      cases b <;>
        simp [cw112NaturalType, cw112MarginalType, cw112SideMarginalType,
          cw112DiagonalFirstAddress, cw112DiagonalSecondAddress,
          cw112CrossFirstAddress, cw112CrossSecondAddress, cw112BlockAddress]
  | Y =>
      cases b <;>
        simp [cw112NaturalType, cw112MarginalType, cw112SideMarginalType,
          cw112DiagonalFirstAddress, cw112DiagonalSecondAddress,
          cw112CrossFirstAddress, cw112CrossSecondAddress, cw112BlockAddress]
  | Z =>
      cases b
      all_goals simp [cw112NaturalType, cw112MarginalType, cw112ZMarginalType,
        cw112DiagonalFirstAddress, cw112DiagonalSecondAddress,
        cw112CrossFirstAddress, cw112CrossSecondAddress, cw112BlockAddress]
      all_goals omega

/-- Selected positive address words of joint type `L,L,G,G`. -/
noncomputable def cw112TypeWords (L G : ℕ) :
    Finset (PositiveWord cw112BlockSupport (cw112TypeDepth L G)) :=
  positiveTypeClass cw112BlockSupport (cw112TypeDepth L G) (cw112NaturalType L G)

/-- The exact number of selected joint words is the multinomial coefficient of their four
multiplicities. -/
theorem card_cw112TypeWords_eq_multinomial {L G : ℕ} (hLG : 0 < L + G) :
    (cw112TypeWords L G).card =
      Nat.multinomial Finset.univ (cw112NaturalType L G) := by
  rw [cw112TypeWords, card_positiveTypeClass,
    WordType.card_typeClass_eq_multinomial _ (cw112NaturalType_mem_types hLG)]

/-- The selected joint type is inhabited whenever its even length is positive. -/
theorem cw112TypeWords_nonempty {L G : ℕ} (hLG : 0 < L + G) :
    (cw112TypeWords L G).Nonempty := by
  rw [← Finset.card_pos, card_cw112TypeWords_eq_multinomial hLG]
  exact Nat.multinomial_pos _ _

/-- Exact cardinality of any of the three marginal type classes. -/
theorem card_cw112MarginalTypeClass_eq_multinomial {L G : ℕ}
    (hLG : 0 < L + G) (c : Leg) :
    (WordType.typeClass (cw112TypeDepth L G + 1)
      (cw112MarginalType L G c)).card =
        Nat.multinomial Finset.univ (cw112MarginalType L G c) := by
  exact WordType.card_typeClass_eq_multinomial _
    (cw112MarginalType_mem_types hLG c)

/-- Factorial specification of the joint `L,L,G,G` multinomial. -/
theorem cw112JointMultinomial_spec (L G : ℕ) :
    (Nat.factorial L * Nat.factorial L * Nat.factorial G * Nat.factorial G) *
        Nat.multinomial Finset.univ (cw112NaturalType L G) =
      Nat.factorial (2 * (L + G)) := by
  have h := Nat.multinomial_spec (Finset.univ : Finset cw112BlockSupport)
    (cw112NaturalType L G)
  change (∏ s : cw112BlockSupport, Nat.factorial (cw112NaturalType L G s)) *
      Nat.multinomial Finset.univ (cw112NaturalType L G) =
    Nat.factorial (∑ s : cw112BlockSupport, cw112NaturalType L G s) at h
  rw [prod_cw112BlockSupportSubtype, sum_cw112BlockSupportSubtype] at h
  rw [show 2 * (L + G) = L + L + G + G by omega]
  simpa [cw112NaturalType, cw112DiagonalFirstAddress,
    cw112DiagonalSecondAddress, cw112CrossFirstAddress, cw112CrossSecondAddress,
    cw112BlockAddress] using h

/-- Factorial specification of the Z marginal multinomial `(L,L,2G)`. -/
theorem cw112ZMultinomial_spec (L G : ℕ) :
    (Nat.factorial L * Nat.factorial L * Nat.factorial (2 * G)) *
        Nat.multinomial Finset.univ (cw112ZMarginalType L G) =
      Nat.factorial (2 * (L + G)) := by
  have h := Nat.multinomial_spec (Finset.univ : Finset CW112ZBlock)
    (cw112ZMarginalType L G)
  change (∏ z : CW112ZBlock, Nat.factorial (cw112ZMarginalType L G z)) *
      Nat.multinomial Finset.univ (cw112ZMarginalType L G) =
    Nat.factorial (∑ z : CW112ZBlock, cw112ZMarginalType L G z) at h
  have hprod : (∏ z : CW112ZBlock, Nat.factorial (cw112ZMarginalType L G z)) =
      Nat.factorial L * Nat.factorial L * Nat.factorial (2 * G) := by
    rw [show (Finset.univ : Finset CW112ZBlock) =
      {.firstCorner, .secondCorner, .grid} by decide]
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_singleton]
    simp [cw112ZMarginalType]
    ring
  have hsum : (∑ z : CW112ZBlock, cw112ZMarginalType L G z) =
      2 * (L + G) := by
    rw [show (Finset.univ : Finset CW112ZBlock) =
      {.firstCorner, .secondCorner, .grid} by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    simp [cw112ZMarginalType]
    omega
  rw [hprod, hsum] at h
  simpa [cw112ZMarginalType] using h

/-- The binary X/Y marginal multinomial is the central binomial coefficient. -/
theorem cw112SideMultinomial_eq_choose (L G : ℕ) :
    Nat.multinomial Finset.univ (cw112SideMarginalType L G) =
      Nat.choose (2 * (L + G)) (L + G) := by
  rw [show (Finset.univ : Finset CW112Side) = {.first, .second} by decide,
    Nat.binomial_eq_choose (by decide)]
  simp [cw112SideMarginalType]
  congr 1
  omega

/-- Splitting `2G` grid positions equally between the two cross addresses contributes the
central binomial factor `choose (2G) G`. -/
theorem cw112GridChoose_spec (G : ℕ) :
    (Nat.factorial G * Nat.factorial G) * Nat.choose (2 * G) G =
      Nat.factorial (2 * G) := by
  have h := Nat.choose_mul_factorial_mul_factorial (n := 2 * G) (k := G) (by omega)
  rw [show 2 * G - G = G by omega] at h
  calc
    (Nat.factorial G * Nat.factorial G) * Nat.choose (2 * G) G =
        Nat.choose (2 * G) G * Nat.factorial G * Nat.factorial G := by ring
    _ = Nat.factorial (2 * G) := h

/-- A fixed Z word of type `(L,L,2G)` has exactly `choose (2G) G` compatible joint words.
Algebraically, multiplying the Z marginal multinomial by this grid split recovers the joint
`L,L,G,G` multinomial. -/
theorem cw112ZMultinomial_mul_choose_eq_joint (L G : ℕ) :
    Nat.multinomial Finset.univ (cw112ZMarginalType L G) *
        Nat.choose (2 * G) G =
      Nat.multinomial Finset.univ (cw112NaturalType L G) := by
  let d := Nat.factorial L * Nat.factorial L *
    (Nat.factorial G * Nat.factorial G)
  apply Nat.eq_of_mul_eq_mul_left (n := d) (by
    dsimp [d]
    positivity)
  calc
    d * (Nat.multinomial Finset.univ (cw112ZMarginalType L G) *
        Nat.choose (2 * G) G) =
      (Nat.factorial L * Nat.factorial L * Nat.factorial (2 * G)) *
        Nat.multinomial Finset.univ (cw112ZMarginalType L G) := by
          rw [← cw112GridChoose_spec G]
          simp only [d]
          ring
    _ = Nat.factorial (2 * (L + G)) := cw112ZMultinomial_spec L G
    _ = d * Nat.multinomial Finset.univ (cw112NaturalType L G) := by
      simpa [d, mul_assoc] using (cw112JointMultinomial_spec L G).symm

/-- Choosing `L` diagonal positions within each of the two size-`L+G` side words gives the
square of a binomial coefficient. -/
theorem cw112SideChoose_spec (L G : ℕ) :
    (Nat.factorial L * Nat.factorial G) * Nat.choose (L + G) L =
      Nat.factorial (L + G) := by
  have h := Nat.choose_mul_factorial_mul_factorial
    (n := L + G) (k := L) (by omega)
  rw [show L + G - L = G by omega] at h
  calc
    (Nat.factorial L * Nat.factorial G) * Nat.choose (L + G) L =
        Nat.choose (L + G) L * Nat.factorial L * Nat.factorial G := by ring
    _ = Nat.factorial (L + G) := h

/-- The binary side marginal count times the two independent side-splitting choices equals the
joint `L,L,G,G` count. -/
theorem cw112SideMultinomial_mul_choose_sq_eq_joint (L G : ℕ) :
    Nat.multinomial Finset.univ (cw112SideMarginalType L G) *
        (Nat.choose (L + G) L) ^ 2 =
      Nat.multinomial Finset.univ (cw112NaturalType L G) := by
  let d := (Nat.factorial L * Nat.factorial G) ^ 2
  apply Nat.eq_of_mul_eq_mul_left (n := d) (by
    dsimp [d]
    positivity)
  calc
    d * (Nat.multinomial Finset.univ (cw112SideMarginalType L G) *
        Nat.choose (L + G) L ^ 2) =
      (Nat.factorial (L + G) * Nat.factorial (L + G)) *
        Nat.multinomial Finset.univ (cw112SideMarginalType L G) := by
          rw [← cw112SideChoose_spec L G]
          simp only [d]
          ring
    _ = Nat.factorial (2 * (L + G)) := by
      rw [cw112SideMultinomial_eq_choose]
      exact cw112GridChoose_spec (L + G)
    _ = d * Nat.multinomial Finset.univ (cw112NaturalType L G) := by
      simpa [d, pow_two, mul_assoc, mul_left_comm, mul_comm] using
        (cw112JointMultinomial_spec L G).symm

/-- A selected support word projects on each leg to the exact marginal type class. -/
theorem cw112LegWord_mem_marginalTypeClass
    (L G : ℕ) (q : PositiveWord cw112BlockSupport (cw112TypeDepth L G))
    (hq : q ∈ cw112TypeWords L G) (c : Leg) :
    positiveWordEquiv (CW112Block c) (cw112TypeDepth L G)
        (PartitionHashEncoding.supportWordAddress
          (A := CW112Block) (support := cw112BlockSupport)
          (cw112TypeDepth L G) q c) ∈
      WordType.typeClass (cw112TypeDepth L G + 1)
        (cw112MarginalType L G c) := by
  rw [WordType.mem_typeClass]
  rw [PartitionHashEncoding.positiveWordEquiv_supportWordAddress
    (A := CW112Block) (support := cw112BlockSupport)]
  change WordType.multiplicity
    ((fun s : cw112BlockSupport ↦ s.1 c) ∘
      positiveWordEquiv cw112BlockSupport (cw112TypeDepth L G) q) = _
  rw [WordType.multiplicity_comp_eq_mappedType,
    mem_positiveTypeClass.mp hq, cw112_mappedType_eq_marginal]

/-- Field labels `0,1` on X/Y and `2,0,1` on Z realize the integral tight-support weights. -/
def cw112BlockFieldValue {R : Type*} [OfNat R 0] [OfNat R 1] [OfNat R 2] :
    ∀ c, CW112Block c → R
  | .X, .first => 0
  | .X, .second => 1
  | .Y, .first => 0
  | .Y, .second => 1
  | .Z, .firstCorner => 2
  | .Z, .secondCorner => 0
  | .Z, .grid => 1

/-- The block labels remain injective over every field of odd characteristic. -/
theorem cw112BlockFieldValue_injective
    {R : Type*} [Field R] [NeZero (2 : R)] (c : Leg) :
    Function.Injective (cw112BlockFieldValue (R := R) c) := by
  cases c with
  | X =>
      intro a b h
      cases a <;> cases b <;> simp_all [cw112BlockFieldValue]
  | Y =>
      intro a b h
      cases a <;> cases b <;> simp_all [cw112BlockFieldValue]
  | Z =>
      intro a b h
      cases a <;> cases b
      · rfl
      · exact ((NeZero.ne (2 : R)) (by simpa [cw112BlockFieldValue] using h)).elim
      · exfalso
        have h' : (1 : R) + 1 = 1 + 0 := by
          simpa [cw112BlockFieldValue, one_add_one_eq_two] using h
        exact one_ne_zero (add_left_cancel h')
      · exact ((NeZero.ne (2 : R)) (by simpa [cw112BlockFieldValue] using h.symm)).elim
      · rfl
      · simp [cw112BlockFieldValue] at h
      · exfalso
        have h' : (1 : R) + 0 = 1 + 1 := by
          simpa [cw112BlockFieldValue, one_add_one_eq_two] using h
        exact zero_ne_one (add_left_cancel h')
      · simp [cw112BlockFieldValue] at h
      · rfl

/-- The four-address `112` support as a legal constant-sum affine-hashing support. -/
def cw112PartitionHashEncoding
    {R : Type*} [Field R] [NeZero (2 : R)] :
    PartitionHashEncoding (R := R) cw112BlockSupport where
  encode := cw112BlockFieldValue
  target := 2
  support_nonempty := ⟨cw112DiagonalFirstAddress, by decide⟩
  encode_injective := cw112BlockFieldValue_injective
  legal s hs := by
    simp only [cw112BlockSupport, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl <;>
      norm_num [cw112DiagonalFirstAddress, cw112DiagonalSecondAddress,
        cw112CrossFirstAddress, cw112CrossSecondAddress, cw112BlockAddress,
        cw112BlockFieldValue, one_add_one_eq_two]

/-- Encoded legal triples associated to all selected joint-type words. -/
noncomputable def cw112TypeTargets
    {R : Type*} [Field R] [NeZero (2 : R)] (L G : ℕ) :
    Finset (ProgressionHash.LegalTriple R (Fin (cw112TypeDepth L G + 1)) 2) :=
  (cw112PartitionHashEncoding (R := R)).legalTargets
    (cw112TypeDepth L G) (cw112TypeWords L G)

/-- Encoding the selected words as legal triples preserves their cardinality. -/
@[simp] theorem card_cw112TypeTargets
    {R : Type*} [Field R] [NeZero (2 : R)] (L G : ℕ) :
    (cw112TypeTargets (R := R) L G).card = (cw112TypeWords L G).card := by
  exact PartitionHashEncoding.card_legalTargets _ _ _

/-- Common X/Y typed-fiber size, defined as the exact joint-to-marginal type-class ratio. -/
noncomputable def cw112XYFiberSize (L G : ℕ) : ℕ :=
  (cw112TypeWords L G).card /
    (WordType.typeClass (cw112TypeDepth L G + 1)
      (cw112SideMarginalType L G)).card

/-- The X/Y marginal class times the common fiber size is exactly the joint class.  Proof
sketch: choose any joint-type word and apply the typed-word double-counting theorem to X. -/
theorem cw112XYMarginalCard_mul_fiberSize {L G : ℕ} (hLG : 0 < L + G) :
    (WordType.typeClass (cw112TypeDepth L G + 1)
        (cw112SideMarginalType L G)).card * cw112XYFiberSize L G =
      (cw112TypeWords L G).card := by
  unfold cw112XYFiberSize
  exact Nat.mul_div_cancel'
    (by
      obtain ⟨q, hq⟩ := cw112TypeWords_nonempty hLG
      let target := (fun s : cw112BlockSupport ↦ s.1 .X) ∘
        positiveWordEquiv cw112BlockSupport (cw112TypeDepth L G) q
      have htarget : target ∈ WordType.typeClass (cw112TypeDepth L G + 1)
          (cw112SideMarginalType L G) := by
        rw [WordType.mem_typeClass]
        unfold target
        rw [WordType.multiplicity_comp_eq_mappedType,
          mem_positiveTypeClass.mp hq]
        simpa [cw112MarginalType] using cw112_mappedType_eq_marginal L G .X
      have hdouble := WordType.card_targetType_mul_card_typedWordMapFiber
        (fun s : cw112BlockSupport ↦ s.1 .X) (cw112NaturalType L G) target
        (by
          rw [cw112_mappedType_eq_marginal]
          exact htarget)
      have hsource :
          (WordType.typeClass (cw112TypeDepth L G + 1)
            (cw112NaturalType L G)).card = (cw112TypeWords L G).card :=
        (card_positiveTypeClass (I := cw112BlockSupport) (cw112TypeDepth L G)
          (cw112NaturalType L G)).symm
      rw [show WordType.mappedType (fun s : cw112BlockSupport ↦ s.1 .X)
        (cw112NaturalType L G) = cw112SideMarginalType L G by
          simpa [cw112MarginalType] using cw112_mappedType_eq_marginal L G .X,
        hsource] at hdouble
      exact ⟨_, hdouble.symm⟩)

/-- The common X/Y typed-fiber size is the paper's explicit degree
`choose (L + G) L ^ 2`: each side word independently chooses which `L` of its `L+G`
positions carry a diagonal rather than a cross address. -/
theorem cw112XYFiberSize_eq_choose_sq {L G : ℕ} (hLG : 0 < L + G) :
    cw112XYFiberSize L G = Nat.choose (L + G) L ^ 2 := by
  let marginalCard := (WordType.typeClass (cw112TypeDepth L G + 1)
    (cw112SideMarginalType L G)).card
  have hmarginal : marginalCard =
      Nat.multinomial Finset.univ (cw112SideMarginalType L G) := by
    simpa [marginalCard, cw112MarginalType] using
      card_cw112MarginalTypeClass_eq_multinomial hLG .X
  have hmarginalPos : 0 < marginalCard := by
    dsimp [marginalCard]
    exact Finset.card_pos.mpr <| WordType.typeClass_nonempty _
      (by simpa [cw112MarginalType] using cw112MarginalType_mem_types hLG .X)
  apply Nat.eq_of_mul_eq_mul_left (n := marginalCard) hmarginalPos
  calc
    marginalCard * cw112XYFiberSize L G = (cw112TypeWords L G).card := by
      simpa [marginalCard] using cw112XYMarginalCard_mul_fiberSize hLG
    _ = Nat.multinomial Finset.univ (cw112NaturalType L G) :=
      card_cw112TypeWords_eq_multinomial hLG
    _ = Nat.multinomial Finset.univ (cw112SideMarginalType L G) *
        Nat.choose (L + G) L ^ 2 :=
      (cw112SideMultinomial_mul_choose_sq_eq_joint L G).symm
    _ = marginalCard * Nat.choose (L + G) L ^ 2 := by rw [hmarginal]

/-- Every X typed word fiber of the selected joint type has the common size. -/
theorem card_cw112XTypedWordMapFiber {L G : ℕ} (hLG : 0 < L + G)
    (target : Fin (cw112TypeDepth L G + 1) → CW112Side)
    (htarget : target ∈ WordType.typeClass (cw112TypeDepth L G + 1)
      (cw112SideMarginalType L G)) :
    (WordType.typedWordMapFiber (fun s : cw112BlockSupport ↦ s.1 .X)
      (cw112NaturalType L G) target).card = cw112XYFiberSize L G := by
  have hdouble := WordType.card_targetType_mul_card_typedWordMapFiber
    (fun s : cw112BlockSupport ↦ s.1 .X) (cw112NaturalType L G) target
    (by
      rw [cw112_mappedType_eq_marginal]
      exact htarget)
  have hsource :
      (WordType.typeClass (cw112TypeDepth L G + 1)
        (cw112NaturalType L G)).card = (cw112TypeWords L G).card :=
    (card_positiveTypeClass (I := cw112BlockSupport) (cw112TypeDepth L G)
      (cw112NaturalType L G)).symm
  rw [show WordType.mappedType (fun s : cw112BlockSupport ↦ s.1 .X)
      (cw112NaturalType L G) = cw112SideMarginalType L G by
        simpa [cw112MarginalType] using cw112_mappedType_eq_marginal L G .X,
    hsource] at hdouble
  unfold cw112XYFiberSize
  exact Nat.eq_div_of_mul_eq_left
    (Finset.card_ne_zero.mpr
      (WordType.typeClass_nonempty _
        (by simpa [cw112MarginalType] using cw112MarginalType_mem_types hLG .X)))
    (by simpa [Nat.mul_comm] using hdouble)

/-- Every Y typed word fiber has the same size as an X typed word fiber. -/
theorem card_cw112YTypedWordMapFiber {L G : ℕ} (hLG : 0 < L + G)
    (target : Fin (cw112TypeDepth L G + 1) → CW112Side)
    (htarget : target ∈ WordType.typeClass (cw112TypeDepth L G + 1)
      (cw112SideMarginalType L G)) :
    (WordType.typedWordMapFiber (fun s : cw112BlockSupport ↦ s.1 .Y)
      (cw112NaturalType L G) target).card = cw112XYFiberSize L G := by
  have hdouble := WordType.card_targetType_mul_card_typedWordMapFiber
    (fun s : cw112BlockSupport ↦ s.1 .Y) (cw112NaturalType L G) target
    (by
      rw [cw112_mappedType_eq_marginal]
      exact htarget)
  have hsource :
      (WordType.typeClass (cw112TypeDepth L G + 1)
        (cw112NaturalType L G)).card = (cw112TypeWords L G).card :=
    (card_positiveTypeClass (I := cw112BlockSupport) (cw112TypeDepth L G)
      (cw112NaturalType L G)).symm
  rw [show WordType.mappedType (fun s : cw112BlockSupport ↦ s.1 .Y)
      (cw112NaturalType L G) = cw112SideMarginalType L G by
        simpa [cw112MarginalType] using cw112_mappedType_eq_marginal L G .Y,
    hsource] at hdouble
  unfold cw112XYFiberSize
  exact Nat.eq_div_of_mul_eq_left
    (Finset.card_ne_zero.mpr
      (WordType.typeClass_nonempty _
        (by simpa [cw112MarginalType] using cw112MarginalType_mem_types hLG .Y)))
    (by simpa [Nat.mul_comm] using hdouble)

/-- Every Z word of marginal type `(L,L,2G)` has exactly `choose (2G) G` compatible joint
words.  These are precisely the terms intentionally kept together as one C-tensor group. -/
theorem card_cw112ZTypedWordMapFiber {L G : ℕ} (hLG : 0 < L + G)
    (target : Fin (cw112TypeDepth L G + 1) → CW112ZBlock)
    (htarget : target ∈ WordType.typeClass (cw112TypeDepth L G + 1)
      (cw112ZMarginalType L G)) :
    (WordType.typedWordMapFiber (fun s : cw112BlockSupport ↦ s.1 .Z)
      (cw112NaturalType L G) target).card = Nat.choose (2 * G) G := by
  have hdouble := WordType.card_targetType_mul_card_typedWordMapFiber
    (fun s : cw112BlockSupport ↦ s.1 .Z) (cw112NaturalType L G) target
    (by
      rw [cw112_mappedType_eq_marginal]
      exact htarget)
  have hsource :
      (WordType.typeClass (cw112TypeDepth L G + 1)
        (cw112NaturalType L G)).card = (cw112TypeWords L G).card :=
    (card_positiveTypeClass (I := cw112BlockSupport) (cw112TypeDepth L G)
      (cw112NaturalType L G)).symm
  rw [show WordType.mappedType (fun s : cw112BlockSupport ↦ s.1 .Z)
      (cw112NaturalType L G) = cw112ZMarginalType L G by
        simpa [cw112MarginalType] using cw112_mappedType_eq_marginal L G .Z,
    hsource] at hdouble
  let marginalCard := (WordType.typeClass (cw112TypeDepth L G + 1)
    (cw112ZMarginalType L G)).card
  have hmarginal : marginalCard =
      Nat.multinomial Finset.univ (cw112ZMarginalType L G) := by
    simpa [marginalCard, cw112MarginalType] using
      card_cw112MarginalTypeClass_eq_multinomial hLG .Z
  have hmarginalPos : 0 < marginalCard := by
    dsimp [marginalCard]
    exact Finset.card_pos.mpr <| WordType.typeClass_nonempty _
      (by simpa [cw112MarginalType] using cw112MarginalType_mem_types hLG .Z)
  apply Nat.eq_of_mul_eq_mul_left (n := marginalCard) hmarginalPos
  calc
    marginalCard *
        (WordType.typedWordMapFiber (fun s : cw112BlockSupport ↦ s.1 .Z)
          (cw112NaturalType L G) target).card = (cw112TypeWords L G).card := by
      simpa [marginalCard] using hdouble
    _ = Nat.multinomial Finset.univ (cw112NaturalType L G) :=
      card_cw112TypeWords_eq_multinomial hLG
    _ = Nat.multinomial Finset.univ (cw112ZMarginalType L G) *
        Nat.choose (2 * G) G := (cw112ZMultinomial_mul_choose_eq_joint L G).symm
    _ = marginalCard * Nat.choose (2 * G) G := by rw [hmarginal]

/-- X-leg hashing fibers are bounded by the exact typed source-to-marginal ratio. -/
theorem card_cw112Target_xLegFiber_le
    {R : Type*} [Field R] [NeZero (2 : R)] {L G : ℕ} (hLG : 0 < L + G)
    {triple : ProgressionHash.LegalTriple R (Fin (cw112TypeDepth L G + 1)) 2}
    (htriple : triple ∈ cw112TypeTargets (R := R) L G) :
    (ProgressionHash.LegalTriple.legFiber
      (cw112TypeTargets (R := R) L G) triple .X).card ≤
        cw112XYFiberSize L G := by
  classical
  change triple ∈ (cw112TypeWords L G).image
    ((cw112PartitionHashEncoding (R := R)).legalTriple (cw112TypeDepth L G)) at htriple
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp htriple
  have hlegal : (cw112PartitionHashEncoding (R := R)).legalTriple
      (cw112TypeDepth L G) q ∈ cw112TypeTargets (R := R) L G := by
    unfold cw112TypeTargets PartitionHashEncoding.legalTargets
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  apply ((cw112PartitionHashEncoding (R := R)).card_legFiber_legalTargets_le_card_typedWordMapFiber
    (cw112TypeDepth L G) (cw112TypeWords L G) (cw112NaturalType L G)
    (fun word hword ↦ mem_positiveTypeClass.mp hword) hlegal .X).trans_eq
  apply card_cw112XTypedWordMapFiber hLG
  simpa [cw112MarginalType] using
    cw112LegWord_mem_marginalTypeClass L G q hq .X

/-- Y-leg hashing fibers obey the same exact bound as X-leg fibers. -/
theorem card_cw112Target_yLegFiber_le
    {R : Type*} [Field R] [NeZero (2 : R)] {L G : ℕ} (hLG : 0 < L + G)
    {triple : ProgressionHash.LegalTriple R (Fin (cw112TypeDepth L G + 1)) 2}
    (htriple : triple ∈ cw112TypeTargets (R := R) L G) :
    (ProgressionHash.LegalTriple.legFiber
      (cw112TypeTargets (R := R) L G) triple .Y).card ≤
        cw112XYFiberSize L G := by
  classical
  change triple ∈ (cw112TypeWords L G).image
    ((cw112PartitionHashEncoding (R := R)).legalTriple (cw112TypeDepth L G)) at htriple
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp htriple
  have hlegal : (cw112PartitionHashEncoding (R := R)).legalTriple
      (cw112TypeDepth L G) q ∈ cw112TypeTargets (R := R) L G := by
    unfold cw112TypeTargets PartitionHashEncoding.legalTargets
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  apply ((cw112PartitionHashEncoding (R := R)).card_legFiber_legalTargets_le_card_typedWordMapFiber
    (cw112TypeDepth L G) (cw112TypeWords L G) (cw112NaturalType L G)
    (fun word hword ↦ mem_positiveTypeClass.mp hword) hlegal .Y).trans_eq
  apply card_cw112YTypedWordMapFiber hLG
  simpa [cw112MarginalType] using
    cw112LegWord_mem_marginalTypeClass L G q hq .Y

/-- The number of XY collision proxies for any selected target is at most twice the common
typed-fiber size. -/
theorem card_cw112Target_xyCompetitorYIndices_le
    {R : Type*} [Field R] [NeZero (2 : R)] {L G : ℕ} (hLG : 0 < L + G)
    {triple : ProgressionHash.LegalTriple R (Fin (cw112TypeDepth L G + 1)) 2}
    (htriple : triple ∈ cw112TypeTargets (R := R) L G) :
    (ProgressionHash.LegalTriple.xyCompetitorYIndices
      (cw112TypeTargets (R := R) L G) triple).card ≤
        2 * cw112XYFiberSize L G := by
  exact ProgressionHash.LegalTriple.card_xyCompetitorYIndices_le_two_mul
    _ _ _ (card_cw112Target_xLegFiber_le hLG htriple)
      (card_cw112Target_yLegFiber_le hLG htriple)

/-- A field of size at least eight times the typed-fiber degree satisfies the collision budget
required by two-leg affine hashing. -/
theorem cw112_xyCompetitorQuarter_of_fieldCard
    {R : Type*} [Field R] [Fintype R] [NeZero (2 : R)]
    {L G : ℕ} (hLG : 0 < L + G)
    (hfield : 8 * cw112XYFiberSize L G ≤ Fintype.card R) :
    ∀ triple ∈ cw112TypeTargets (R := R) L G,
      4 * (ProgressionHash.LegalTriple.xyCompetitorYIndices
        (cw112TypeTargets (R := R) L G) triple).card ≤ Fintype.card R := by
  intro triple htriple
  calc
    4 * (ProgressionHash.LegalTriple.xyCompetitorYIndices
      (cw112TypeTargets (R := R) L G) triple).card ≤
        4 * (2 * cw112XYFiberSize L G) :=
      Nat.mul_le_mul_left 4 (card_cw112Target_xyCompetitorYIndices_le hLG htriple)
    _ = 8 * cw112XYFiberSize L G := by ring
    _ ≤ Fintype.card R := hfield

/-- Finite `112` two-leg extraction.  Some affine seed retains many selected words, globally
injective on X and Y, while leaving shared Z words untouched for the later C-tensor grouping.
The displayed inequality keeps all field-size and progression-free-set losses exact. -/
theorem exists_cw112_many_xyIsolatedTargets
    {R : Type*} [Field R] [Fintype R] [NeZero (2 : R)]
    {L G : ℕ} (hLG : 0 < L + G)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hfield : 8 * cw112XYFiberSize L G ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1)),
      3 * (cw112TypeTargets (R := R) L G).card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (ProgressionHash.LegalTriple.xyIsolatedTargets
              (cw112TypeTargets (R := R) L G) B seed).card ∧
        ProgressionHash.LegalTriple.xyIsolatedTargets
            (cw112TypeTargets (R := R) L G) B seed ⊆
          ProgressionHash.LegalTriple.filteredTargets
            (cw112TypeTargets (R := R) L G) B seed ∧
        Set.InjOn
          (fun triple : ProgressionHash.LegalTriple R
              (Fin (cw112TypeDepth L G + 1)) 2 ↦ triple.xIndex)
          (ProgressionHash.LegalTriple.xyIsolatedTargets
            (cw112TypeTargets (R := R) L G) B seed : Set _) ∧
        Set.InjOn
          (fun triple : ProgressionHash.LegalTriple R
              (Fin (cw112TypeDepth L G + 1)) 2 ↦ triple.yIndex)
          (ProgressionHash.LegalTriple.xyIsolatedTargets
            (cw112TypeTargets (R := R) L G) B seed : Set _) := by
  exact ProgressionHash.LegalTriple.exists_seed_many_xyIsolatedTargets
    (cw112TypeTargets (R := R) L G) B hB
      (cw112_xyCompetitorQuarter_of_fieldCard hLG hfield)

end AlgebraicComplexity.Examples
