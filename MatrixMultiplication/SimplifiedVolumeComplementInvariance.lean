import MatrixMultiplication.SimplifiedVolumeReconstruction

/-!
# Complement invariance of the volume-only zero-leaf formula

The volume recurrence deliberately consumes one primary complete-split law.  It does not need a
serialized table describing the complementary law: digitwise complementation merely relabels the
ternary words, preserves Shannon entropy, and preserves the number of `1` digits.  This module
makes that independence explicit without putting any complement table in the generated-certificate
boundary.
-/

open scoped BigOperators

namespace MatrixMultiplication.SimplifiedVolumeComplementInvariance

open MatrixMultiplication.SimplifiedVolumeReconstruction

noncomputable section

/-- The zero-leaf volume is invariant under a finite relabelling that transports both the
probability numerator and the matrix-size statistic. -/
theorem zeroLeafValue_reindex
    {I J : Type*} [Fintype I] [Fintype J]
    (bits : ℕ) (e : I ≃ J)
    (numeratorI : I → ℕ) (numeratorJ : J → ℕ)
    (onesI : I → ℕ) (onesJ : J → ℕ)
    (hnumerator : ∀ i, numeratorI i = numeratorJ (e i))
    (hones : ∀ i, onesI i = onesJ (e i)) :
    zeroLeafValue bits numeratorI onesI =
      zeroLeafValue bits numeratorJ onesJ := by
  unfold zeroLeafValue
  have hentropy :
      (∑ i, MatrixMultiplication.DyadicEntropy.entropyTerm bits (numeratorI i)) =
        ∑ j, MatrixMultiplication.DyadicEntropy.entropyTerm bits (numeratorJ j) := by
    exact Fintype.sum_equiv e _ _ (fun i ↦ by rw [hnumerator i])
  have hweighted :
      (∑ i, numeratorI i * onesI i) = ∑ j, numeratorJ j * onesJ j := by
    exact Fintype.sum_equiv e _ _ (fun i ↦ by rw [hnumerator i, hones i])
  rw [hentropy, hweighted]

/-- The outer occurrence mass does not affect reindexing invariance. -/
theorem weightedZeroLeafValue_reindex
    {I J : Type*} [Fintype I] [Fintype J]
    (outerBits localBits outerNumerator : ℕ) (e : I ≃ J)
    (numeratorI : I → ℕ) (numeratorJ : J → ℕ)
    (onesI : I → ℕ) (onesJ : J → ℕ)
    (hnumerator : ∀ i, numeratorI i = numeratorJ (e i))
    (hones : ∀ i, onesI i = onesJ (e i)) :
    weightedZeroLeafValue outerBits localBits outerNumerator numeratorI onesI =
      weightedZeroLeafValue outerBits localBits outerNumerator numeratorJ onesJ := by
  unfold weightedZeroLeafValue
  rw [zeroLeafValue_reindex localBits e numeratorI numeratorJ onesI onesJ
    hnumerator hones]

/-- Digitwise complementation on the alphabet `{0,1,2}`. -/
def ternaryDigitComplement : Fin 3 ≃ Fin 3 where
  toFun digit := ⟨2 - digit.val, by omega⟩
  invFun digit := ⟨2 - digit.val, by omega⟩
  left_inv digit := by fin_cases digit <;> rfl
  right_inv digit := by fin_cases digit <;> rfl

/-- Pointwise digitwise complementation of a ternary word. -/
def ternaryWordComplement (length : ℕ) :
    (Fin length → Fin 3) ≃ (Fin length → Fin 3) where
  toFun word position := ternaryDigitComplement (word position)
  invFun word position := ternaryDigitComplement.symm (word position)
  left_inv word := by
    funext position
    exact ternaryDigitComplement.left_inv (word position)
  right_inv word := by
    funext position
    exact ternaryDigitComplement.right_inv (word position)

/-- The matrix-size statistic used by a zero leaf: the number of `1` digits. -/
def ternaryWordOnes {length : ℕ} (word : Fin length → Fin 3) : ℕ :=
  ∑ position, if word position = 1 then 1 else 0

theorem ternaryDigitComplement_eq_one_iff (digit : Fin 3) :
    ternaryDigitComplement digit = 1 ↔ digit = 1 := by
  fin_cases digit <;> decide

theorem ternaryWordOnes_complement {length : ℕ} (word : Fin length → Fin 3) :
    ternaryWordOnes (ternaryWordComplement length word) = ternaryWordOnes word := by
  apply Finset.sum_congr rfl
  intro position _
  change (if ternaryDigitComplement (word position) = 1 then 1 else 0) =
    if word position = 1 then 1 else 0
  simp only [ternaryDigitComplement_eq_one_iff]

/-- Sum of the ternary digits of a word.  Complete-split laws are supported on fibers of this
map. -/
def ternaryWordWeight {length : ℕ} (word : Fin length → Fin 3) : ℕ :=
  ∑ position, (word position).val

theorem ternaryDigitComplement_val_add (digit : Fin 3) :
    (ternaryDigitComplement digit).val + digit.val = 2 := by
  fin_cases digit <;> decide

theorem ternaryWordWeight_complement_add {length : ℕ} (word : Fin length → Fin 3) :
    ternaryWordWeight (ternaryWordComplement length word) + ternaryWordWeight word =
      2 * length := by
  unfold ternaryWordWeight
  rw [← Finset.sum_add_distrib]
  simp only [ternaryWordComplement]
  calc
    ∑ position, ((ternaryDigitComplement (word position)).val + (word position).val) =
        ∑ _position : Fin length, 2 := by
      apply Finset.sum_congr rfl
      intro position _
      exact ternaryDigitComplement_val_add (word position)
    _ = 2 * length := by simp [Nat.mul_comm]

theorem ternaryWordWeight_complement {length : ℕ} (word : Fin length → Fin 3) :
    ternaryWordWeight (ternaryWordComplement length word) =
      2 * length - ternaryWordWeight word := by
  have h := ternaryWordWeight_complement_add word
  omega

/-- Ternary words of a prescribed digit sum, the natural support type of one complete-split
law. -/
def TernaryWordsOfTotal (length total : ℕ) :=
  { word : Fin length → Fin 3 // ternaryWordWeight word = total }

instance (length total : ℕ) : Fintype (TernaryWordsOfTotal length total) :=
  Subtype.fintype _

/-- True digitwise complement identifies the support of total `t` with the support of total
`2 * length - t`. -/
def ternarySupportComplement (length total : ℕ) (htotal : total ≤ 2 * length) :
    TernaryWordsOfTotal length total ≃
      TernaryWordsOfTotal length (2 * length - total) where
  toFun word := ⟨ternaryWordComplement length word.val, by
    rw [ternaryWordWeight_complement, word.property]⟩
  invFun word := ⟨ternaryWordComplement length word.val, by
    rw [ternaryWordWeight_complement, word.property]
    omega⟩
  left_inv word := by
    apply Subtype.ext
    exact (ternaryWordComplement length).left_inv word.val
  right_inv word := by
    apply Subtype.ext
    exact (ternaryWordComplement length).right_inv word.val

def ternarySupportOnes {length total : ℕ}
    (word : TernaryWordsOfTotal length total) : ℕ :=
  ternaryWordOnes word.val

theorem ternarySupportOnes_complement
    (length total : ℕ) (htotal : total ≤ 2 * length)
    (word : TernaryWordsOfTotal length total) :
    ternarySupportOnes (ternarySupportComplement length total htotal word) =
      ternarySupportOnes word := by
  change ternaryWordOnes (ternaryWordComplement length word.val) = ternaryWordOnes word.val
  exact ternaryWordOnes_complement word.val

/-- The zero-leaf volume on a fixed-total support is invariant under the mathematically correct
complement bijection to the complementary total. -/
theorem zeroLeafValue_ternarySupportComplement
    (bits length total : ℕ) (htotal : total ≤ 2 * length)
    (numerator : TernaryWordsOfTotal length (2 * length - total) → ℕ) :
    zeroLeafValue bits
        (fun word ↦ numerator (ternarySupportComplement length total htotal word))
        ternarySupportOnes =
      zeroLeafValue bits numerator ternarySupportOnes := by
  apply zeroLeafValue_reindex bits (ternarySupportComplement length total htotal)
  · intro word
    rfl
  · intro word
    exact (ternarySupportOnes_complement length total htotal word).symm

/-- Weighted fixed-total zero-leaf contributions are complement-invariant as well. -/
theorem weightedZeroLeafValue_ternarySupportComplement
    (outerBits localBits outerNumerator length total : ℕ)
    (htotal : total ≤ 2 * length)
    (numerator : TernaryWordsOfTotal length (2 * length - total) → ℕ) :
    weightedZeroLeafValue outerBits localBits outerNumerator
        (fun word ↦ numerator (ternarySupportComplement length total htotal word))
        ternarySupportOnes =
      weightedZeroLeafValue outerBits localBits outerNumerator numerator ternarySupportOnes := by
  unfold weightedZeroLeafValue
  rw [zeroLeafValue_ternarySupportComplement]

/-- Complementing every ternary word in a zero-law row leaves its exact volume contribution
unchanged.  Consequently the volume-only certificate does not require archived `sup*_comp`
tables. -/
theorem zeroLeafValue_ternaryComplement
    (bits length : ℕ) (numerator : (Fin length → Fin 3) → ℕ) :
    zeroLeafValue bits
        (fun word ↦ numerator (ternaryWordComplement length word)) ternaryWordOnes =
      zeroLeafValue bits numerator ternaryWordOnes := by
  apply zeroLeafValue_reindex bits (ternaryWordComplement length)
  · intro word
    rfl
  · intro word
    exact (ternaryWordOnes_complement word).symm

/-- The actual weighted zero-leaf contribution is likewise invariant under digitwise
complementation. -/
theorem weightedZeroLeafValue_ternaryComplement
    (outerBits localBits outerNumerator length : ℕ)
    (numerator : (Fin length → Fin 3) → ℕ) :
    weightedZeroLeafValue outerBits localBits outerNumerator
        (fun word ↦ numerator (ternaryWordComplement length word)) ternaryWordOnes =
      weightedZeroLeafValue outerBits localBits outerNumerator numerator ternaryWordOnes := by
  unfold weightedZeroLeafValue
  rw [zeroLeafValue_ternaryComplement]

end

end MatrixMultiplication.SimplifiedVolumeComplementInvariance
