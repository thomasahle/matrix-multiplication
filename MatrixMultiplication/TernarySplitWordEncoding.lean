/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorWordCore
import MatrixMultiplication.BetaFourLocalGeometry
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity

/-!
# Ternary serialization of complete-split words

The compact level-four evaluator stores a complete-split word by its big-endian base-three code
inside the increasing list of codes having the requested digit sum.  This module proves the small
structural facts behind the depth-two serialization and support lookup.

Digit recovery is proved from four quotient/remainder identities, while support and lookup
consequences use ordinary arithmetic and the injectivity of `List.idxOf`.  Keeping this work
separate prevents certificate clients from repeating large closed reductions merely to move
between words and evaluator slots.  The module intentionally imports only the definition-level
word and local-geometry leaves; the full recurrence and validity checker depend on this module,
not conversely.
-/

namespace MatrixMultiplication.TernarySplitWordEncoding

open scoped BigOperators

open AlgebraicComplexity
open MatrixMultiplication.BetaFourLocalGeometry

/-- Big-endian base-three code of a four-digit complete-split word. -/
def splitWordDepthTwoCode (word : SplitWord 2) : ℕ :=
  (word ⟨0, by decide⟩ : ℕ) * 27 +
    (word ⟨1, by decide⟩ : ℕ) * 9 +
      (word ⟨2, by decide⟩ : ℕ) * 3 +
        (word ⟨3, by decide⟩ : ℕ)

/-- Big-endian base-three code of an eight-digit complete-split word.

This is the canonical name used by the level-four evaluator.  Its relationship with the two
four-digit halves is proved downstream, where the recursive split equivalence is available. -/
def splitWordDepthThreeCode (word : SplitWord 3) : ℕ :=
  (word ⟨0, by decide⟩ : ℕ) * 2187 +
    (word ⟨1, by decide⟩ : ℕ) * 729 +
      (word ⟨2, by decide⟩ : ℕ) * 243 +
        (word ⟨3, by decide⟩ : ℕ) * 81 +
          (word ⟨4, by decide⟩ : ℕ) * 27 +
            (word ⟨5, by decide⟩ : ℕ) * 9 +
              (word ⟨6, by decide⟩ : ℕ) * 3 +
                (word ⟨7, by decide⟩ : ℕ)

/-- Every depth-two word code lies in the four-digit base-three range.

Proof sketch: each digit is smaller than three, so the weighted four-digit sum is smaller than
`3^4 = 81`. -/
theorem splitWordDepthTwoCode_lt (word : SplitWord 2) :
    splitWordDepthTwoCode word < 3 ^ childWordLength := by
  have h0 := (word ⟨0, by decide⟩).isLt
  have h1 := (word ⟨1, by decide⟩).isLt
  have h2 := (word ⟨2, by decide⟩).isLt
  have h3 := (word ⟨3, by decide⟩).isLt
  norm_num [splitWordDepthTwoCode, childWordLength]
  omega

/-- Reading one digit of a serialized depth-two word recovers that split digit.

Proof sketch: write the code as `27a + 9b + 3c + d`.  At each of the four positions, the
lower-order suffix is smaller than the relevant divisor; `Nat.mul_add_div` therefore removes it,
and reduction modulo three removes all higher-order digits. -/
theorem ternaryDigit_splitWordDepthTwoCode (word : SplitWord 2)
    (position : Fin childWordLength) :
    ternaryDigit childWordLength (splitWordDepthTwoCode word) position =
      word position := by
  let a : ℕ := word ⟨0, by decide⟩
  let b : ℕ := word ⟨1, by decide⟩
  let c : ℕ := word ⟨2, by decide⟩
  let d : ℕ := word ⟨3, by decide⟩
  have ha : a < 3 := (word ⟨0, by decide⟩).isLt
  have hb : b < 3 := (word ⟨1, by decide⟩).isLt
  have hc : c < 3 := (word ⟨2, by decide⟩).isLt
  have hd : d < 3 := (word ⟨3, by decide⟩).isLt
  have h27 : (a * 27 + b * 9 + c * 3 + d) / 27 % 3 = a := by
    have hsuffix : b * 9 + c * 3 + d < 27 := by omega
    rw [show a * 27 + b * 9 + c * 3 + d = 27 * a + (b * 9 + c * 3 + d) by omega,
      Nat.mul_add_div (by decide), Nat.div_eq_of_lt hsuffix, Nat.add_zero,
      Nat.mod_eq_of_lt ha]
  have h9 : (a * 27 + b * 9 + c * 3 + d) / 9 % 3 = b := by
    have hsuffix : c * 3 + d < 9 := by omega
    rw [show a * 27 + b * 9 + c * 3 + d = 9 * (a * 3 + b) + (c * 3 + d) by omega,
      Nat.mul_add_div (by decide), Nat.div_eq_of_lt hsuffix, Nat.add_zero,
      show a * 3 + b = b + 3 * a by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hb]
  have h3 : (a * 27 + b * 9 + c * 3 + d) / 3 % 3 = c := by
    rw [show a * 27 + b * 9 + c * 3 + d = 3 * (a * 9 + b * 3 + c) + d by omega,
      Nat.mul_add_div (by decide), Nat.div_eq_of_lt hd, Nat.add_zero,
      show a * 9 + b * 3 + c = c + 3 * (a * 3 + b) by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  have h1 : (a * 27 + b * 9 + c * 3 + d) % 3 = d := by
    rw [show a * 27 + b * 9 + c * 3 + d = d + 3 * (a * 9 + b * 3 + c) by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
  fin_cases position
  · simpa [ternaryDigit, childWordLength, splitWordDepthTwoCode, a, b, c, d] using h27
  · simpa [ternaryDigit, childWordLength, splitWordDepthTwoCode, a, b, c, d] using h9
  · simpa [ternaryDigit, childWordLength, splitWordDepthTwoCode, a, b, c, d] using h3
  · simpa [ternaryDigit, childWordLength, splitWordDepthTwoCode, a, b, c, d] using h1

/-- The four-digit ternary serialization is injective.

Proof sketch: equal codes have equal decoded digits at every position, and digit recovery
identifies those decoded digits with the original split words. -/
theorem splitWordDepthTwoCode_injective : Function.Injective splitWordDepthTwoCode := by
  intro left right hcode
  funext position
  apply Fin.ext
  have hdigit := congrArg (fun code ↦ ternaryDigit childWordLength code position) hcode
  exact (ternaryDigit_splitWordDepthTwoCode left position).symm.trans
    (hdigit.trans (ternaryDigit_splitWordDepthTwoCode right position))

/-- The evaluator's digit-sum function reads the intrinsic weight of a depth-two word.

Proof sketch: expand the four-entry evaluator sum, apply the preceding digit-recovery theorem at
each position, and identify the result with the finite sum defining `splitWordWeight`. -/
theorem ternaryCodeWeight_splitWordDepthTwoCode (word : SplitWord 2) :
    ternaryCodeWeight childWordLength (splitWordDepthTwoCode word) =
      splitWordWeight word := by
  have h0 : ternaryDigit 4 (splitWordDepthTwoCode word) 0 =
      (word ⟨0, by decide⟩ : ℕ) := by
    simpa [childWordLength] using
      ternaryDigit_splitWordDepthTwoCode word ⟨0, by decide⟩
  have h1 : ternaryDigit 4 (splitWordDepthTwoCode word) 1 =
      (word ⟨1, by decide⟩ : ℕ) := by
    simpa [childWordLength] using
      ternaryDigit_splitWordDepthTwoCode word ⟨1, by decide⟩
  have h2 : ternaryDigit 4 (splitWordDepthTwoCode word) 2 =
      (word ⟨2, by decide⟩ : ℕ) := by
    simpa [childWordLength] using
      ternaryDigit_splitWordDepthTwoCode word ⟨2, by decide⟩
  have h3 : ternaryDigit 4 (splitWordDepthTwoCode word) 3 =
      (word ⟨3, by decide⟩ : ℕ) := by
    simpa [childWordLength] using
      ternaryDigit_splitWordDepthTwoCode word ⟨3, by decide⟩
  norm_num [ternaryCodeWeight, childWordLength, List.range_succ]
  rw [h0, h1, h2, h3]
  simp [splitWordWeight, Fin.sum_univ_succ]

/-- Every four-digit ternary code has digit sum at most eight.

Proof sketch: each of the four residues modulo three is at most two, independently of whether the
input has higher base-three digits.  Expanding the fixed digit sum therefore gives a total at most
`4 * 2 = 8`. -/
theorem ternaryCodeWeight_depthTwo_le (code : ℕ) :
    ternaryCodeWeight childWordLength code ≤ 8 := by
  have h0 : code / 27 % 3 < 3 := Nat.mod_lt _ (by decide)
  have h1 : code / 9 % 3 < 3 := Nat.mod_lt _ (by decide)
  have h2 : code / 3 % 3 < 3 := Nat.mod_lt _ (by decide)
  have h3 : code % 3 < 3 := Nat.mod_lt _ (by decide)
  norm_num [ternaryCodeWeight, ternaryDigit, childWordLength, List.range_succ]
  omega

/-- Exact coefficient table for four ternary digits, padded by zero outside weights `0,…,8`. -/
private def depthTwoSupportLengthTable (total : ℕ) : ℕ :=
  if total = 0 then 1 else
  if total = 1 then 4 else
  if total = 2 then 10 else
  if total = 3 then 16 else
  if total = 4 then 19 else
  if total = 5 then 16 else
  if total = 6 then 10 else
  if total = 7 then 4 else
  if total = 8 then 1 else 0

/-- The fixed-weight support length is the corresponding entry of the small coefficient table.

Proof sketch: for weights `0,…,8`, normalize the 81 four-digit codes once.  Above weight eight the
support is empty by `ternaryCodeWeight_depthTwo_le`, so the table's zero padding is exact. -/
private theorem ternarySupportCodes_depthTwo_length_eq_table (total : ℕ) :
    (ternarySupportCodes childWordLength total).length =
      depthTwoSupportLengthTable total := by
  by_cases htotal : total ≤ 8
  · interval_cases total <;>
      norm_num [ternarySupportCodes, ternaryCodeWeight, ternaryDigit, childWordLength,
        depthTwoSupportLengthTable, List.range_succ]
  · have hempty : ternarySupportCodes childWordLength total = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro code hcode
      have hcode' : code < 3 ^ childWordLength ∧
          ternaryCodeWeight childWordLength code = total := by
        simpa only [ternarySupportCodes, List.mem_filter, List.mem_range,
          decide_eq_true_eq] using hcode
      have hweight := ternaryCodeWeight_depthTwo_le code
      omega
    rw [hempty]
    have h0 : total ≠ 0 := by omega
    have h1 : total ≠ 1 := by omega
    have h2 : total ≠ 2 := by omega
    have h3 : total ≠ 3 := by omega
    have h4 : total ≠ 4 := by omega
    have h5 : total ≠ 5 := by omega
    have h6 : total ≠ 6 := by omega
    have h7 : total ≠ 7 := by omega
    have h8 : total ≠ 8 := by omega
    simp [depthTwoSupportLengthTable, h0, h1, h2, h3, h4, h5, h6, h7, h8]

/-- Digitwise split-word complementation is subtraction from the largest four-digit ternary code.

Proof sketch: `Fin.rev` sends each digit `a` to `2-a`; expanding the four positional weights then
gives `80 - (27a + 9b + 3c + d)`. -/
theorem splitWordDepthTwoCode_complement (word : SplitWord 2) :
    splitWordDepthTwoCode (complementSplitWord word) =
      3 ^ childWordLength - 1 - splitWordDepthTwoCode word := by
  have h0 := (word ⟨0, by decide⟩).isLt
  have h1 := (word ⟨1, by decide⟩).isLt
  have h2 := (word ⟨2, by decide⟩).isLt
  have h3 := (word ⟨3, by decide⟩).isLt
  simp only [splitWordDepthTwoCode, complementSplitWord_apply, Fin.val_rev]
  norm_num [childWordLength]
  omega

/-- A depth-two word code occurs in the fixed-weight evaluator support row.

Proof sketch: membership in `ternarySupportCodes` is exactly the conjunction of the range bound
and the digit-sum equation proved above. -/
theorem splitWordDepthTwoCode_mem_support (word : SplitWord 2) :
    splitWordDepthTwoCode word ∈
      ternarySupportCodes childWordLength (splitWordWeight word) := by
  simp only [ternarySupportCodes, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨splitWordDepthTwoCode_lt word,
    ternaryCodeWeight_splitWordDepthTwoCode word⟩

/-- A serialized depth-two word lies in exactly the support row named by its intrinsic weight.

Proof sketch: support membership is the conjunction of the fixed range bound and equality of the
decoded digit sum with `total`.  The range bound is automatic for a split-word code, and digit
recovery identifies the decoded sum with `splitWordWeight`. -/
theorem splitWordDepthTwoCode_mem_support_iff (word : SplitWord 2) (total : ℕ) :
    splitWordDepthTwoCode word ∈ ternarySupportCodes childWordLength total ↔
      splitWordWeight word = total := by
  simp only [ternarySupportCodes, List.mem_filter, List.mem_range, decide_eq_true_eq,
    ternaryCodeWeight_splitWordDepthTwoCode]
  exact and_iff_right (splitWordDepthTwoCode_lt word)

/-- A depth-two word has digit sum at most eight. -/
theorem splitWordWeight_depthTwo_le (word : SplitWord 2) : splitWordWeight word ≤ 8 := by
  unfold splitWordWeight
  calc
    (∑ i, (word i : ℕ)) ≤ ∑ _i : Fin (2 ^ 2), 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      exact Nat.le_of_lt_succ (word i).isLt
    _ = 8 := by norm_num

/-- Every length-four fixed-weight support row fits the evaluator's nineteen-cell padding.

Proof sketch: a length-four ternary word has total between zero and eight.  Evaluating the nine
fixed support lengths gives `1, 4, 10, 16, 19, 16, 10, 4, 1`, whose maximum is nineteen. -/
theorem ternarySupportCodes_depthTwo_length_le (total : ℕ) (htotal : total ≤ 8) :
    (ternarySupportCodes childWordLength total).length ≤ childSupportWidth := by
  rw [ternarySupportCodes_depthTwo_length_eq_table]
  interval_cases total <;>
    norm_num [depthTwoSupportLengthTable, childSupportWidth]

/-- The support row selected by a depth-two word fits the common child-row padding. -/
theorem ternarySupportCodes_depthTwoWord_length_le (word : SplitWord 2) :
    (ternarySupportCodes childWordLength (splitWordWeight word)).length ≤
      childSupportWidth :=
  ternarySupportCodes_depthTwo_length_le _ (splitWordWeight_depthTwo_le word)

/-- Looking up a genuine support code at its `idxOf` position recovers that code. -/
theorem ternarySupportCodeAt_idxOf {length total code : ℕ}
    (hcode : code ∈ ternarySupportCodes length total) :
    ternarySupportCodeAt length total
        ((ternarySupportCodes length total).idxOf code) = code := by
  unfold ternarySupportCodeAt
  rw [List.getElem?_idxOf hcode]
  rfl

/-- Fixed-weight ternary support enumeration contains no repeated code. -/
theorem ternarySupportCodes_nodup (length total : ℕ) :
    (ternarySupportCodes length total).Nodup := by
  exact List.nodup_range.filter _

/-- An in-range serialized support position reads a code belonging to that support. -/
theorem ternarySupportCodeAt_mem {length total symbol : ℕ}
    (hsymbol : symbol < (ternarySupportCodes length total).length) :
    ternarySupportCodeAt length total symbol ∈ ternarySupportCodes length total := by
  let position : Fin (ternarySupportCodes length total).length := ⟨symbol, hsymbol⟩
  have hget : ternarySupportCodeAt length total symbol =
      (ternarySupportCodes length total).get position := by
    unfold ternarySupportCodeAt
    rw [List.getElem?_eq_getElem hsymbol]
    rfl
  rw [hget]
  exact List.get_mem _ _

/-- Encoding and then locating an in-range support position returns that position. -/
theorem ternarySupport_idxOf_codeAt {length total symbol : ℕ}
    (hsymbol : symbol < (ternarySupportCodes length total).length) :
    (ternarySupportCodes length total).idxOf
        (ternarySupportCodeAt length total symbol) = symbol := by
  let position : Fin (ternarySupportCodes length total).length := ⟨symbol, hsymbol⟩
  have hget : ternarySupportCodeAt length total symbol =
      (ternarySupportCodes length total).get position := by
    unfold ternarySupportCodeAt
    rw [List.getElem?_eq_getElem hsymbol]
    rfl
  rw [hget]
  exact List.get_idxOf (ternarySupportCodes_nodup length total) position

/-- A support member is determined uniquely by its support index. -/
theorem support_idxOf_inj {length total left right : ℕ}
    (hleft : left ∈ ternarySupportCodes length total)
    (hindex : (ternarySupportCodes length total).idxOf left =
      (ternarySupportCodes length total).idxOf right) :
    left = right :=
  (List.idxOf_inj hleft).mp hindex

/-- Dividing a concatenated four-digit pair by `3^4` recovers its left code. -/
theorem concat_div_depthTwo (left right : ℕ)
    (hright : right < 3 ^ childWordLength) :
    (left * 3 ^ childWordLength + right) / 3 ^ childWordLength = left := by
  rw [Nat.mul_comm left (3 ^ childWordLength), Nat.mul_add_div (by positivity),
    Nat.div_eq_of_lt hright,
    Nat.add_zero]

/-- Reducing a concatenated four-digit pair modulo `3^4` recovers its right code. -/
theorem concat_mod_depthTwo (left right : ℕ)
    (hright : right < 3 ^ childWordLength) :
    (left * 3 ^ childWordLength + right) % 3 ^ childWordLength = right := by
  rw [Nat.mul_comm left (3 ^ childWordLength), Nat.add_comm,
    Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hright]

/-- Concatenating two four-digit codes adds their digit sums.

Proof sketch: quotienting the eight-digit code by `3^4` recovers the left half.  For the four
lower digits, the left half contributes a multiple of three after each remaining quotient, so it
vanishes modulo three.  Expanding the two fixed digit sums then gives the result. -/
theorem ternaryCodeWeight_concat_depthTwo (left right : ℕ)
    (hright : right < 3 ^ childWordLength) :
    ternaryCodeWeight parentWordLength
        (left * 3 ^ childWordLength + right) =
      ternaryCodeWeight childWordLength left +
        ternaryCodeWeight childWordLength right := by
  have hdiv : (left * 81 + right) / 81 = left := by
    simpa [childWordLength] using concat_div_depthTwo left right hright
  have hhigh27 : (left * 81 + right) / 2187 = left / 27 := by
    calc
      (left * 81 + right) / 2187 = (left * 81 + right) / (81 * 27) := by norm_num
      _ = (left * 81 + right) / 81 / 27 := by rw [Nat.div_div_eq_div_mul]
      _ = left / 27 := by rw [hdiv]
  have hhigh9 : (left * 81 + right) / 729 = left / 9 := by
    calc
      (left * 81 + right) / 729 = (left * 81 + right) / (81 * 9) := by norm_num
      _ = (left * 81 + right) / 81 / 9 := by rw [Nat.div_div_eq_div_mul]
      _ = left / 9 := by rw [hdiv]
  have hhigh3 : (left * 81 + right) / 243 = left / 3 := by
    calc
      (left * 81 + right) / 243 = (left * 81 + right) / (81 * 3) := by norm_num
      _ = (left * 81 + right) / 81 / 3 := by rw [Nat.div_div_eq_div_mul]
      _ = left / 3 := by rw [hdiv]
  have hlow27 : (left * 81 + right) / 27 = left * 3 + right / 27 := by
    calc
      (left * 81 + right) / 27 = (27 * (left * 3) + right) / 27 := by
        congr 1
        omega
      _ = left * 3 + right / 27 := by rw [Nat.mul_add_div (by decide)]
  have hlow9 : (left * 81 + right) / 9 = left * 9 + right / 9 := by
    calc
      (left * 81 + right) / 9 = (9 * (left * 9) + right) / 9 := by
        congr 1
        omega
      _ = left * 9 + right / 9 := by rw [Nat.mul_add_div (by decide)]
  have hlow3 : (left * 81 + right) / 3 = left * 27 + right / 3 := by
    calc
      (left * 81 + right) / 3 = (3 * (left * 27) + right) / 3 := by
        congr 1
        omega
      _ = left * 27 + right / 3 := by rw [Nat.mul_add_div (by decide)]
  have hlow27mod : (left * 81 + right) / 27 % 3 = right / 27 % 3 := by
    rw [hlow27, show left * 3 = 3 * left by omega, Nat.add_comm,
      Nat.add_mul_mod_self_left]
  have hlow9mod : (left * 81 + right) / 9 % 3 = right / 9 % 3 := by
    rw [hlow9, show left * 9 = 3 * (left * 3) by omega, Nat.add_comm,
      Nat.add_mul_mod_self_left]
  have hlow3mod : (left * 81 + right) / 3 % 3 = right / 3 % 3 := by
    rw [hlow3, show left * 27 = 3 * (left * 9) by omega, Nat.add_comm,
      Nat.add_mul_mod_self_left]
  have hmod : (left * 81 + right) % 3 = right % 3 := by
    calc
      (left * 81 + right) % 3 = (right + 3 * (left * 27)) % 3 := by
        congr 1
        omega
      _ = right % 3 := Nat.add_mul_mod_self_left _ _ _
  norm_num [ternaryCodeWeight, ternaryDigit, parentWordLength, childWordLength,
    List.range_succ, hhigh27, hhigh9, hhigh3, hdiv, hlow27mod, hlow9mod,
    hlow3mod, hmod]
  simp only [Nat.add_assoc]

/-- Splitting an arbitrary eight-digit code into quotient and remainder adds the two half weights.

Proof sketch: quotient/remainder recomposition writes the input as a concatenation of its two
four-digit halves.  The remainder is automatically below `3^4`, so the concatenation theorem
applies without a separate range hypothesis on the original code. -/
theorem ternaryCodeWeight_split_depthTwo (code : ℕ) :
    ternaryCodeWeight parentWordLength code =
      ternaryCodeWeight childWordLength (code / 3 ^ childWordLength) +
        ternaryCodeWeight childWordLength (code % 3 ^ childWordLength) := by
  have hright : code % 3 ^ childWordLength < 3 ^ childWordLength :=
    Nat.mod_lt _ (by positivity)
  calc
    ternaryCodeWeight parentWordLength code =
        ternaryCodeWeight parentWordLength
          (code / 3 ^ childWordLength * 3 ^ childWordLength +
            code % 3 ^ childWordLength) :=
      congrArg (ternaryCodeWeight parentWordLength)
        (Nat.div_add_mod' code (3 ^ childWordLength)).symm
    _ = _ := ternaryCodeWeight_concat_depthTwo _ _ hright

/-- Concatenating two supported depth-two codes produces a supported depth-three code. -/
theorem concat_mem_parent_support {left right leftTotal rightTotal : ℕ}
    (hleft : left ∈ ternarySupportCodes childWordLength leftTotal)
    (hright : right ∈ ternarySupportCodes childWordLength rightTotal) :
    left * 3 ^ childWordLength + right ∈
      ternarySupportCodes parentWordLength (leftTotal + rightTotal) := by
  simp only [ternarySupportCodes, List.mem_filter, List.mem_range, decide_eq_true_eq]
    at hleft hright ⊢
  refine ⟨?_, ?_⟩
  · norm_num [parentWordLength, childWordLength] at hleft hright ⊢
    omega
  · rw [ternaryCodeWeight_concat_depthTwo left right hright.1,
      hleft.2, hright.2]

/-! ## Structural bound for the eight-digit parent support -/

/-- Quotient and remainder by `3^4` decode an eight-digit code into its two four-digit halves. -/
def decodeDepthTwoPair (code : ℕ) : ℕ × ℕ :=
  (code / 3 ^ childWordLength, code % 3 ^ childWordLength)

/-- The quotient/remainder decoder loses no information.

Proof sketch: equality of decoded pairs gives equality of both quotient and remainder.  Recombine
each input with `Nat.div_add_mod'`. -/
theorem decodeDepthTwoPair_injective : Function.Injective decodeDepthTwoPair := by
  intro left right heq
  have hquotient : left / 3 ^ childWordLength = right / 3 ^ childWordLength := by
    simpa only [decodeDepthTwoPair] using congrArg Prod.fst heq
  have hremainder : left % 3 ^ childWordLength = right % 3 ^ childWordLength := by
    simpa only [decodeDepthTwoPair] using congrArg Prod.snd heq
  calc
    left = left / 3 ^ childWordLength * 3 ^ childWordLength +
        left % 3 ^ childWordLength := (Nat.div_add_mod' left _).symm
    _ = right / 3 ^ childWordLength * 3 ^ childWordLength +
        right % 3 ^ childWordLength := by
      rw [hquotient, hremainder]
    _ = right := Nat.div_add_mod' right _

/-- Candidate pairs of four-digit support codes whose two weights can add to `total`.

The union is deliberately allowed to contain harmless extra pairs when `leftTotal > total`; this
keeps the cardinality proof inequality-valued and avoids subtraction side conditions in the
finite cover. -/
def depthTwoSupportPairCover (total : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range 9).biUnion fun leftTotal ↦
    (ternarySupportCodes childWordLength leftTotal).toFinset ×ˢ
      (ternarySupportCodes childWordLength (total - leftTotal)).toFinset

/-- Decoding a supported eight-digit code lands in the two-half support cover.

Proof sketch: the parent range bound makes its quotient and remainder four-digit codes.  Weight
additivity under concatenation identifies their two weights with the parent total.  Choose the
left weight as the union index; it is below nine by `ternaryCodeWeight_depthTwo_le`. -/
theorem decodeDepthTwoPair_mem_cover {total code : ℕ}
    (hcode : code ∈ ternarySupportCodes parentWordLength total) :
    decodeDepthTwoPair code ∈ depthTwoSupportPairCover total := by
  have hparent : code < 3 ^ parentWordLength ∧
      ternaryCodeWeight parentWordLength code = total := by
    simpa only [ternarySupportCodes, List.mem_filter, List.mem_range,
      decide_eq_true_eq] using hcode
  let left := code / 3 ^ childWordLength
  let right := code % 3 ^ childWordLength
  have hright : right < 3 ^ childWordLength := by
    exact Nat.mod_lt _ (by positivity)
  have hleft : left < 3 ^ childWordLength := by
    dsimp only [left]
    apply (Nat.div_lt_iff_lt_mul (by positivity)).2
    norm_num [parentWordLength, childWordLength] at hparent ⊢
    exact hparent.1
  have hweights : ternaryCodeWeight childWordLength left +
      ternaryCodeWeight childWordLength right = total := by
    have hsplit := ternaryCodeWeight_split_depthTwo code
    rw [hparent.2] at hsplit
    simpa only [left, right] using hsplit.symm
  let leftTotal := ternaryCodeWeight childWordLength left
  have hleftTotal : leftTotal < 9 := by
    exact Nat.lt_succ_of_le (ternaryCodeWeight_depthTwo_le left)
  have hrightWeight : ternaryCodeWeight childWordLength right = total - leftTotal := by
    dsimp only [leftTotal]
    omega
  have hleftMem : left ∈ ternarySupportCodes childWordLength leftTotal := by
    simp only [ternarySupportCodes, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨hleft, rfl⟩
  have hrightMem : right ∈
      ternarySupportCodes childWordLength (total - leftTotal) := by
    simp only [ternarySupportCodes, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨hright, hrightWeight⟩
  simp only [decodeDepthTwoPair, depthTwoSupportPairCover, Finset.mem_biUnion,
    Finset.mem_product, List.mem_toFinset]
  exact ⟨leftTotal, Finset.mem_range.mpr hleftTotal, hleftMem, hrightMem⟩

/-- The nine four-digit support convolutions never exceed the central coefficient `1107`.

Proof sketch: the parent total has only the seventeen values `0,…,16`.  In each case Lean reduces
the nine factors to the small length-four supports (at most 81 codes each) and checks the resulting
integer inequality.  No length-eight support list is evaluated. -/
private theorem depthTwoSupportLengthTable_convolution_le (total : ℕ)
    (htotal : total ≤ 16) :
    (∑ leftTotal ∈ Finset.range 9,
      depthTwoSupportLengthTable leftTotal *
        depthTwoSupportLengthTable (total - leftTotal)) ≤ parentSupportWidth := by
  interval_cases total <;>
    norm_num [Finset.sum_range_succ, depthTwoSupportLengthTable, parentSupportWidth]

/-- The nine four-digit support convolutions never exceed the central coefficient `1107`. -/
private theorem depthTwoSupportConvolution_le (total : ℕ) (htotal : total ≤ 16) :
    (∑ leftTotal ∈ Finset.range 9,
      (ternarySupportCodes childWordLength leftTotal).length *
        (ternarySupportCodes childWordLength (total - leftTotal)).length) ≤
      parentSupportWidth := by
  simp_rw [ternarySupportCodes_depthTwo_length_eq_table]
  exact depthTwoSupportLengthTable_convolution_le total htotal

/-- Every fixed-weight eight-digit ternary support fits the evaluator's 1,107-cell parent row.

Proof sketch: map each parent code injectively to its quotient/remainder pair.  The preceding cover
contains every decoded pair.  Bound the cover by the sum of the nine product-cardinalities, turn
cards back into list lengths using nodup, and apply the compact convolution calculation. -/
theorem ternarySupportCodes_depthThree_length_le (total : ℕ) (htotal : total ≤ 16) :
    (ternarySupportCodes parentWordLength total).length ≤ parentSupportWidth := by
  let source := (ternarySupportCodes parentWordLength total).toFinset
  let decoded := source.image decodeDepthTwoPair
  have hsourceCard : source.card =
      (ternarySupportCodes parentWordLength total).length := by
    exact List.toFinset_card_of_nodup
      (ternarySupportCodes_nodup parentWordLength total)
  have hdecodedCard : decoded.card = source.card := by
    exact Finset.card_image_of_injective source decodeDepthTwoPair_injective
  have hsubset : decoded ⊆ depthTwoSupportPairCover total := by
    intro pair hpair
    obtain ⟨code, hcode, rfl⟩ := Finset.mem_image.mp hpair
    exact decodeDepthTwoPair_mem_cover (List.mem_toFinset.mp hcode)
  calc
    (ternarySupportCodes parentWordLength total).length = source.card := hsourceCard.symm
    _ = decoded.card := hdecodedCard.symm
    _ ≤ (depthTwoSupportPairCover total).card := Finset.card_le_card hsubset
    _ ≤ ∑ leftTotal ∈ Finset.range 9,
        ((ternarySupportCodes childWordLength leftTotal).toFinset ×ˢ
          (ternarySupportCodes childWordLength (total - leftTotal)).toFinset).card :=
      by
        unfold depthTwoSupportPairCover
        exact Finset.card_biUnion_le
    _ = ∑ leftTotal ∈ Finset.range 9,
        (ternarySupportCodes childWordLength leftTotal).length *
          (ternarySupportCodes childWordLength (total - leftTotal)).length := by
      apply Finset.sum_congr rfl
      intro leftTotal _
      rw [Finset.card_product,
        List.toFinset_card_of_nodup
          (ternarySupportCodes_nodup childWordLength leftTotal),
        List.toFinset_card_of_nodup
          (ternarySupportCodes_nodup childWordLength (total - leftTotal))]
    _ ≤ parentSupportWidth := depthTwoSupportConvolution_le total htotal

end MatrixMultiplication.TernarySplitWordEncoding
