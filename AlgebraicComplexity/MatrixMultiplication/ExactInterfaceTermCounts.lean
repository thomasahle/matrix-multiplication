/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensor

/-!
# Constructing exact interface terms from integral count rows

Certificate checkers naturally reconstruct one integer complete-split row for each tensor leg.
This small adapter packages those rows as an `ExactInterfaceTermParameters`.  It asks only for
the two properties that the semantic interface actually needs: a common row total and support on
words of the advertised coordinate weight.

The second constructor starts with one count row on an arbitrary finite source alphabet and maps
that row to the three complete-split alphabets.  Source letters of count zero need not satisfy any
weight condition.  A final theorem says that a source word of the prescribed type realizes all
three mapped split profiles, so certificate clients do not have to repeat the pushforward argument.
-/

open scoped BigOperators

namespace AlgebraicComplexity

namespace ExactInterfaceTermParameters

/-- Construct an exact recursive interface term directly from three integral complete-split
count rows.  Structural zeros are allowed. -/
def ofCountRows {depth samples : ℕ}
    (index : LevelConstituentIndex depth)
    (counts : ∀ _c, SplitWord depth → ℕ)
    (htotal : ∀ c, ∑ word, counts c word = samples)
    (hsupported : ∀ c word, counts c word ≠ 0 → splitWordWeight word = index.count c) :
    ExactInterfaceTermParameters depth where
  multiplicity := samples
  index := index
  split c := CompleteSplitProfile.ofCounts (counts c) (htotal c) (hsupported c)

@[simp] theorem ofCountRows_multiplicity {depth samples : ℕ}
    (index : LevelConstituentIndex depth)
    (counts : ∀ _c, SplitWord depth → ℕ)
    (htotal : ∀ c, ∑ word, counts c word = samples)
    (hsupported : ∀ c word, counts c word ≠ 0 → splitWordWeight word = index.count c) :
    (ofCountRows index counts htotal hsupported).multiplicity = samples :=
  rfl

@[simp] theorem ofCountRows_index {depth samples : ℕ}
    (index : LevelConstituentIndex depth)
    (counts : ∀ _c, SplitWord depth → ℕ)
    (htotal : ∀ c, ∑ word, counts c word = samples)
    (hsupported : ∀ c word, counts c word ≠ 0 → splitWordWeight word = index.count c) :
    (ofCountRows index counts htotal hsupported).index = index :=
  rfl

@[simp] theorem ofCountRows_split_counts {depth samples : ℕ}
    (index : LevelConstituentIndex depth)
    (counts : ∀ _c, SplitWord depth → ℕ)
    (htotal : ∀ c, ∑ word, counts c word = samples)
    (hsupported : ∀ c word, counts c word ≠ 0 → splitWordWeight word = index.count c)
    (c word) :
    ((ofCountRows index counts htotal hsupported).split c).counts word = counts c word :=
  rfl

/-- Construct an exact recursive interface term by pushing one finite source-count row through a
possibly different split-word encoding on each leg.

Only source letters carrying positive mass must have the advertised coordinate weight.  The
encodings need not be injective: counts of source letters with the same encoded split word are
added by `WordType.mappedType`.

Proof sketch: push the common source row forward on each leg and invoke `ofCountRows`.  Pushforward
preserves the row total.  If a pushed count is nonzero, at least one source letter in that fiber has
nonzero count; its conditional weight hypothesis supplies the required support equation. -/
noncomputable def ofMappedCountRows {I : Type*} [Fintype I] {depth samples : ℕ}
    (index : LevelConstituentIndex depth)
    (sourceCount : I → ℕ)
    (encode : Tensor.Leg → I → SplitWord depth)
    (htotal : ∑ i, sourceCount i = samples)
    (hsupported : ∀ c i, sourceCount i ≠ 0 →
      splitWordWeight (encode c i) = index.count c) :
    ExactInterfaceTermParameters depth :=
  ofCountRows index (fun c ↦ WordType.mappedType (encode c) sourceCount)
    (fun _c ↦ by
      simpa only [WordType.sum_mappedType] using htotal)
    (fun c word hcount ↦ by
      classical
      change (∑ i ∈ WordType.letterFiber (encode c) word, sourceCount i) ≠ 0 at hcount
      obtain ⟨i, hi, hsource⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcount
      have hencode : encode c i = word := WordType.mem_letterFiber.mp hi
      rw [← hencode]
      exact hsupported c i hsource)

/-- The mapped-row constructor records the advertised common sample multiplicity. -/
@[simp] theorem ofMappedCountRows_multiplicity
    {I : Type*} [Fintype I] {depth samples : ℕ}
    (index : LevelConstituentIndex depth)
    (sourceCount : I → ℕ)
    (encode : Tensor.Leg → I → SplitWord depth)
    (htotal : ∑ i, sourceCount i = samples)
    (hsupported : ∀ c i, sourceCount i ≠ 0 →
      splitWordWeight (encode c i) = index.count c) :
    (ofMappedCountRows index sourceCount encode htotal hsupported).multiplicity = samples :=
  rfl

/-- The mapped-row constructor preserves the supplied constituent index. -/
@[simp] theorem ofMappedCountRows_index
    {I : Type*} [Fintype I] {depth samples : ℕ}
    (index : LevelConstituentIndex depth)
    (sourceCount : I → ℕ)
    (encode : Tensor.Leg → I → SplitWord depth)
    (htotal : ∑ i, sourceCount i = samples)
    (hsupported : ∀ c i, sourceCount i ≠ 0 →
      splitWordWeight (encode c i) = index.count c) :
    (ofMappedCountRows index sourceCount encode htotal hsupported).index = index :=
  rfl

/-- Each stored split count is the pushforward of the common source row along that leg's
encoding. -/
@[simp] theorem ofMappedCountRows_split_counts
    {I : Type*} [Fintype I] {depth samples : ℕ}
    (index : LevelConstituentIndex depth)
    (sourceCount : I → ℕ)
    (encode : Tensor.Leg → I → SplitWord depth)
    (htotal : ∑ i, sourceCount i = samples)
    (hsupported : ∀ c i, sourceCount i ≠ 0 →
      splitWordWeight (encode c i) = index.count c)
    (c word) :
    ((ofMappedCountRows index sourceCount encode htotal hsupported).split c).counts word =
      WordType.mappedType (encode c) sourceCount word :=
  rfl

/-- A source word with the prescribed multiplicities realizes the mapped complete-split profile
on every leg.

Proof sketch: mapping the source word through `encode c` pushes its empirical multiplicities
forward.  Substitute the assumed source multiplicity row; the result is definitionally the split
row stored by `ofMappedCountRows`. -/
theorem ofMappedCountRows_split_isConsistent
    {I : Type*} [Fintype I] {depth samples : ℕ}
    (index : LevelConstituentIndex depth)
    (sourceCount : I → ℕ)
    (encode : Tensor.Leg → I → SplitWord depth)
    (htotal : ∑ i, sourceCount i = samples)
    (hsupported : ∀ c i, sourceCount i ≠ 0 →
      splitWordWeight (encode c i) = index.count c)
    (source : Fin samples → I)
    (hsource : WordType.multiplicity source = sourceCount)
    (c : Tensor.Leg) :
    ((ofMappedCountRows index sourceCount encode htotal hsupported).split c).IsConsistent
      (encode c ∘ source) := by
  change WordType.multiplicity (encode c ∘ source) =
    WordType.mappedType (encode c) sourceCount
  rw [WordType.multiplicity_comp_eq_mappedType, hsource]

end ExactInterfaceTermParameters
end AlgebraicComplexity
