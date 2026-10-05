/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.DyadicTable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exact algebra for dyadic masses

Recursive tensor certificates repeatedly form products, mixtures, and pushforwards of dyadic
probability rows.  Performing those operations on exact natural-number numerators has two useful
properties: denominators are tracked by adding bit widths, and every recurrence identity remains
kernel-computable.

This module supplies that algebra independently of the level-four Coppersmith--Winograd geometry.
It is intentionally small: later paper clients provide only finite index maps and exact numerator
tables, while these lemmas prove that their products and scatter-adds have the intended rational
semantics and preserve normalization.
-/

open scoped BigOperators

namespace AlgebraicComplexity

namespace DyadicMassData

variable {I J K : Type*}

/-- Exact numerator total of an arbitrary dyadic mass. -/
def totalNumerator [Fintype I] (data : DyadicMassData I) : ℕ :=
  ∑ i, data.numerator i

/-- Add two masses represented at the same bit width.  This operation is useful for assembling
unnormalized branches; it does not claim that the result is itself a probability distribution. -/
def add (left right : DyadicMassData I) : DyadicMassData I where
  numerator i := left.numerator i + right.numerator i

/-- Multiply all numerators by a power of two, thereby representing the same real mass at a wider
dyadic denominator. -/
def rescale (extra : ℕ) (data : DyadicMassData I) : DyadicMassData I where
  numerator i := data.numerator i * dyadicDenominator extra

/-- Tensor product of two exact dyadic masses. -/
def product (left : DyadicMassData I) (right : DyadicMassData J) :
    DyadicMassData (I × J) where
  numerator ij := left.numerator ij.1 * right.numerator ij.2

/-- Push a dyadic mass forward along a finite map.  This is the exact `scatter-add` operation used
by the numerical recursive evaluator. -/
def pushforward [Fintype I] [Fintype J] [DecidableEq J]
    (map : I → J) (data : DyadicMassData I) : DyadicMassData J where
  numerator j := ∑ i, if map i = j then data.numerator i else 0

/-- Mixture of dyadic conditional rows.  If the outer mass has width `outerBits` and every inner
row has width `innerBits`, the result has width `outerBits + innerBits`. -/
def bind [Fintype I]
    (outer : DyadicMassData I) (inner : I → DyadicMassData J) : DyadicMassData J where
  numerator j := ∑ i, outer.numerator i * (inner i).numerator j

@[simp] theorem add_numerator (left right : DyadicMassData I) (i : I) :
    (left.add right).numerator i = left.numerator i + right.numerator i :=
  rfl

@[simp] theorem rescale_numerator (extra : ℕ) (data : DyadicMassData I) (i : I) :
    (data.rescale extra).numerator i = data.numerator i * dyadicDenominator extra :=
  rfl

@[simp] theorem product_numerator (left : DyadicMassData I) (right : DyadicMassData J)
    (ij : I × J) :
    (left.product right).numerator ij = left.numerator ij.1 * right.numerator ij.2 :=
  rfl

theorem totalNumerator_add [Fintype I] (left right : DyadicMassData I) :
    (left.add right).totalNumerator = left.totalNumerator + right.totalNumerator := by
  simp [totalNumerator, add, Finset.sum_add_distrib]

theorem totalNumerator_rescale [Fintype I] (extra : ℕ) (data : DyadicMassData I) :
    (data.rescale extra).totalNumerator =
      data.totalNumerator * dyadicDenominator extra := by
  simp [totalNumerator, rescale, Finset.sum_mul]

theorem totalNumerator_product [Fintype I] [Fintype J]
    (left : DyadicMassData I) (right : DyadicMassData J) :
    (left.product right).totalNumerator =
      left.totalNumerator * right.totalNumerator := by
  unfold totalNumerator product
  rw [Fintype.sum_prod_type]
  calc
    ∑ i, ∑ j, left.numerator i * right.numerator j =
        ∑ i, left.numerator i * ∑ j, right.numerator j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = (∑ i, left.numerator i) * ∑ j, right.numerator j := by
      rw [Finset.sum_mul]

theorem totalNumerator_pushforward [Fintype I] [Fintype J] [DecidableEq J]
    (map : I → J) (data : DyadicMassData I) :
    (data.pushforward map).totalNumerator = data.totalNumerator := by
  unfold totalNumerator pushforward
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem totalNumerator_bind [Fintype I] [Fintype J]
    (outer : DyadicMassData I) (inner : I → DyadicMassData J) :
    (outer.bind inner).totalNumerator =
      ∑ i, outer.numerator i * (inner i).totalNumerator := by
  unfold totalNumerator bind
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum]

/-- Raising the denominator width by `extra` leaves the represented rational mass unchanged. -/
theorem toRational_rescale_weight [Fintype I]
    (bits extra : ℕ) (data : DyadicMassData I) (i : I) :
    ((data.rescale extra).toRational (bits + extra)).weight i =
      (data.toRational bits).weight i := by
  simp only [toRational, rescale, dyadicDenominator, pow_add]
  field_simp
  push_cast
  ring

/-- Tensoring numerator tables agrees exactly with multiplying their rational weights. -/
theorem toRational_product_weight [Fintype I] [Fintype J]
    (leftBits rightBits : ℕ) (left : DyadicMassData I) (right : DyadicMassData J)
    (ij : I × J) :
    ((left.product right).toRational (leftBits + rightBits)).weight ij =
      (left.toRational leftBits).weight ij.1 *
        (right.toRational rightBits).weight ij.2 := by
  simp only [toRational, product, dyadicDenominator, pow_add]
  field_simp
  push_cast
  ring

/-- A finite scatter-add agrees exactly with rational pushforward. -/
theorem toRational_pushforward_weight [Fintype I] [Fintype J] [DecidableEq J]
    (bits : ℕ) (map : I → J) (data : DyadicMassData I) (j : J) :
    ((data.pushforward map).toRational bits).weight j =
      ∑ i, if map i = j then (data.toRational bits).weight i else 0 := by
  simp only [toRational, pushforward]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all

/-- Exact numerator mixture agrees with the corresponding rational mixture. -/
theorem toRational_bind_weight [Fintype I] [Fintype J]
    (outerBits innerBits : ℕ) (outer : DyadicMassData I)
    (inner : I → DyadicMassData J) (j : J) :
    ((outer.bind inner).toRational (outerBits + innerBits)).weight j =
      ∑ i, (outer.toRational outerBits).weight i *
        ((inner i).toRational innerBits).weight j := by
  simp only [toRational, bind, dyadicDenominator, pow_add]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  field_simp

/-- Rescaling preserves exact simplex normalization at the enlarged bit width. -/
theorem rescale_isProbability [Fintype I]
    {bits : ℕ} {data : DyadicMassData I} (hdata : data.IsProbability bits)
    (extra : ℕ) :
    (data.rescale extra).IsProbability (bits + extra) := by
  unfold IsProbability at hdata ⊢
  rw [show (∑ i, (data.rescale extra).numerator i) =
      (data.rescale extra).totalNumerator by rfl,
    totalNumerator_rescale, show data.totalNumerator = ∑ i, data.numerator i by rfl,
    hdata]
  simp [dyadicDenominator, pow_add]

/-- Tensor products preserve exact simplex normalization. -/
theorem product_isProbability [Fintype I] [Fintype J]
    {leftBits rightBits : ℕ} {left : DyadicMassData I} {right : DyadicMassData J}
    (hleft : left.IsProbability leftBits) (hright : right.IsProbability rightBits) :
    (left.product right).IsProbability (leftBits + rightBits) := by
  unfold IsProbability at hleft hright ⊢
  rw [show (∑ ij, (left.product right).numerator ij) =
      (left.product right).totalNumerator by rfl,
    totalNumerator_product,
    show left.totalNumerator = ∑ i, left.numerator i by rfl,
    show right.totalNumerator = ∑ j, right.numerator j by rfl,
    hleft, hright]
  simp [dyadicDenominator, pow_add]

/-- Pushforward preserves exact simplex normalization. -/
theorem pushforward_isProbability [Fintype I] [Fintype J] [DecidableEq J]
    {bits : ℕ} {data : DyadicMassData I} (hdata : data.IsProbability bits)
    (map : I → J) :
    (data.pushforward map).IsProbability bits := by
  unfold IsProbability at hdata ⊢
  rw [show (∑ j, (data.pushforward map).numerator j) =
      (data.pushforward map).totalNumerator by rfl,
    totalNumerator_pushforward,
    show data.totalNumerator = ∑ i, data.numerator i by rfl,
    hdata]

/-- A normalized outer mass and normalized conditional rows give a normalized exact mixture. -/
theorem bind_isProbability [Fintype I] [Fintype J]
    {outerBits innerBits : ℕ} {outer : DyadicMassData I}
    {inner : I → DyadicMassData J}
    (houter : outer.IsProbability outerBits)
    (hinner : ∀ i, (inner i).IsProbability innerBits) :
    (outer.bind inner).IsProbability (outerBits + innerBits) := by
  unfold IsProbability at houter hinner ⊢
  rw [show (∑ j, (outer.bind inner).numerator j) =
      (outer.bind inner).totalNumerator by rfl,
    totalNumerator_bind]
  simp only [totalNumerator]
  simp_rw [hinner]
  rw [← Finset.sum_mul, houter]
  simp [dyadicDenominator, pow_add]

end DyadicMassData

end AlgebraicComplexity
