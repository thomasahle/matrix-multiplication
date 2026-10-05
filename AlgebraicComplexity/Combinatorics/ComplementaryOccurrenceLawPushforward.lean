/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ComplementaryOccurrenceLaw

set_option autoImplicit false

/-!
# Occurrence-dependent pushforwards of complementary-occurrence laws

Claim 6.18 of Alman--Duan--Vassilevska Williams--Xu--Xu--Zhou,
*More Asymmetry Yields Faster Matrix Multiplication*, counts a fixed child word after pooling its
labelled child occurrences into compatibility cells.  The Total-Weight variant applies a quotient
to the child symbol first, and that quotient may depend on the labelled occurrence: for example,
positive recursive children use a blockwise total-weight map while boundary children remain
literal.

This file packages that operation for an arbitrary finite symbol law.  `pushforwardSymbols`
pushes every occurrence row through its own map and proves that the ordered-state marginal is
unchanged.  `cellJointProfile_pushforwardSymbols` then identifies cell pooling of the pushed law
with the direct heterogeneous fiber sum.  These are exact finite identities; no entropy bound,
compatibility relation, tensor restriction, or paper-specific alphabet is introduced.

The construction formalizes the finite pushforward operation used in [alman2025more, Claim 6.18],
`papers/sources/2404.16349/constituent.tex:402-429`, and in the Total-Weight pushed-cell formula
`better_bound/paper.tex:1641-1654`.
-/

open scoped BigOperators

namespace AlgebraicComplexity
namespace ComplementaryOccurrenceLaw

universe u v w x

variable {State : Type u} [Fintype State]
variable {RawSymbol : Type v} [Fintype RawSymbol]
variable {Symbol : Type w} [Fintype Symbol]
variable {Cell : Type x} [Fintype Cell] [DecidableEq Cell]
variable {profile : State → ℕ}

/-- Push each labelled occurrence row through its own map of finite symbol alphabets.

The resulting table has the same ordered-state row mass as the original law because a finite
pushforward partitions, rather than deletes or duplicates, the raw symbols. -/
noncomputable def pushforwardSymbols
    (law : ComplementaryOccurrenceLaw profile RawSymbol)
    (symbolMap : ComplementaryOccurrence State → RawSymbol → Symbol) :
    ComplementaryOccurrenceLaw profile Symbol where
  count occurrence := WordType.mappedType (symbolMap occurrence) (law.count occurrence)
  rowSum occurrence := by
    change WordType.profileMass
        (WordType.mappedType (symbolMap occurrence) (law.count occurrence)) =
      profile occurrence.orderedState
    rw [WordType.profileMass_mappedType]
    exact law.rowSum occurrence

/-- A row of the pushed occurrence law is the integral pushforward of the corresponding raw row. -/
theorem pushforwardSymbols_count
    (law : ComplementaryOccurrenceLaw profile RawSymbol)
    (symbolMap : ComplementaryOccurrence State → RawSymbol → Symbol)
    (occurrence : ComplementaryOccurrence State) (symbol : Symbol) :
    (law.pushforwardSymbols symbolMap).count occurrence symbol =
      WordType.mappedType (symbolMap occurrence) (law.count occurrence) symbol :=
  rfl

omit [Fintype Cell] in
/-- Pooling an occurrence-dependent symbol pushforward by cells is the direct heterogeneous
fiber sum.

Proof sketch: unfold the cell joint profile.  Each surviving occurrence contributes the row of
the pushed law; `pushforwardSymbols_count` rewrites that row to its finite fiber sum.  No exchange
of infinite sums or representative choice is involved. -/
theorem cellJointProfile_pushforwardSymbols
    (law : ComplementaryOccurrenceLaw profile RawSymbol)
    (symbolMap : ComplementaryOccurrence State → RawSymbol → Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell)
    (cell : Cell) (symbol : Symbol) :
    (law.pushforwardSymbols symbolMap).cellJointProfile complement cellOf (cell, symbol) =
      ∑ occurrence,
        if cellOf (occurrence.childState complement) = cell then
          WordType.mappedType (symbolMap occurrence) (law.count occurrence) symbol
        else 0 := by
  rfl

end ComplementaryOccurrenceLaw
end AlgebraicComplexity
