/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ComplementaryOccurrenceDefs
import AlgebraicComplexity.Combinatorics.ComplementaryOccurrenceMass
import AlgebraicComplexity.Combinatorics.ComplementaryOccurrenceCell

/-!
# Labelled complementary occurrences

This compatibility import exposes the occurrence definitions, total-mass identity, and exact cell
pushforward formula.  The declarations are split into small modules to keep Lean's per-module
axiom-metadata export below the shared-worktree memory budget.
-/
