/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ComplementaryOccurrence
import AlgebraicComplexity.Combinatorics.ComplementaryOccurrenceLaw

/-!
# Profiles on labelled complementary occurrences

This compatibility import exposes the lightweight occurrence cell-profile API together with its
exact occurrence/symbol law.  The declarations are split across two modules so Lean's per-module
axiom-metadata export remains bounded on memory-constrained builds.
-/
