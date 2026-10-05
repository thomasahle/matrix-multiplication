/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoRegionalCellEntry

/-! # Axiom audit for the cell-weight to region-entry adapter

A one-segment cell weight becomes a region entry at the uniform coarse spelling, by an equation
and a sixth power.

Primary source: `[duan2023faster]`, section 6.3 (the level-two global-value example),
`papers/sources/2210.10173/global_value.tex:332-348`. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_symSixRegionEntry_of_oneSegmentWeight
