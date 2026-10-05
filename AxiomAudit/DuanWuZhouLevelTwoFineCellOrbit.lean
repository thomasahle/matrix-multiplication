/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellOrbit

/-! # Axiom audit for the three orbit regions of the fine leaf

The orbit cells' row indices, published values and coarse targets (checked against
`dwz63Component`), their split-row degrees, the orbit region itself, and the two steps that turn the
certificate lane's `sym₃` obligation into a `sym₆` region entry.  That obligation is a binder
here: no typed-cut `112`/`beta` certificate is asserted to exist by this module.

Primary source: `[duan2023faster]`, section 6.3 (the level-two global-value example),
`papers/sources/2210.10173/global_value.tex:332-348` (the three orbit rows at `:341-347`);
`note:T112` at `papers/sources/2210.10173/second_power.tex:235` and `lem:non-rot-values` (d) at
`papers/sources/2210.10173/second_power.tex:144-152` (line 151). -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63OrbitRow
#assert_axioms AlgebraicComplexity.Examples.dwz63OrbitLogVal
#assert_axioms AlgebraicComplexity.Examples.dwz63OrbitTarget
#assert_axioms AlgebraicComplexity.Examples.dwz63OrbitTarget_eq_component
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaTildeDegree_six
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaTildeDegree_seven
#assert_axioms AlgebraicComplexity.Examples.dwz63_alphaTildeDegree_ten
#assert_axioms AlgebraicComplexity.Examples.dwz63OrbitRegion
#assert_axioms AlgebraicComplexity.Examples.dwz63_symSix_orbitRegionEntry_of_symThree
#assert_axioms AlgebraicComplexity.Examples.dwz63_exists_symSix_orbitRegionEntry
