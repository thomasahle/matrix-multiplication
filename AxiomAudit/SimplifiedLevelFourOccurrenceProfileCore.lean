/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.SimplifiedLevelFourOccurrenceProfileCore

set_option autoImplicit false

/-! Focused trust audit for the lightweight level-four occurrence-profile core used in the
recursive Coppersmith--Winograd analysis [coppersmith1990matrix]. -/

#assert_axioms MatrixMultiplication.SimplifiedRecursiveSplitTypes.levelFourSlotNumerator
#assert_axioms MatrixMultiplication.SimplifiedRecursiveSplitTypes.levelFourSamples
#assert_axioms MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles.levelFourChildSamples
#assert_axioms MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles.levelFourChildProductScale
#assert_axioms MatrixMultiplication.SimplifiedRecursiveLevelFourProfiles.levelFourParentSamples
#assert_axioms AlgebraicComplexity.Examples.levelFourOccurrenceSourceProfile
#assert_axioms AlgebraicComplexity.Examples.profileMass_levelFourOccurrenceSourceProfile
