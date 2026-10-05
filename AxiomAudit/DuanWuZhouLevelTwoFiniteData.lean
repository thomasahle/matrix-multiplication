/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFiniteData

/-!
# Audit of the literal DWZ finite-profile client

The assertions cover all fifteen ordered profiles, their zero-extended table identity and
the literal 022 repeated-child and legal-zero probes for [duan2023faster], section 6.3.
They do not assert tensor extraction, a complete certificate DAG or an exponent bound.
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63ProfilePairs
#assert_axioms AlgebraicComplexity.Examples.dwz63FiniteProfile
#assert_axioms AlgebraicComplexity.Examples.dwz63FiniteProfile_valid
#assert_axioms AlgebraicComplexity.Examples.dwz63FiniteProfile_isOrderedSplitFor
#assert_axioms AlgebraicComplexity.Examples.dwz63FiniteProfile_countAt
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022Profile
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022Profile_eq
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022Profile_valid
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022Profile_isProbability
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022Descriptor
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022Descriptor_valid
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022ZeroProfile
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022ZeroProfile_valid
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022ZeroProfile_keeps_zero
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022ChildShapes
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022MiddleChild
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022MiddleChildren
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022MiddleChildren_valid
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022MiddleChildren_shapes
#assert_axioms AlgebraicComplexity.Examples.dwz63Row022MiddleChildren_count
