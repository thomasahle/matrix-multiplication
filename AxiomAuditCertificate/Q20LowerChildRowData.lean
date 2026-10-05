/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryPos3AData0
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero3Data0

set_option autoImplicit false

/-!
# Audit of the two level-three lower-row data chunks

Every public declaration of the regional-weight and zero-coordinate chunks is audited.
Their parameters correspond to [alman2025more], Section 6: region weights at
`papers/sources/2404.16349/constituent.tex:153-157` and zero-coordinate complete-split
parameters at `constituent.tex:14-35`. The two stored arrays are listed in
`better_bound/paper.tex:3483-3490`, Table `tab:arrays`.

Both chunks retain the literal data generated from the archived candidate with SHA-256
`90dfb5ea1f9560845093afcf88dc12d11af836d3b34983886f0e915729bbfb8d`.
This audit covers only exact sparse-array arithmetic. It neither identifies these rows with
a new top law nor proves profile consistency, compatibility cleanup, or an exponent endpoint.
The final example consumes both sealed value-count projections without reducing either table.

## Reference

- [alman2025more] Josh Alman et al., *More Asymmetry Yields Faster Matrix Multiplication*.
-/

open MatrixMultiplication.Generated.PairedTotalWeightPrimary

#assert_axioms Pos3AData0.rawData
#assert_axioms Pos3AData0.checked
#assert_axioms Pos3AData0.data
#assert_axioms Pos3AData0.data_isValid
#assert_axioms Pos3AData0.valueCount_eq
#assert_axioms Pos3AData0.data_eq_rawData
#assert_axioms Pos3AData0.certificate
#assert_axioms Pos3AData0.certificate_isValid
#assert_axioms Pos3AData0.toDyadicTable
#assert_axioms Pos3AData0.numerator

#assert_axioms Zero3Data0.rawData
#assert_axioms Zero3Data0.checked
#assert_axioms Zero3Data0.data
#assert_axioms Zero3Data0.data_isValid
#assert_axioms Zero3Data0.valueCount_eq
#assert_axioms Zero3Data0.data_eq_rawData
#assert_axioms Zero3Data0.certificate
#assert_axioms Zero3Data0.certificate_isValid
#assert_axioms Zero3Data0.toDyadicTable
#assert_axioms Zero3Data0.numerator

example : Pos3AData0.data.valueCount + Zero3Data0.data.valueCount = 736 := by
  calc
    _ = 420 + 316 := congrArg₂ Nat.add Pos3AData0.valueCount_eq Zero3Data0.valueCount_eq
    _ = 736 := rfl
