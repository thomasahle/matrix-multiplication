/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryEdgeZero2Data0
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryEdgeZero2Data1
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryEdgeZero2Data2
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryPos3AlphaData0
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryPos3AlphaData1
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryMuData0

set_option autoImplicit false

/-!
# Audit of the narrow lower-primary chunks needed by q20 row multiplicities

These six archived chunks supply the exact lower fields of the q20 primary-table record.
Their complete-split convention follows [alman2025more],
`papers/sources/2404.16349/prelim.tex:249-278`. The row-multiplicity consumer uses the
reconstructed ordered top-row sum; no numerical table replaces that definition.

Every public declaration of the six chunks is asserted below. The fourteen direct zero-four
chunks have their separate `Q20UnpackedZeroFourRowData` audit. This audit does not import the
older top-law aggregate or its packed zero-four presentation, and proves no tensor extraction.
-/

open MatrixMultiplication.Generated.PairedTotalWeightPrimary

#assert_axioms EdgeZero2Data0.rawData
#assert_axioms EdgeZero2Data0.checked
#assert_axioms EdgeZero2Data0.data
#assert_axioms EdgeZero2Data0.data_isValid
#assert_axioms EdgeZero2Data0.valueCount_eq
#assert_axioms EdgeZero2Data0.data_eq_rawData
#assert_axioms EdgeZero2Data0.certificate
#assert_axioms EdgeZero2Data0.certificate_isValid
#assert_axioms EdgeZero2Data0.toDyadicTable
#assert_axioms EdgeZero2Data0.numerator

#assert_axioms EdgeZero2Data1.rawData
#assert_axioms EdgeZero2Data1.checked
#assert_axioms EdgeZero2Data1.data
#assert_axioms EdgeZero2Data1.data_isValid
#assert_axioms EdgeZero2Data1.valueCount_eq
#assert_axioms EdgeZero2Data1.data_eq_rawData
#assert_axioms EdgeZero2Data1.certificate
#assert_axioms EdgeZero2Data1.certificate_isValid
#assert_axioms EdgeZero2Data1.toDyadicTable
#assert_axioms EdgeZero2Data1.numerator

#assert_axioms EdgeZero2Data2.rawData
#assert_axioms EdgeZero2Data2.checked
#assert_axioms EdgeZero2Data2.data
#assert_axioms EdgeZero2Data2.data_isValid
#assert_axioms EdgeZero2Data2.valueCount_eq
#assert_axioms EdgeZero2Data2.data_eq_rawData
#assert_axioms EdgeZero2Data2.certificate
#assert_axioms EdgeZero2Data2.certificate_isValid
#assert_axioms EdgeZero2Data2.toDyadicTable
#assert_axioms EdgeZero2Data2.numerator

#assert_axioms Pos3AlphaData0.rawData
#assert_axioms Pos3AlphaData0.checked
#assert_axioms Pos3AlphaData0.data
#assert_axioms Pos3AlphaData0.data_isValid
#assert_axioms Pos3AlphaData0.valueCount_eq
#assert_axioms Pos3AlphaData0.data_eq_rawData
#assert_axioms Pos3AlphaData0.certificate
#assert_axioms Pos3AlphaData0.certificate_isValid
#assert_axioms Pos3AlphaData0.toDyadicTable
#assert_axioms Pos3AlphaData0.numerator

#assert_axioms Pos3AlphaData1.rawData
#assert_axioms Pos3AlphaData1.checked
#assert_axioms Pos3AlphaData1.data
#assert_axioms Pos3AlphaData1.data_isValid
#assert_axioms Pos3AlphaData1.valueCount_eq
#assert_axioms Pos3AlphaData1.data_eq_rawData
#assert_axioms Pos3AlphaData1.certificate
#assert_axioms Pos3AlphaData1.certificate_isValid
#assert_axioms Pos3AlphaData1.toDyadicTable
#assert_axioms Pos3AlphaData1.numerator

#assert_axioms MuData0.rawData
#assert_axioms MuData0.checked
#assert_axioms MuData0.data
#assert_axioms MuData0.data_isValid
#assert_axioms MuData0.valueCount_eq
#assert_axioms MuData0.data_eq_rawData

