/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data0
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data1
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data2
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data3
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data4
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data5
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data6
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data7
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data8
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data9
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data10
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data11
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data12
import MatrixMultiplication.Generated.PairedTotalWeightPrimaryZero4Data13

set_option autoImplicit false

/-!
# Audit of the direct level-four boundary-row data used by q20

The complete-split distributions of [alman2025more],
`papers/sources/2404.16349/prelim.tex:249-278` and
`papers/sources/2404.16349/constituent.tex:14-35`, are represented by finite dyadic rows in
Total-Weight's primary-table reconstruction. The q20 lower-data record imports these fourteen
direct chunks; an audit of the packed presentation alone does not cover their declarations.

These assertions cover every public declaration of the imported direct chunks, including their
kernel-checked sparse-array validity witnesses. The literals retain the archived lower-data
candidate hash `90dfb5ea1f9560845093afcf88dc12d11af836d3b34983886f0e915729bbfb8d`.
They do not establish the top-law reconstruction, normalization of a semantic complete-split
profile, boundary source accounting, or any matrix-multiplication exponent.
-/

open MatrixMultiplication.Generated.PairedTotalWeightPrimary

#assert_axioms Zero4Data0.rawData
#assert_axioms Zero4Data0.checked
#assert_axioms Zero4Data0.data
#assert_axioms Zero4Data0.data_isValid
#assert_axioms Zero4Data0.valueCount_eq
#assert_axioms Zero4Data0.data_eq_rawData
#assert_axioms Zero4Data0.certificate
#assert_axioms Zero4Data0.certificate_isValid
#assert_axioms Zero4Data0.toDyadicTable
#assert_axioms Zero4Data0.numerator

#assert_axioms Zero4Data1.rawData
#assert_axioms Zero4Data1.checked
#assert_axioms Zero4Data1.data
#assert_axioms Zero4Data1.data_isValid
#assert_axioms Zero4Data1.valueCount_eq
#assert_axioms Zero4Data1.data_eq_rawData
#assert_axioms Zero4Data1.certificate
#assert_axioms Zero4Data1.certificate_isValid
#assert_axioms Zero4Data1.toDyadicTable
#assert_axioms Zero4Data1.numerator

#assert_axioms Zero4Data2.rawData
#assert_axioms Zero4Data2.checked
#assert_axioms Zero4Data2.data
#assert_axioms Zero4Data2.data_isValid
#assert_axioms Zero4Data2.valueCount_eq
#assert_axioms Zero4Data2.data_eq_rawData
#assert_axioms Zero4Data2.certificate
#assert_axioms Zero4Data2.certificate_isValid
#assert_axioms Zero4Data2.toDyadicTable
#assert_axioms Zero4Data2.numerator

#assert_axioms Zero4Data3.rawData
#assert_axioms Zero4Data3.checked
#assert_axioms Zero4Data3.data
#assert_axioms Zero4Data3.data_isValid
#assert_axioms Zero4Data3.valueCount_eq
#assert_axioms Zero4Data3.data_eq_rawData
#assert_axioms Zero4Data3.certificate
#assert_axioms Zero4Data3.certificate_isValid
#assert_axioms Zero4Data3.toDyadicTable
#assert_axioms Zero4Data3.numerator

#assert_axioms Zero4Data4.rawData
#assert_axioms Zero4Data4.checked
#assert_axioms Zero4Data4.data
#assert_axioms Zero4Data4.data_isValid
#assert_axioms Zero4Data4.valueCount_eq
#assert_axioms Zero4Data4.data_eq_rawData
#assert_axioms Zero4Data4.certificate
#assert_axioms Zero4Data4.certificate_isValid
#assert_axioms Zero4Data4.toDyadicTable
#assert_axioms Zero4Data4.numerator

#assert_axioms Zero4Data5.rawData
#assert_axioms Zero4Data5.checked
#assert_axioms Zero4Data5.data
#assert_axioms Zero4Data5.data_isValid
#assert_axioms Zero4Data5.valueCount_eq
#assert_axioms Zero4Data5.data_eq_rawData
#assert_axioms Zero4Data5.certificate
#assert_axioms Zero4Data5.certificate_isValid
#assert_axioms Zero4Data5.toDyadicTable
#assert_axioms Zero4Data5.numerator

#assert_axioms Zero4Data6.rawData
#assert_axioms Zero4Data6.checked
#assert_axioms Zero4Data6.data
#assert_axioms Zero4Data6.data_isValid
#assert_axioms Zero4Data6.valueCount_eq
#assert_axioms Zero4Data6.data_eq_rawData
#assert_axioms Zero4Data6.certificate
#assert_axioms Zero4Data6.certificate_isValid
#assert_axioms Zero4Data6.toDyadicTable
#assert_axioms Zero4Data6.numerator

#assert_axioms Zero4Data7.rawData
#assert_axioms Zero4Data7.checked
#assert_axioms Zero4Data7.data
#assert_axioms Zero4Data7.data_isValid
#assert_axioms Zero4Data7.valueCount_eq
#assert_axioms Zero4Data7.data_eq_rawData
#assert_axioms Zero4Data7.certificate
#assert_axioms Zero4Data7.certificate_isValid
#assert_axioms Zero4Data7.toDyadicTable
#assert_axioms Zero4Data7.numerator

#assert_axioms Zero4Data8.rawData
#assert_axioms Zero4Data8.checked
#assert_axioms Zero4Data8.data
#assert_axioms Zero4Data8.data_isValid
#assert_axioms Zero4Data8.valueCount_eq
#assert_axioms Zero4Data8.data_eq_rawData
#assert_axioms Zero4Data8.certificate
#assert_axioms Zero4Data8.certificate_isValid
#assert_axioms Zero4Data8.toDyadicTable
#assert_axioms Zero4Data8.numerator

#assert_axioms Zero4Data9.rawData
#assert_axioms Zero4Data9.checked
#assert_axioms Zero4Data9.data
#assert_axioms Zero4Data9.data_isValid
#assert_axioms Zero4Data9.valueCount_eq
#assert_axioms Zero4Data9.data_eq_rawData
#assert_axioms Zero4Data9.certificate
#assert_axioms Zero4Data9.certificate_isValid
#assert_axioms Zero4Data9.toDyadicTable
#assert_axioms Zero4Data9.numerator

#assert_axioms Zero4Data10.rawData
#assert_axioms Zero4Data10.checked
#assert_axioms Zero4Data10.data
#assert_axioms Zero4Data10.data_isValid
#assert_axioms Zero4Data10.valueCount_eq
#assert_axioms Zero4Data10.data_eq_rawData
#assert_axioms Zero4Data10.certificate
#assert_axioms Zero4Data10.certificate_isValid
#assert_axioms Zero4Data10.toDyadicTable
#assert_axioms Zero4Data10.numerator

#assert_axioms Zero4Data11.rawData
#assert_axioms Zero4Data11.checked
#assert_axioms Zero4Data11.data
#assert_axioms Zero4Data11.data_isValid
#assert_axioms Zero4Data11.valueCount_eq
#assert_axioms Zero4Data11.data_eq_rawData
#assert_axioms Zero4Data11.certificate
#assert_axioms Zero4Data11.certificate_isValid
#assert_axioms Zero4Data11.toDyadicTable
#assert_axioms Zero4Data11.numerator

#assert_axioms Zero4Data12.rawData
#assert_axioms Zero4Data12.checked
#assert_axioms Zero4Data12.data
#assert_axioms Zero4Data12.data_isValid
#assert_axioms Zero4Data12.valueCount_eq
#assert_axioms Zero4Data12.data_eq_rawData
#assert_axioms Zero4Data12.certificate
#assert_axioms Zero4Data12.certificate_isValid
#assert_axioms Zero4Data12.toDyadicTable
#assert_axioms Zero4Data12.numerator

#assert_axioms Zero4Data13.rawData
#assert_axioms Zero4Data13.checked
#assert_axioms Zero4Data13.data
#assert_axioms Zero4Data13.data_isValid
#assert_axioms Zero4Data13.valueCount_eq
#assert_axioms Zero4Data13.data_eq_rawData
#assert_axioms Zero4Data13.certificate
#assert_axioms Zero4Data13.certificate_isValid
#assert_axioms Zero4Data13.toDyadicTable
#assert_axioms Zero4Data13.numerator

