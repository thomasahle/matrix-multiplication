import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 0, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk0

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 1418175041551668953055704731615232
def positiveArguments : Array ℕ := #[
    193, 1, 2445, 2675, 2445, 2675,
    171, 28557, 741, 30723, 45999, 1425,
    45999, 47937, 28557, 1425, 403, 455,
    195, 5135, 455, 195, 455, 455,
    18863, 117, 5135, 18863, 403, 455,
    117, 455, 57, 1653, 1463, 95,
    57, 95, 2907, 95, 57, 46569,
    2983, 1653, 2907, 95, 2983, 95
  ]
def positiveCoefficients : Array ℕ := #[
    15291035365253017155553982414848, 158456325028528675187087900672, 189172712253297173258022420480, 206968100318024514709697331200, 189172712253297173258022420480, 206968100318024514709697331200,
    26460968339725003375968780288, 552372714091759445473348288512, 28666049034702086990632845312, 594269247296324034151965523968, 889750060423253238516950237184, 27563508687213545183300812800,
    889750060423253238516950237184, 927236432237863659966239342592, 552372714091759445473348288512, 27563508687213545183300812800, 62361229479001031348043382784, 70407839734356003134887690240,
    60349576915162288401332305920, 794602762716303463950875361280, 70407839734356003134887690240, 60349576915162288401332305920, 70407839734356003134887690240, 70407839734356003134887690240,
    2918907870130016015677772529664, 72419492298194746081598767104, 794602762716303463950875361280, 2918907870130016015677772529664, 62361229479001031348043382784, 70407839734356003134887690240,
    72419492298194746081598767104, 70407839734356003134887690240, 2205080694977083614664065024, 31973670077167712412628942848, 56597071171078479443044335616, 1837567245814236345553387520,
    35281291119633337834625040384, 1837567245814236345553387520, 56229557721915632173933658112, 58802151866055563057708400640, 35281291119633337834625040384, 900775463898138656590270562304,
    57699611518567021250376368128, 31973670077167712412628942848, 56229557721915632173933658112, 1837567245814236345553387520, 57699611518567021250376368128, 1837567245814236345553387520
  ]
def positiveScales : Array ℕ := #[
    7, 0, 11, 11, 11, 11,
    7, 14, 9, 14, 15, 10,
    15, 15, 14, 10, 8, 8,
    7, 12, 8, 7, 8, 8,
    14, 6, 12, 14, 8, 8,
    6, 8, 5, 10, 10, 6,
    5, 6, 11, 6, 5, 15,
    11, 10, 11, 6, 11, 6
  ]
def negativeArguments : Array ℕ := #[
    1377, 37, 45, 45, 1163, 37,
    123414963, 11125325, 123414963, 11125325, 234595, 3,
    1, 5, 57, 13
  ]
def negativeCoefficients : Array ℕ := #[
    13317526828874754988563234816, 715684085211860471426056192, 13926825441960528092615147520, 13926825441960528092615147520, 22495691651389019682932523008, 715684085211860471426056192,
    569151059331833396358807552, 51306505752960679333068800, 569151059331833396358807552, 51306505752960679333068800, 1107843565048804418907013120, 928455029464035206174343168,
    158456325028528675187087900672, 792281625142643375935439503360, 4516005263313067242832005169152, 8239728901483491109728570834944
  ]
def negativeScales : Array ℕ := #[
    10, 5, 5, 5, 10, 5,
    26, 23, 26, 23, 17, 1,
    0, 2, 5, 3
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7592457037267794, 0, 11255618749839595, 11385323176175871, 11255618749839595, 11385323176175871,
    7417852514885896, 14801556807318634, 9533329732305783, 14907031476611228, 15489314877442509, 10476746203939458,
    15489314877442509, 15548852004419805, 14801556807318634, 10476746203939458, 8654636028526477, 8829722735013603,
    7607330313749179, 12326148561205557, 8829722735013603, 7607330313749179, 8829722735013603, 8829722735013603,
    14203271522207836, 6870364719426147, 12326148561205557, 14203271522207836, 8654636028526477, 8829722735013603,
    6870364719426147, 8829722735013603, 5832890014087662, 10690871009288692, 10514714054138458, 6569855608330797,
    5832890014087662, 6569855608330797, 11505315356136216, 6569855608330797, 5832890014087662, 15507082282310403,
    11542548262335146, 10690871009288692, 11505315356136216, 6569855608330797, 11542548262335146, 6569855608330797
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    10427312844134984, 5209453365628950, 5491853096329881, 5491853096329881, 10183635381473219, 5209453365628950,
    26878942081502675, 23407344145822237, 26878942081502675, 23407344145822237, 17839812740923619, 1584962500724866,
    0, 2321928094887363, 5832890015409720, 3700439718214233
  ]

abbrev PositiveTerm := Fin 48
abbrev NegativeTerm := Fin 16
def positiveArgument (term : PositiveTerm) : ℕ :=
  positiveArguments[term.val]?.getD 0
def positiveCoefficient (term : PositiveTerm) : ℕ :=
  positiveCoefficients[term.val]?.getD 0
def positiveScale (term : PositiveTerm) : ℕ :=
  positiveScales[term.val]?.getD 0
def negativeArgument (term : NegativeTerm) : ℕ :=
  negativeArguments[term.val]?.getD 0
def negativeCoefficient (term : NegativeTerm) : ℕ :=
  negativeCoefficients[term.val]?.getD 0
def negativeScale (term : NegativeTerm) : ℕ :=
  negativeScales[term.val]?.getD 0
def positiveLogLowerNumerator (term : PositiveTerm) : ℕ :=
  positiveLogLowerNumerators[term.val]?.getD 0
def negativeLogUpperNumerator (term : NegativeTerm) : ℕ :=
  negativeLogUpperNumerators[term.val]?.getD 0

noncomputable def positiveLogLower (term : PositiveTerm) : ℝ :=
  (positiveLogLowerNumerator term : ℝ) / logBoundDenominator
noncomputable def negativeLogUpper (term : NegativeTerm) : ℝ :=
  (negativeLogUpperNumerator term : ℝ) / logBoundDenominator
def positiveLogLowerRat (term : PositiveTerm) : ℚ :=
  positiveLogLowerNumerator term / logBoundDenominator
def negativeLogUpperRat (term : NegativeTerm) : ℚ :=
  negativeLogUpperNumerator term / logBoundDenominator

theorem positiveScales_valid :
    ∀ term, 2 ^ positiveScale term ≤ positiveArgument term := by decide

theorem negativeScales_valid :
    ∀ term, 2 ^ negativeScale term ≤ negativeArgument term := by decide

noncomputable def positiveExact : ℝ :=
  Form.natLogSum bits positiveArgument positiveCoefficient
noncomputable def negativeExact : ℝ :=
  Form.natLogSum bits negativeArgument negativeCoefficient
noncomputable def positiveRationalLower : ℝ :=
  ∑ term, mass bits (positiveCoefficient term) * positiveLogLower term
noncomputable def negativeRationalUpper : ℝ :=
  ∑ term, mass bits (negativeCoefficient term) * negativeLogUpper term
noncomputable def positiveFloor : ℝ := 483387603 / 125000000000
noncomputable def negativeCeiling : ℝ := 356623337 / 500000000000

theorem positiveLogLowerRat_le_fastRat :
    ∀ term, positiveLogLowerRat term ≤
      MatrixMultiplication.RationalDyadicLog.numeratorLogLower
        (positiveArgument term) (positiveScale term) 8 := by decide +kernel

theorem negativeFastRat_le_logUpperRat :
    ∀ term, MatrixMultiplication.RationalDyadicLog.numeratorLogUpper
        (negativeArgument term) (negativeScale term) 8 ≤
      negativeLogUpperRat term := by decide +kernel

theorem positiveLogLower_le_fast (term : PositiveTerm) :
    positiveLogLower term ≤ MatrixMultiplication.FastDyadicLog.numeratorLogLower
      (positiveArgument term) (positiveScale term) 8 := by
  simpa [positiveLogLower, positiveLogLowerRat] using
    MatrixMultiplication.RationalDyadicLog.cast_le_fastLower
      (positiveLogLowerRat_le_fastRat term)

theorem negativeFast_le_logUpper (term : NegativeTerm) :
    MatrixMultiplication.FastDyadicLog.numeratorLogUpper
        (negativeArgument term) (negativeScale term) 8 ≤
      negativeLogUpper term := by
  simpa [negativeLogUpper, negativeLogUpperRat] using
    MatrixMultiplication.RationalDyadicLog.fastUpper_le_cast
      (negativeFastRat_le_logUpperRat term)

theorem positiveFloor_le_rationalLower : positiveFloor ≤ positiveRationalLower := by
  norm_num [positiveRationalLower, negativeRationalUpper,
    positiveFloor, negativeCeiling, bits,
    positiveLogLower, negativeLogUpper, logBoundDenominator,
    positiveLogLowerNumerator, negativeLogUpperNumerator,
    positiveLogLowerNumerators, negativeLogUpperNumerators,
    positiveCoefficient, negativeCoefficient,
    positiveCoefficients, negativeCoefficients,
    Fin.sum_univ_succ, mass]

theorem negativeRationalUpper_le_ceiling : negativeRationalUpper ≤ negativeCeiling := by
  norm_num [positiveRationalLower, negativeRationalUpper,
    positiveFloor, negativeCeiling, bits,
    positiveLogLower, negativeLogUpper, logBoundDenominator,
    positiveLogLowerNumerator, negativeLogUpperNumerator,
    positiveLogLowerNumerators, negativeLogUpperNumerators,
    positiveCoefficient, negativeCoefficient,
    positiveCoefficients, negativeCoefficients,
    Fin.sum_univ_succ, mass]

theorem positiveFloor_le_exact : positiveFloor ≤ positiveExact :=
  positiveFloor_le_rationalLower.trans
    (weightedLowerWithScale_le_natLogSum 8 bits
      positiveArgument positiveCoefficient positiveScale positiveLogLower
      positiveScales_valid positiveLogLower_le_fast)

theorem negativeExact_le_ceiling : negativeExact ≤ negativeCeiling :=
  (natLogSum_le_weightedUpperWithScale 8 bits
    negativeArgument negativeCoefficient negativeScale negativeLogUpper
    negativeScales_valid negativeFast_le_logUpper).trans
      negativeRationalUpper_le_ceiling

/-- Sign-separated exact form used by the directed arithmetic checker. -/
def signedForm : Form :=
  SignedDyadicLogCertificate.Form.ofSignedFamilies constantNumerator
    positiveArgument positiveCoefficient negativeArgument negativeCoefficient

/-- Exact source-order form before this shard's bounded power-of-two normalization. -/
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 13317526828874754988563234816, coefficient := (-13317526828874754988563234816) }, { argument := 715684085211860471426056192, coefficient := (-715684085211860471426056192) }, { argument := 13926825441960528092615147520, coefficient := (-13926825441960528092615147520) }, { argument := 13926825441960528092615147520, coefficient := (-13926825441960528092615147520) }, { argument := 22495691651389019682932523008, coefficient := (-22495691651389019682932523008) }, { argument := 715684085211860471426056192, coefficient := (-715684085211860471426056192) }, { argument := 569151059331833396358807552, coefficient := (-569151059331833396358807552) }, { argument := 51306505752960679333068800, coefficient := (-51306505752960679333068800) }, { argument := 569151059331833396358807552, coefficient := (-569151059331833396358807552) }, { argument := 51306505752960679333068800, coefficient := (-51306505752960679333068800) }, { argument := 1107843565048804418907013120, coefficient := (-1107843565048804418907013120) }, { argument := 928455029464035206174343168, coefficient := (-928455029464035206174343168) }, { argument := 15291035365253017155553982414848, coefficient := 15291035365253017155553982414848 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 189172712253297173258022420480, coefficient := 189172712253297173258022420480 }, { argument := 206968100318024514709697331200, coefficient := 206968100318024514709697331200 }, { argument := 189172712253297173258022420480, coefficient := 189172712253297173258022420480 }, { argument := 206968100318024514709697331200, coefficient := 206968100318024514709697331200 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 26460968339725003375968780288, coefficient := 26460968339725003375968780288 }, { argument := 552372714091759445473348288512, coefficient := 552372714091759445473348288512 }, { argument := 28666049034702086990632845312, coefficient := 28666049034702086990632845312 }, { argument := 594269247296324034151965523968, coefficient := 594269247296324034151965523968 }, { argument := 889750060423253238516950237184, coefficient := 889750060423253238516950237184 }, { argument := 27563508687213545183300812800, coefficient := 27563508687213545183300812800 }, { argument := 889750060423253238516950237184, coefficient := 889750060423253238516950237184 }, { argument := 927236432237863659966239342592, coefficient := 927236432237863659966239342592 }, { argument := 552372714091759445473348288512, coefficient := 552372714091759445473348288512 }, { argument := 27563508687213545183300812800, coefficient := 27563508687213545183300812800 }, { argument := 4516005263313067242832005169152, coefficient := (-4516005263313067242832005169152) }, { argument := 62361229479001031348043382784, coefficient := 62361229479001031348043382784 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 60349576915162288401332305920, coefficient := 60349576915162288401332305920 }, { argument := 794602762716303463950875361280, coefficient := 794602762716303463950875361280 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 60349576915162288401332305920, coefficient := 60349576915162288401332305920 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 2918907870130016015677772529664, coefficient := 2918907870130016015677772529664 }, { argument := 72419492298194746081598767104, coefficient := 72419492298194746081598767104 }, { argument := 794602762716303463950875361280, coefficient := 794602762716303463950875361280 }, { argument := 2918907870130016015677772529664, coefficient := 2918907870130016015677772529664 }, { argument := 62361229479001031348043382784, coefficient := 62361229479001031348043382784 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 72419492298194746081598767104, coefficient := 72419492298194746081598767104 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 8239728901483491109728570834944, coefficient := (-8239728901483491109728570834944) }, { argument := 2205080694977083614664065024, coefficient := 2205080694977083614664065024 }, { argument := 31973670077167712412628942848, coefficient := 31973670077167712412628942848 }, { argument := 56597071171078479443044335616, coefficient := 56597071171078479443044335616 }, { argument := 1837567245814236345553387520, coefficient := 1837567245814236345553387520 }, { argument := 35281291119633337834625040384, coefficient := 35281291119633337834625040384 }, { argument := 1837567245814236345553387520, coefficient := 1837567245814236345553387520 }, { argument := 56229557721915632173933658112, coefficient := 56229557721915632173933658112 }, { argument := 58802151866055563057708400640, coefficient := 58802151866055563057708400640 }, { argument := 35281291119633337834625040384, coefficient := 35281291119633337834625040384 }, { argument := 900775463898138656590270562304, coefficient := 900775463898138656590270562304 }, { argument := 57699611518567021250376368128, coefficient := 57699611518567021250376368128 }, { argument := 31973670077167712412628942848, coefficient := 31973670077167712412628942848 }, { argument := 56229557721915632173933658112, coefficient := 56229557721915632173933658112 }, { argument := 1837567245814236345553387520, coefficient := 1837567245814236345553387520 }, { argument := 57699611518567021250376368128, coefficient := 57699611518567021250376368128 }, { argument := 1837567245814236345553387520, coefficient := 1837567245814236345553387520 }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := Form.normalizePowersOfTwo rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  unfold form
  exact Form.eval_normalizePowersOfTwo bits rawForm

/-- Sign separation retains this bounded shard's exact constant. -/
theorem signedForm_constant : signedForm.constantNumerator = form.constantNumerator := by
  rfl

/-- Sign separation only permutes this bounded shard's exact term list. -/
theorem signedForm_terms_perm : signedForm.terms.Perm form.terms := by
  decide +kernel

/-- Rational lower endpoint contributed by this shard. -/
noncomputable def lower : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveFloor - negativeCeiling

/-- Kernel-checked lower-bound certificate before restoring source term order. -/
noncomputable def signedCertificate : LowerBound bits :=
  LowerBound.ofSignedFamilies bits constantNumerator positiveArgument positiveCoefficient
    negativeArgument negativeCoefficient positiveFloor negativeCeiling
      positiveFloor_le_exact negativeExact_le_ceiling

/-- Kernel-checked lower-bound certificate in the shard's exact source order. -/
noncomputable def certificate : LowerBound bits :=
  LowerBound.reorder signedCertificate form signedForm_constant signedForm_terms_perm

@[simp] theorem certificate_form : certificate.form = form := rfl

@[simp] theorem certificate_lower : certificate.lower = lower := by
  simp [certificate, LowerBound.reorder, signedCertificate, LowerBound.ofSignedFamilies, lower,
    constantNumerator, bits]

end TermShard4


end Parent3

namespace Parent3

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-447749377973295271788005812076544)
def positiveArguments : Array ℕ := #[
    2907, 95, 57, 47, 35, 37,
    3, 643, 1163, 35, 643, 19,
    19, 37, 37, 1163, 37, 47,
    3, 1, 19, 19, 9662991, 70399927,
    19325995, 11667957, 116620689, 233241321, 11667957, 20795,
    851975, 17542825, 851975, 20795, 42083, 8346525,
    8346525, 42083
  ]
def positiveCoefficients : Array ℕ := #[
    56229557721915632173933658112, 58802151866055563057708400640, 2205080694977083614664065024, 909112216350201139379044352, 676998458984192337835458560, 715684085211860471426056192,
    928455029464035206174343168, 12437428832195304949377138688, 22495691651389019682932523008, 676998458984192337835458560, 12437428832195304949377138688, 735026898325694538221355008,
    735026898325694538221355008, 715684085211860471426056192, 715684085211860471426056192, 22495691651389019682932523008, 715684085211860471426056192, 909112216350201139379044352,
    928455029464035206174343168, 79228162514264337593543950336, 752667543885511207138667528192, 752667543885511207138667528192, 1460229914325473147940400791552, 5319268090580316376961564803072,
    1460230896577701584826605240320, 55100369060364256958660739072, 2202902531771058888027119026176, 2202901993421279840887564664832, 55100369060364256958660739072, 392806444045097088875233280,
    64373410947885855695018393600, 662749190358781470367652249600, 64373410947885855695018393600, 392806444045097088875233280, 397462697397206559055937536, 78830699816867131034488012800,
    78830699816867131034488012800, 397462697397206559055937536
  ]
def positiveScales : Array ℕ := #[
    11, 6, 5, 5, 5, 5,
    1, 9, 10, 5, 9, 4,
    4, 5, 5, 10, 5, 5,
    1, 0, 4, 4, 23, 26,
    24, 23, 26, 27, 23, 14,
    19, 24, 19, 14, 15, 22,
    22, 15
  ]
def negativeArguments : Array ℕ := #[
    19, 1, 1, 19, 13, 57,
    5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1505335087771022414277335056384, 79228162514264337593543950336, 79228162514264337593543950336, 1505335087771022414277335056384, 8239728901483491109728570834944, 4516005263313067242832005169152,
    792281625142643375935439503360, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    4, 0, 0, 4, 3, 5,
    2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11505315356136216, 6569855608330797, 5832890014087662, 5554588851677541, 5129283016944966, 5209453365628949,
    1584962500720924, 9328674927327946, 10183635381473218, 5129283016944966, 9328674927327946, 4247927513443585,
    4247927513443585, 5209453365628949, 5209453365628949, 10183635381473218, 5209453365628949, 5554588851677541,
    1584962500720924, 0, 4247927513443585, 4247927513443585, 23204038387056918, 26069070597096941,
    24204039357513644, 23476048638796366, 26797248510463714, 27797248157894938, 23476048638796366, 14343949064533718,
    19700451571661328, 24064377754372501, 19700451571661328, 14343949064533718, 15360949934247378, 22992744237616252,
    22992744237616252, 15360949934247378
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    4247927513443586, 0, 0, 4247927513443586, 3700439718214233, 5832890015409720,
    2321928094887363, 0
  ]

abbrev PositiveTerm := Fin 38
abbrev NegativeTerm := Fin 8
def positiveArgument (term : PositiveTerm) : ℕ :=
  positiveArguments[term.val]?.getD 0
def positiveCoefficient (term : PositiveTerm) : ℕ :=
  positiveCoefficients[term.val]?.getD 0
def positiveScale (term : PositiveTerm) : ℕ :=
  positiveScales[term.val]?.getD 0
def negativeArgument (term : NegativeTerm) : ℕ :=
  negativeArguments[term.val]?.getD 0
def negativeCoefficient (term : NegativeTerm) : ℕ :=
  negativeCoefficients[term.val]?.getD 0
def negativeScale (term : NegativeTerm) : ℕ :=
  negativeScales[term.val]?.getD 0
def positiveLogLowerNumerator (term : PositiveTerm) : ℕ :=
  positiveLogLowerNumerators[term.val]?.getD 0
def negativeLogUpperNumerator (term : NegativeTerm) : ℕ :=
  negativeLogUpperNumerators[term.val]?.getD 0

noncomputable def positiveLogLower (term : PositiveTerm) : ℝ :=
  (positiveLogLowerNumerator term : ℝ) / logBoundDenominator
noncomputable def negativeLogUpper (term : NegativeTerm) : ℝ :=
  (negativeLogUpperNumerator term : ℝ) / logBoundDenominator
def positiveLogLowerRat (term : PositiveTerm) : ℚ :=
  positiveLogLowerNumerator term / logBoundDenominator
def negativeLogUpperRat (term : NegativeTerm) : ℚ :=
  negativeLogUpperNumerator term / logBoundDenominator

theorem positiveScales_valid :
    ∀ term, 2 ^ positiveScale term ≤ positiveArgument term := by decide

theorem negativeScales_valid :
    ∀ term, 2 ^ negativeScale term ≤ negativeArgument term := by decide

noncomputable def positiveExact : ℝ :=
  Form.natLogSum bits positiveArgument positiveCoefficient
noncomputable def negativeExact : ℝ :=
  Form.natLogSum bits negativeArgument negativeCoefficient
noncomputable def positiveRationalLower : ℝ :=
  ∑ term, mass bits (positiveCoefficient term) * positiveLogLower term
noncomputable def negativeRationalUpper : ℝ :=
  ∑ term, mass bits (negativeCoefficient term) * negativeLogUpper term
noncomputable def positiveFloor : ℝ := 2173015461 / 500000000000
noncomputable def negativeCeiling : ℝ := 860177029 / 1000000000000

theorem positiveLogLowerRat_le_fastRat :
    ∀ term, positiveLogLowerRat term ≤
      MatrixMultiplication.RationalDyadicLog.numeratorLogLower
        (positiveArgument term) (positiveScale term) 8 := by decide +kernel

theorem negativeFastRat_le_logUpperRat :
    ∀ term, MatrixMultiplication.RationalDyadicLog.numeratorLogUpper
        (negativeArgument term) (negativeScale term) 8 ≤
      negativeLogUpperRat term := by decide +kernel

theorem positiveLogLower_le_fast (term : PositiveTerm) :
    positiveLogLower term ≤ MatrixMultiplication.FastDyadicLog.numeratorLogLower
      (positiveArgument term) (positiveScale term) 8 := by
  simpa [positiveLogLower, positiveLogLowerRat] using
    MatrixMultiplication.RationalDyadicLog.cast_le_fastLower
      (positiveLogLowerRat_le_fastRat term)

theorem negativeFast_le_logUpper (term : NegativeTerm) :
    MatrixMultiplication.FastDyadicLog.numeratorLogUpper
        (negativeArgument term) (negativeScale term) 8 ≤
      negativeLogUpper term := by
  simpa [negativeLogUpper, negativeLogUpperRat] using
    MatrixMultiplication.RationalDyadicLog.fastUpper_le_cast
      (negativeFastRat_le_logUpperRat term)

theorem positiveFloor_le_rationalLower : positiveFloor ≤ positiveRationalLower := by
  norm_num [positiveRationalLower, negativeRationalUpper,
    positiveFloor, negativeCeiling, bits,
    positiveLogLower, negativeLogUpper, logBoundDenominator,
    positiveLogLowerNumerator, negativeLogUpperNumerator,
    positiveLogLowerNumerators, negativeLogUpperNumerators,
    positiveCoefficient, negativeCoefficient,
    positiveCoefficients, negativeCoefficients,
    Fin.sum_univ_succ, mass]

theorem negativeRationalUpper_le_ceiling : negativeRationalUpper ≤ negativeCeiling := by
  norm_num [positiveRationalLower, negativeRationalUpper,
    positiveFloor, negativeCeiling, bits,
    positiveLogLower, negativeLogUpper, logBoundDenominator,
    positiveLogLowerNumerator, negativeLogUpperNumerator,
    positiveLogLowerNumerators, negativeLogUpperNumerators,
    positiveCoefficient, negativeCoefficient,
    positiveCoefficients, negativeCoefficients,
    Fin.sum_univ_succ, mass]

theorem positiveFloor_le_exact : positiveFloor ≤ positiveExact :=
  positiveFloor_le_rationalLower.trans
    (weightedLowerWithScale_le_natLogSum 8 bits
      positiveArgument positiveCoefficient positiveScale positiveLogLower
      positiveScales_valid positiveLogLower_le_fast)

theorem negativeExact_le_ceiling : negativeExact ≤ negativeCeiling :=
  (natLogSum_le_weightedUpperWithScale 8 bits
    negativeArgument negativeCoefficient negativeScale negativeLogUpper
    negativeScales_valid negativeFast_le_logUpper).trans
      negativeRationalUpper_le_ceiling

/-- Sign-separated exact form used by the directed arithmetic checker. -/
def signedForm : Form :=
  SignedDyadicLogCertificate.Form.ofSignedFamilies constantNumerator
    positiveArgument positiveCoefficient negativeArgument negativeCoefficient

/-- Exact source-order form before this shard's bounded power-of-two normalization. -/
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 56229557721915632173933658112, coefficient := 56229557721915632173933658112 }, { argument := 58802151866055563057708400640, coefficient := 58802151866055563057708400640 }, { argument := 2205080694977083614664065024, coefficient := 2205080694977083614664065024 }, { argument := 1505335087771022414277335056384, coefficient := (-1505335087771022414277335056384) }, { argument := 909112216350201139379044352, coefficient := 909112216350201139379044352 }, { argument := 676998458984192337835458560, coefficient := 676998458984192337835458560 }, { argument := 715684085211860471426056192, coefficient := 715684085211860471426056192 }, { argument := 928455029464035206174343168, coefficient := 928455029464035206174343168 }, { argument := 12437428832195304949377138688, coefficient := 12437428832195304949377138688 }, { argument := 22495691651389019682932523008, coefficient := 22495691651389019682932523008 }, { argument := 676998458984192337835458560, coefficient := 676998458984192337835458560 }, { argument := 12437428832195304949377138688, coefficient := 12437428832195304949377138688 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 715684085211860471426056192, coefficient := 715684085211860471426056192 }, { argument := 715684085211860471426056192, coefficient := 715684085211860471426056192 }, { argument := 22495691651389019682932523008, coefficient := 22495691651389019682932523008 }, { argument := 715684085211860471426056192, coefficient := 715684085211860471426056192 }, { argument := 909112216350201139379044352, coefficient := 909112216350201139379044352 }, { argument := 928455029464035206174343168, coefficient := 928455029464035206174343168 }, { argument := 79228162514264337593543950336, coefficient := (-79228162514264337593543950336) }, { argument := 79228162514264337593543950336, coefficient := 79228162514264337593543950336 }, { argument := 79228162514264337593543950336, coefficient := (-79228162514264337593543950336) }, { argument := 752667543885511207138667528192, coefficient := 752667543885511207138667528192 }, { argument := 752667543885511207138667528192, coefficient := 752667543885511207138667528192 }, { argument := 1505335087771022414277335056384, coefficient := (-1505335087771022414277335056384) }, { argument := 1460229914325473147940400791552, coefficient := 1460229914325473147940400791552 }, { argument := 5319268090580316376961564803072, coefficient := 5319268090580316376961564803072 }, { argument := 1460230896577701584826605240320, coefficient := 1460230896577701584826605240320 }, { argument := 8239728901483491109728570834944, coefficient := (-8239728901483491109728570834944) }, { argument := 55100369060364256958660739072, coefficient := 55100369060364256958660739072 }, { argument := 2202902531771058888027119026176, coefficient := 2202902531771058888027119026176 }, { argument := 2202901993421279840887564664832, coefficient := 2202901993421279840887564664832 }, { argument := 55100369060364256958660739072, coefficient := 55100369060364256958660739072 }, { argument := 4516005263313067242832005169152, coefficient := (-4516005263313067242832005169152) }, { argument := 392806444045097088875233280, coefficient := 392806444045097088875233280 }, { argument := 64373410947885855695018393600, coefficient := 64373410947885855695018393600 }, { argument := 662749190358781470367652249600, coefficient := 662749190358781470367652249600 }, { argument := 64373410947885855695018393600, coefficient := 64373410947885855695018393600 }, { argument := 392806444045097088875233280, coefficient := 392806444045097088875233280 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 397462697397206559055937536, coefficient := 397462697397206559055937536 }, { argument := 78830699816867131034488012800, coefficient := 78830699816867131034488012800 }, { argument := 78830699816867131034488012800, coefficient := 78830699816867131034488012800 }, { argument := 397462697397206559055937536, coefficient := 397462697397206559055937536 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := Form.normalizePowersOfTwo rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  unfold form
  exact Form.eval_normalizePowersOfTwo bits rawForm

/-- Sign separation retains this bounded shard's exact constant. -/
theorem signedForm_constant : signedForm.constantNumerator = form.constantNumerator := by
  rfl

/-- Sign separation only permutes this bounded shard's exact term list. -/
theorem signedForm_terms_perm : signedForm.terms.Perm form.terms := by
  decide +kernel

/-- Rational lower endpoint contributed by this shard. -/
noncomputable def lower : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveFloor - negativeCeiling

/-- Kernel-checked lower-bound certificate before restoring source term order. -/
noncomputable def signedCertificate : LowerBound bits :=
  LowerBound.ofSignedFamilies bits constantNumerator positiveArgument positiveCoefficient
    negativeArgument negativeCoefficient positiveFloor negativeCeiling
      positiveFloor_le_exact negativeExact_le_ceiling

/-- Kernel-checked lower-bound certificate in the shard's exact source order. -/
noncomputable def certificate : LowerBound bits :=
  LowerBound.reorder signedCertificate form signedForm_constant signedForm_terms_perm

@[simp] theorem certificate_form : certificate.form = form := rfl

@[simp] theorem certificate_lower : certificate.lower = lower := by
  simp [certificate, LowerBound.reorder, signedCertificate, LowerBound.ofSignedFamilies, lower,
    constantNumerator, bits]

end TermShard5


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk0
