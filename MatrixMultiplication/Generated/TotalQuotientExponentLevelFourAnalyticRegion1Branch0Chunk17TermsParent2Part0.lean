import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 17, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk17

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    17, 231, 257, 463, 671, 933,
    1087, 2201, 2687, 3745, 5041, 17595,
    109761, 110175
  ]
def positiveCoefficients : Array ℕ := #[
    6100568513598353994702884175872, 1678686307352232784932009219719168, 86358697140548127976962905866240, 672488643421075697494001050451968, 273257932511697700360133084708864, 1988230738295463551909985433681920,
    6021340351084089657109340225536, 260026829371815555982011245002752, 273178704349183436022539540758528, 1314078303461588303326519960272896, 6390226675750504412944880858300416, 260185285696844084657198332903424,
    1332142324514840572297847980949504, 1330320076777012492533196470091776
  ]
def positiveScales : Array ℕ := #[
    4, 7, 8, 8, 9, 9,
    10, 11, 11, 11, 12, 14,
    16, 16
  ]
def negativeArguments : Array ℕ := #[
    7, 13, 15, 19, 27, 31,
    39, 57, 77, 401, 453, 541,
    545, 549, 821, 937, 1081, 1227,
    1597, 1641, 1871, 2463, 4753, 8407,
    9505, 16791, 6294676066859
  ]
def negativeCoefficients : Array ℕ := #[
    1109194275199700726309615304704, 4119864450741745554864285417472, 2376844875427930127806318510080, 6021340351084089657109340225536, 12834962327310822690154119954432, 2456073037942194465399862460416,
    6179796676112618332296428126208, 36128042106504537942656041353216, 6100568513598353994702884175872, 127081972672879997500044496338944, 35890357618961744929875409502208, 85724871840434013276214554263552,
    43179348570274063988481452933120, 43496261220331121338855628734464, 260185285696844084657198332903424, 148473576551731368650301362929664, 85645643677919748938621010313216, 388851821620009368909113708249088,
    126527375535280147136889688686592, 260026829371815555982011245002752, 148235892064188575637520731078656, 390277928545266126985797499355136, 753142912860596793164228791894016, 1332142324514840572297847980949504,
    753063684698082528826635247943680, 1330320076777012492533196470091776, 3195113337875252206472440429150208
  ]
def negativeScales : Array ℕ := #[
    2, 3, 3, 4, 4, 4,
    5, 5, 6, 8, 8, 9,
    9, 9, 9, 9, 10, 10,
    10, 10, 10, 11, 12, 13,
    13, 14, 42
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    4087462841250339, 7851749041305231, 8005624549193878, 8854868383142649, 9390168956200182, 9865733270707501,
    10086136225027309, 11103943429891557, 11391780606013165, 11870750003187727, 12299494239009363, 14102877893637026,
    16744006005075539, 16749437371038382
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2807354922807594, 3700439718214233, 3906890600547867, 4247927513443586, 4754887502413606, 4954196321574415,
    5285402218862249, 5832890015409720, 6266786540694902, 8647458426474890, 8823367241078867, 9079484783826816,
    9090112419664289, 9100662339005199, 9681238411824066, 9871905240275299, 10078150807734651, 10260919533662906,
    10641148597428215, 10680359523558999, 10869593845746860, 11266200912498962, 12214622686302336, 13037375357763239,
    13214470911535915, 14035400533116809, 42517269275328495
  ]

abbrev PositiveTerm := Fin 14
abbrev NegativeTerm := Fin 27
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
noncomputable def positiveFloor : ℝ := 458721790707 / 200000000000
noncomputable def negativeCeiling : ℝ := 642169127589 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7, coefficient := (-1109194275199700726309615304704) }, { argument := 13, coefficient := (-4119864450741745554864285417472) }, { argument := 15, coefficient := (-2376844875427930127806318510080) }, { argument := 17, coefficient := 6100568513598353994702884175872 }, { argument := 19, coefficient := (-6021340351084089657109340225536) }, { argument := 27, coefficient := (-12834962327310822690154119954432) }, { argument := 31, coefficient := (-2456073037942194465399862460416) }, { argument := 39, coefficient := (-6179796676112618332296428126208) }, { argument := 57, coefficient := (-36128042106504537942656041353216) }, { argument := 77, coefficient := (-6100568513598353994702884175872) }, { argument := 231, coefficient := 1678686307352232784932009219719168 }, { argument := 257, coefficient := 86358697140548127976962905866240 }, { argument := 401, coefficient := (-127081972672879997500044496338944) }, { argument := 453, coefficient := (-35890357618961744929875409502208) }, { argument := 463, coefficient := 672488643421075697494001050451968 }, { argument := 541, coefficient := (-85724871840434013276214554263552) }, { argument := 545, coefficient := (-43179348570274063988481452933120) }, { argument := 549, coefficient := (-43496261220331121338855628734464) }, { argument := 671, coefficient := 273257932511697700360133084708864 }, { argument := 821, coefficient := (-260185285696844084657198332903424) }, { argument := 933, coefficient := 1988230738295463551909985433681920 }, { argument := 937, coefficient := (-148473576551731368650301362929664) }, { argument := 1081, coefficient := (-85645643677919748938621010313216) }, { argument := 1087, coefficient := 6021340351084089657109340225536 }, { argument := 1227, coefficient := (-388851821620009368909113708249088) }, { argument := 1597, coefficient := (-126527375535280147136889688686592) }, { argument := 1641, coefficient := (-260026829371815555982011245002752) }, { argument := 1871, coefficient := (-148235892064188575637520731078656) }, { argument := 2201, coefficient := 260026829371815555982011245002752 }, { argument := 2463, coefficient := (-390277928545266126985797499355136) }, { argument := 2687, coefficient := 273178704349183436022539540758528 }, { argument := 3745, coefficient := 1314078303461588303326519960272896 }, { argument := 4753, coefficient := (-753142912860596793164228791894016) }, { argument := 5041, coefficient := 6390226675750504412944880858300416 }, { argument := 8407, coefficient := (-1332142324514840572297847980949504) }, { argument := 9505, coefficient := (-753063684698082528826635247943680) }, { argument := 16791, coefficient := (-1330320076777012492533196470091776) }, { argument := 17595, coefficient := 260185285696844084657198332903424 }, { argument := 109761, coefficient := 1332142324514840572297847980949504 }, { argument := 110175, coefficient := 1330320076777012492533196470091776 }, { argument := 6294676066859, coefficient := (-3195113337875252206472440429150208) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  rfl

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

end TermShard0


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk17
