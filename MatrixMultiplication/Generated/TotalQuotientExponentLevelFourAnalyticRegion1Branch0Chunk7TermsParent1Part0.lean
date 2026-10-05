import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 7, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk7

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    31, 187, 375, 497, 1021, 1221,
    2041, 2181, 2435, 3743, 7177, 7493,
    17407, 22615
  ]
def positiveCoefficients : Array ℕ := #[
    442013918667080739434381698924544, 396140812571321687967719751680, 475368975085586025561263702016, 441776234179537946421601067073536, 11408855402054064613470328848384, 86121012653005334964182274015232,
    11408855402054064613470328848384, 212806844513314010776259050602496, 85804100002948277613808098213888, 480439577486498943167250514837504, 2274482089459500603635459726245888, 480281121161470414492063426936832,
    212410703700742689088291330850816, 688334275923928565012709840519168
  ]
def positiveScales : Array ℕ := #[
    4, 7, 8, 8, 9, 10,
    10, 11, 11, 11, 12, 12,
    14, 14
  ]
def negativeArguments : Array ℕ := #[
    5, 7, 21, 23, 25, 55,
    83, 109, 147, 439, 587, 697,
    901, 1321, 1323, 1599, 1877, 3759,
    5579, 323828727115
  ]
def negativeCoefficients : Array ℕ := #[
    1188422437713965063903159255040, 4436777100798802905238461218816, 6655165651198204357857691828224, 3644495475656159529303021715456, 126765060022822940149670320537600, 4357548938284538567644917268480,
    6575937488683940020264147877888, 34543478856219251190785162346496, 46586159558387430505003842797568, 34781163343762044203565794197504, 46506931395873166167410298847232, 441776234179537946421601067073536,
    142769148850704336343566198505472, 104660402681343189961071558393856, 104818859006371718636258646294528, 126685831860308675812076776587264, 297422522078548323326163989561344, 297818662891119645014131709313024,
    442013918667080739434381698924544, 1137241044729750301817729863122944
  ]
def negativeScales : Array ℕ := #[
    2, 2, 4, 4, 4, 5,
    6, 6, 7, 8, 9, 9,
    9, 10, 10, 10, 10, 11,
    12, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    4954196309696329, 7546894459887560, 8550746785383158, 8957102040837303, 9995767149513532, 10253847484987402,
    10995060465683787, 11090774054640750, 11249706056969704, 11869979332743826, 12809165205323695, 12871327735973913,
    14087379963465402, 14464992375518768
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2321928094887363, 2807354922807594, 4392317422778766, 4523561956057598, 4643856189792934, 5781359713964302,
    6375039431346928, 6768184325109843, 7199672344836365, 8778077129945769, 9197216693110053, 9445014845868462,
    9815383296694715, 10367414751246830, 10369597346278679, 10642954223498123, 10874212937561327, 11876133202872147,
    12445790836048116, 38236440017752326
  ]

abbrev PositiveTerm := Fin 14
abbrev NegativeTerm := Fin 20
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
noncomputable def positiveFloor : ℝ := 777231541511 / 1000000000000
noncomputable def negativeCeiling : ℝ := 402456892329 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5, coefficient := (-1188422437713965063903159255040) }, { argument := 7, coefficient := (-4436777100798802905238461218816) }, { argument := 21, coefficient := (-6655165651198204357857691828224) }, { argument := 23, coefficient := (-3644495475656159529303021715456) }, { argument := 25, coefficient := (-126765060022822940149670320537600) }, { argument := 31, coefficient := 442013918667080739434381698924544 }, { argument := 55, coefficient := (-4357548938284538567644917268480) }, { argument := 83, coefficient := (-6575937488683940020264147877888) }, { argument := 109, coefficient := (-34543478856219251190785162346496) }, { argument := 147, coefficient := (-46586159558387430505003842797568) }, { argument := 187, coefficient := 396140812571321687967719751680 }, { argument := 375, coefficient := 475368975085586025561263702016 }, { argument := 439, coefficient := (-34781163343762044203565794197504) }, { argument := 497, coefficient := 441776234179537946421601067073536 }, { argument := 587, coefficient := (-46506931395873166167410298847232) }, { argument := 697, coefficient := (-441776234179537946421601067073536) }, { argument := 901, coefficient := (-142769148850704336343566198505472) }, { argument := 1021, coefficient := 11408855402054064613470328848384 }, { argument := 1221, coefficient := 86121012653005334964182274015232 }, { argument := 1321, coefficient := (-104660402681343189961071558393856) }, { argument := 1323, coefficient := (-104818859006371718636258646294528) }, { argument := 1599, coefficient := (-126685831860308675812076776587264) }, { argument := 1877, coefficient := (-297422522078548323326163989561344) }, { argument := 2041, coefficient := 11408855402054064613470328848384 }, { argument := 2181, coefficient := 212806844513314010776259050602496 }, { argument := 2435, coefficient := 85804100002948277613808098213888 }, { argument := 3743, coefficient := 480439577486498943167250514837504 }, { argument := 3759, coefficient := (-297818662891119645014131709313024) }, { argument := 5579, coefficient := (-442013918667080739434381698924544) }, { argument := 7177, coefficient := 2274482089459500603635459726245888 }, { argument := 7493, coefficient := 480281121161470414492063426936832 }, { argument := 17407, coefficient := 212410703700742689088291330850816 }, { argument := 22615, coefficient := 688334275923928565012709840519168 }, { argument := 323828727115, coefficient := (-1137241044729750301817729863122944) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk7
