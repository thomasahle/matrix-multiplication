import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 13, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk13

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
    129, 257, 995, 1605, 2367, 2739,
    2763, 3193, 4755, 5631, 5691, 7923,
    35901, 36207, 70799, 86107
  ]
def positiveCoefficients : Array ℕ := #[
    18856302678394912347263460179968, 16162545152909924869082965868544, 2306173354465206338672877306380288, 610532220334920985495849681289216, 67502394462153215629699445686272, 476398941198271461949979773370368,
    477349679148442634001102300774400, 610373764009892456820662593388544, 67977763437238801655260709388288, 2178219872004669433459303826587648, 2173149269603756515853317013766144, 2317265297217203345935973459427328,
    1107055114811815589194589618044928, 1105708236049073095455499370889216, 11218549355694801674570636279676928, 3258654324211692205222462677319680
  ]
def positiveScales : Array ℕ := #[
    7, 8, 9, 10, 11, 11,
    11, 11, 12, 12, 12, 12,
    15, 15, 16, 16
  ]
def negativeArguments : Array ℕ := #[
    3, 9, 13, 27, 31, 43,
    47, 53, 63, 119, 147, 155,
    229, 335, 393, 415, 963, 2373,
    3149, 3661, 3853, 4007, 4011, 4361,
    7291, 17339, 27429, 27493, 16006959245189
  ]
def negativeCoefficients : Array ℕ := #[
    4753689750855860255612637020160, 1426106925256758076683791106048, 37078780056675709993778568757248, 4278320775770274230051373318144, 9824292151768777861599449841664, 27254487904906932132179118915584,
    3723723638170423866896565665792, 4199092613256009892457829367808, 9982748476797306536786537742336, 18856302678394912347263460179968, 11646539889596857626250960699392, 12280365189710972326999312302080,
    18143249215766533308921564626944, 26541434442278553093837223362560, 249093342944847077394102179856384, 32879687443419700101320739389440, 610373764009892456820662593388544, 376016859292698546218959588294656,
    249489483757418399082069899608064, 580108605929443479859928804360192, 610532220334920985495849681289216, 317467247194657200737330608996352, 317784159844714258087704784797696, 1382056066898827104981780669661184,
    577652532891501285394528941899776, 1373737109834829349534458554875904, 2173149269603756515853317013766144, 2178219872004669433459303826587648, 5609274677847400837285318139838464
  ]
def negativeScales : Array ℕ := #[
    1, 3, 3, 4, 4, 5,
    5, 5, 5, 6, 7, 7,
    7, 8, 8, 8, 9, 11,
    11, 11, 11, 11, 11, 12,
    12, 14, 14, 14, 43
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7011227255423254, 8005624549193878, 9958552714688244, 10648357582008395, 11208843990734614, 11419433550705376,
    11432019846812489, 11640696837569049, 12215229625747925, 12459175435552025, 12474466464132624, 12951831086224604,
    15131736409529475, 15143981024067942, 16111441362665214, 16393842904683594
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 3169925001442313, 3700439718214233, 4754887502413606, 4954196321574415, 5426264754702117,
    5554588851679165, 5727920454700926, 5977279939904027, 6894817767286876, 7199672344836365, 7276124405274238,
    7839203789504465, 8388017285345139, 8618385502267938, 8696967526301680, 9911391993193157, 11212496385193949,
    11620678042145331, 11838022059680213, 11911766476044779, 11968306808584376, 11969746265308618, 12090443275081607,
    12831900987417584, 14081733075303968, 14743414405454148, 14746776720184861, 43863764508750611
  ]

abbrev PositiveTerm := Fin 16
abbrev NegativeTerm := Fin 29
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
noncomputable def positiveFloor : ℝ := 1207450463953 / 250000000000
noncomputable def negativeCeiling : ℝ := 2360175832509 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-4753689750855860255612637020160) }, { argument := 9, coefficient := (-1426106925256758076683791106048) }, { argument := 13, coefficient := (-37078780056675709993778568757248) }, { argument := 27, coefficient := (-4278320775770274230051373318144) }, { argument := 31, coefficient := (-9824292151768777861599449841664) }, { argument := 43, coefficient := (-27254487904906932132179118915584) }, { argument := 47, coefficient := (-3723723638170423866896565665792) }, { argument := 53, coefficient := (-4199092613256009892457829367808) }, { argument := 63, coefficient := (-9982748476797306536786537742336) }, { argument := 119, coefficient := (-18856302678394912347263460179968) }, { argument := 129, coefficient := 18856302678394912347263460179968 }, { argument := 147, coefficient := (-11646539889596857626250960699392) }, { argument := 155, coefficient := (-12280365189710972326999312302080) }, { argument := 229, coefficient := (-18143249215766533308921564626944) }, { argument := 257, coefficient := 16162545152909924869082965868544 }, { argument := 335, coefficient := (-26541434442278553093837223362560) }, { argument := 393, coefficient := (-249093342944847077394102179856384) }, { argument := 415, coefficient := (-32879687443419700101320739389440) }, { argument := 963, coefficient := (-610373764009892456820662593388544) }, { argument := 995, coefficient := 2306173354465206338672877306380288 }, { argument := 1605, coefficient := 610532220334920985495849681289216 }, { argument := 2367, coefficient := 67502394462153215629699445686272 }, { argument := 2373, coefficient := (-376016859292698546218959588294656) }, { argument := 2739, coefficient := 476398941198271461949979773370368 }, { argument := 2763, coefficient := 477349679148442634001102300774400 }, { argument := 3149, coefficient := (-249489483757418399082069899608064) }, { argument := 3193, coefficient := 610373764009892456820662593388544 }, { argument := 3661, coefficient := (-580108605929443479859928804360192) }, { argument := 3853, coefficient := (-610532220334920985495849681289216) }, { argument := 4007, coefficient := (-317467247194657200737330608996352) }, { argument := 4011, coefficient := (-317784159844714258087704784797696) }, { argument := 4361, coefficient := (-1382056066898827104981780669661184) }, { argument := 4755, coefficient := 67977763437238801655260709388288 }, { argument := 5631, coefficient := 2178219872004669433459303826587648 }, { argument := 5691, coefficient := 2173149269603756515853317013766144 }, { argument := 7291, coefficient := (-577652532891501285394528941899776) }, { argument := 7923, coefficient := 2317265297217203345935973459427328 }, { argument := 17339, coefficient := (-1373737109834829349534458554875904) }, { argument := 27429, coefficient := (-2173149269603756515853317013766144) }, { argument := 27493, coefficient := (-2178219872004669433459303826587648) }, { argument := 35901, coefficient := 1107055114811815589194589618044928 }, { argument := 36207, coefficient := 1105708236049073095455499370889216 }, { argument := 70799, coefficient := 11218549355694801674570636279676928 }, { argument := 86107, coefficient := 3258654324211692205222462677319680 }, { argument := 16006959245189, coefficient := (-5609274677847400837285318139838464) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk13
