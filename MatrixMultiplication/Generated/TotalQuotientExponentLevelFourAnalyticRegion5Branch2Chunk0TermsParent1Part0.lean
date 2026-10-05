import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 0, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk0

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
def constantNumerator : ℤ := 158456325028528675187087900672
def positiveArguments : Array ℕ := #[
    1, 42415, 8218963, 8218905, 21211, 46973,
    1348989, 13985335, 674463, 46993
  ]
def positiveCoefficients : Array ℕ := #[
    158456325028528675187087900672, 1602393394967328013911326720, 77625910790291495668989034496, 77625362995779482790144245760, 1602657847490368714043293696, 443647441599671689245884416,
    12740840878719679654357106688, 132087754511407499289370296320, 12740245860542838079060180992, 443836336258986475054432256
  ]
def positiveScales : Array ℕ := #[
    0, 15, 22, 22, 14, 15,
    20, 23, 19, 15
  ]
def negativeArguments : Array ℕ := #[
    1992359795, 57217368435, 593187984025, 28607348145, 1993208095, 1992359795,
    386069348999, 386066624565, 996344303, 386069348999, 11087290678407, 114944950907605,
    5543386441869, 386233728259, 57217368435, 11087290678407, 11087212437045, 28613405679,
    386066624565, 11087212437045, 114944139758175, 5543347323015, 386231002665, 593187984025,
    114944950907605, 114944139758175, 296642940685, 996344303, 28613405679, 296642940685,
    14306034693, 996768523, 28607348145, 5543386441869, 5543347323015, 14306034693,
    1993208095, 386233728259, 386231002665, 996768523, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    2243197707587489449902080, 64421029790746594970173440, 667870295953911433501081600, 64418021222940024986664960, 2244152808478464047841280, 2243197707587489449902080,
    108668861018191648306233344, 108668094158194948586864640, 2243567915861758279942144, 108668861018191648306233344, 3120794885488883687586004992, 32354127379725614624674938880,
    3120649139246486010753712128, 108715129666571863173627904, 64421029790746594970173440, 3120794885488883687586004992, 3120772862503336927580651520, 64431661576872617041723392,
    108668094158194948586864640, 3120772862503336927580651520, 32353899061458696512785612800, 3120627117289448815649095680, 108714362480064190469898240, 667870295953911433501081600,
    32354127379725614624674938880, 32353899061458696512785612800, 667980518565527073723514880, 2243567915861758279942144, 64431661576872617041723392, 667980518565527073723514880,
    64428652512544188140617728, 2244523174378719835848704, 64418021222940024986664960, 3120649139246486010753712128, 3120627117289448815649095680, 64428652512544188140617728,
    2244152808478464047841280, 108715129666571863173627904, 108714362480064190469898240, 2244523174378719835848704, 158456325028528675187087900672, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    30, 35, 39, 34, 30, 30,
    38, 38, 29, 38, 43, 46,
    42, 38, 35, 43, 43, 34,
    38, 43, 46, 42, 38, 39,
    46, 46, 38, 29, 34, 38,
    33, 29, 34, 42, 42, 33,
    30, 38, 38, 29, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 15372286941474961, 22970524946615526, 22970514765695333, 14372525018382658, 15519544115936472,
    20363447153555385, 23737411476259634, 19363379775756165, 15520158250863009
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    30891831061181285, 35735734095194466, 39109698417745167, 34735666717394998, 30892445196149966, 30891831061181285,
    38490069063458035, 38490058882537690, 29892069138105268, 38490069063458035, 43333972101076723, 46707936423878689,
    42333904723277502, 38490683198384576, 35735734095194466, 43333972101076723, 43333961920156378, 34735972172103037,
    38490058882537690, 43333961920156378, 46707926242958323, 42333894542357157, 38490673017464231, 39109698417745167,
    46707936423878689, 46707926242958323, 38109936494652864, 29892069138105268, 34735972172103037, 38109936494652864,
    33735904794303568, 29892683273074118, 34735666717394998, 42333904723277502, 42333894542357157, 33735904794303568,
    30892445196149966, 38490683198384576, 38490673017464231, 29892683273074118, 0, 0
  ]

abbrev PositiveTerm := Fin 10
abbrev NegativeTerm := Fin 42
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
noncomputable def positiveFloor : ℝ := 43749941 / 500000000000
noncomputable def negativeCeiling : ℝ := 87499883 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2243197707587489449902080, coefficient := (-2243197707587489449902080) }, { argument := 64421029790746594970173440, coefficient := (-64421029790746594970173440) }, { argument := 667870295953911433501081600, coefficient := (-667870295953911433501081600) }, { argument := 64418021222940024986664960, coefficient := (-64418021222940024986664960) }, { argument := 2244152808478464047841280, coefficient := (-2244152808478464047841280) }, { argument := 2243197707587489449902080, coefficient := (-2243197707587489449902080) }, { argument := 108668861018191648306233344, coefficient := (-108668861018191648306233344) }, { argument := 108668094158194948586864640, coefficient := (-108668094158194948586864640) }, { argument := 2243567915861758279942144, coefficient := (-2243567915861758279942144) }, { argument := 108668861018191648306233344, coefficient := (-108668861018191648306233344) }, { argument := 3120794885488883687586004992, coefficient := (-3120794885488883687586004992) }, { argument := 32354127379725614624674938880, coefficient := (-32354127379725614624674938880) }, { argument := 3120649139246486010753712128, coefficient := (-3120649139246486010753712128) }, { argument := 108715129666571863173627904, coefficient := (-108715129666571863173627904) }, { argument := 64421029790746594970173440, coefficient := (-64421029790746594970173440) }, { argument := 3120794885488883687586004992, coefficient := (-3120794885488883687586004992) }, { argument := 3120772862503336927580651520, coefficient := (-3120772862503336927580651520) }, { argument := 64431661576872617041723392, coefficient := (-64431661576872617041723392) }, { argument := 108668094158194948586864640, coefficient := (-108668094158194948586864640) }, { argument := 3120772862503336927580651520, coefficient := (-3120772862503336927580651520) }, { argument := 32353899061458696512785612800, coefficient := (-32353899061458696512785612800) }, { argument := 3120627117289448815649095680, coefficient := (-3120627117289448815649095680) }, { argument := 108714362480064190469898240, coefficient := (-108714362480064190469898240) }, { argument := 667870295953911433501081600, coefficient := (-667870295953911433501081600) }, { argument := 32354127379725614624674938880, coefficient := (-32354127379725614624674938880) }, { argument := 32353899061458696512785612800, coefficient := (-32353899061458696512785612800) }, { argument := 667980518565527073723514880, coefficient := (-667980518565527073723514880) }, { argument := 2243567915861758279942144, coefficient := (-2243567915861758279942144) }, { argument := 64431661576872617041723392, coefficient := (-64431661576872617041723392) }, { argument := 667980518565527073723514880, coefficient := (-667980518565527073723514880) }, { argument := 64428652512544188140617728, coefficient := (-64428652512544188140617728) }, { argument := 2244523174378719835848704, coefficient := (-2244523174378719835848704) }, { argument := 64418021222940024986664960, coefficient := (-64418021222940024986664960) }, { argument := 3120649139246486010753712128, coefficient := (-3120649139246486010753712128) }, { argument := 3120627117289448815649095680, coefficient := (-3120627117289448815649095680) }, { argument := 64428652512544188140617728, coefficient := (-64428652512544188140617728) }, { argument := 2244152808478464047841280, coefficient := (-2244152808478464047841280) }, { argument := 108715129666571863173627904, coefficient := (-108715129666571863173627904) }, { argument := 108714362480064190469898240, coefficient := (-108714362480064190469898240) }, { argument := 2244523174378719835848704, coefficient := (-2244523174378719835848704) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 1602393394967328013911326720, coefficient := 1602393394967328013911326720 }, { argument := 77625910790291495668989034496, coefficient := 77625910790291495668989034496 }, { argument := 77625362995779482790144245760, coefficient := 77625362995779482790144245760 }, { argument := 1602657847490368714043293696, coefficient := 1602657847490368714043293696 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 443647441599671689245884416, coefficient := 443647441599671689245884416 }, { argument := 12740840878719679654357106688, coefficient := 12740840878719679654357106688 }, { argument := 132087754511407499289370296320, coefficient := 132087754511407499289370296320 }, { argument := 12740245860542838079060180992, coefficient := 12740245860542838079060180992 }, { argument := 443836336258986475054432256, coefficient := 443836336258986475054432256 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end TermShard0


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk0
