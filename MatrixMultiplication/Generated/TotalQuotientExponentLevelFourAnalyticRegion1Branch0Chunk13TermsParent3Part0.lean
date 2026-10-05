import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 13, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    97, 271, 329, 387, 403, 543,
    1323, 1981, 1987, 2017, 6931, 8107,
    50465
  ]
def positiveCoefficients : Array ℕ := #[
    435992578315996649777272358699008, 432823451815426076273530600685568, 110760971194941543955774442569728, 434883384040796949050962743394304, 950737950171172051122527404032, 432506539165369018923156424884224,
    111474024657569922994116338122752, 10141204801825835211973625643008, 10378889289368628224754257494016, 180640210532522689713280206766080, 2196521577545464495443412479115264, 181274035832636804414028558368768,
    714875710366207118106547063881728
  ]
def positiveScales : Array ℕ := #[
    6, 8, 8, 8, 8, 9,
    10, 10, 10, 10, 12, 12,
    15
  ]
def negativeArguments : Array ℕ := #[
    3, 5, 7, 17, 25, 33,
    53, 137, 145, 273, 397, 399,
    573, 699, 1135, 1137, 1407, 1859,
    3713, 5489, 5503, 9835528509
  ]
def negativeCoefficients : Array ℕ := #[
    1901475900342344102245054808064, 792281625142643375935439503360, 5545971375998503631548076523520, 10775030101939949912721977245696, 1980704062856608439838598758400, 2614529362970723140586950361088,
    4199092613256009892457829367808, 43417033057816857001262084784128, 45952334258273315804255491194880, 43258576732788328326074996883456, 62907161036325884049273896566784, 63224073686382941399648072368128,
    45397737120673465441100683542528, 110760971194941543955774442569728, 89923964453690023168672383631360, 90082420778718551843859471532032, 111474024657569922994116338122752, 294570308228034807172796407349248,
    294174167415463485484828687597568, 434883384040796949050962743394304, 435992578315996649777272358699008, 1098260788772732247721706239557632
  ]
def negativeScales : Array ℕ := #[
    1, 2, 2, 4, 4, 5,
    5, 7, 7, 8, 8, 8,
    9, 9, 10, 10, 10, 10,
    11, 12, 12, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6599912842186776, 8082149041353871, 8361943773735241, 8596189756144093, 8654636028526477, 9084808387804361,
    10369597346278676, 10952013164223805, 10956376156533436, 10977995367589168, 12758847803091420, 12984952426585997,
    15622995533105222
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 2321928094887363, 2807354922807594, 4087462841250340, 4643856189792934, 5044394119358454,
    5727920454700926, 7098032082960527, 7179909090014935, 8092757140919853, 8632995197156697, 8640244936238936,
    9162391328756905, 9449148645375482, 10148476582178278, 10151016538892248, 10458406613236597, 10860311057025654,
    11858369601885183, 12422327623974574, 12426002613329380, 33195355431332697
  ]

abbrev PositiveTerm := Fin 13
abbrev NegativeTerm := Fin 22
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
noncomputable def positiveFloor : ℝ := 180221452803 / 250000000000
noncomputable def negativeCeiling : ℝ := 729547911333 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-1901475900342344102245054808064) }, { argument := 5, coefficient := (-792281625142643375935439503360) }, { argument := 7, coefficient := (-5545971375998503631548076523520) }, { argument := 17, coefficient := (-10775030101939949912721977245696) }, { argument := 25, coefficient := (-1980704062856608439838598758400) }, { argument := 33, coefficient := (-2614529362970723140586950361088) }, { argument := 53, coefficient := (-4199092613256009892457829367808) }, { argument := 97, coefficient := 435992578315996649777272358699008 }, { argument := 137, coefficient := (-43417033057816857001262084784128) }, { argument := 145, coefficient := (-45952334258273315804255491194880) }, { argument := 271, coefficient := 432823451815426076273530600685568 }, { argument := 273, coefficient := (-43258576732788328326074996883456) }, { argument := 329, coefficient := 110760971194941543955774442569728 }, { argument := 387, coefficient := 434883384040796949050962743394304 }, { argument := 397, coefficient := (-62907161036325884049273896566784) }, { argument := 399, coefficient := (-63224073686382941399648072368128) }, { argument := 403, coefficient := 950737950171172051122527404032 }, { argument := 543, coefficient := 432506539165369018923156424884224 }, { argument := 573, coefficient := (-45397737120673465441100683542528) }, { argument := 699, coefficient := (-110760971194941543955774442569728) }, { argument := 1135, coefficient := (-89923964453690023168672383631360) }, { argument := 1137, coefficient := (-90082420778718551843859471532032) }, { argument := 1323, coefficient := 111474024657569922994116338122752 }, { argument := 1407, coefficient := (-111474024657569922994116338122752) }, { argument := 1859, coefficient := (-294570308228034807172796407349248) }, { argument := 1981, coefficient := 10141204801825835211973625643008 }, { argument := 1987, coefficient := 10378889289368628224754257494016 }, { argument := 2017, coefficient := 180640210532522689713280206766080 }, { argument := 3713, coefficient := (-294174167415463485484828687597568) }, { argument := 5489, coefficient := (-434883384040796949050962743394304) }, { argument := 5503, coefficient := (-435992578315996649777272358699008) }, { argument := 6931, coefficient := 2196521577545464495443412479115264 }, { argument := 8107, coefficient := 181274035832636804414028558368768 }, { argument := 50465, coefficient := 714875710366207118106547063881728 }, { argument := 9835528509, coefficient := (-1098260788772732247721706239557632) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk13
