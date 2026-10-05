import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 2, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk2

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
def constantNumerator : ℤ := 250852266324760812226665775104
def positiveArguments : Array ℕ := #[
    1, 34571, 1180201, 14346067, 2360431, 72323,
    355035, 16422859, 8209639, 89315
  ]
def positiveCoefficients : Array ℕ := #[
    316912650057057350374175801344, 653027726717146018730737664, 22293366581796952603396931584, 270989543847209130007648534528, 22293640479052959042819325952, 683071422281162701580271616,
    3353210768491248976889118720, 155109517788988197449108553728, 155075696200237885050088062976, 3374225299340018898090065920
  ]
def positiveScales : Array ℕ := #[
    0, 15, 20, 23, 21, 16,
    18, 23, 22, 16
  ]
def negativeArguments : Array ℕ := #[
    12278738395, 567750246615, 283813455421, 3088593205, 418947838075, 19382333907803,
    9689050692927, 105397767275, 12278738395, 418947838075, 5093462746725, 418952873425,
    3214171485, 5093462746725, 235603337812621, 117775987401349, 1281338564225, 567750246615,
    19382333907803, 235603337812621, 605705379447, 593858671201, 418952873425, 605705379447,
    19378339557617, 210798083375, 283813455421, 9689050692927, 117775987401349, 19378339557617,
    593730913037, 3214171485, 593858671201, 593730913037, 6466161295, 3088593205,
    105397767275, 1281338564225, 210798083375, 6466161295, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    3456157603768862632837120, 159807487443426325498429440, 159772771509593559743332352, 3477446801784261490769920, 117923332965140306015027200, 5455641985297007523311648768,
    5454450636279985407969460224, 118667336356343064402329600, 3456157603768862632837120, 117923332965140306015027200, 1433682308011013315336601600, 117924750290164286016716800,
    3618835375537718443376640, 1433682308011013315336601600, 66316444023760314108661989376, 66301986621738448490634149888, 1442658970094789089191526400, 159807487443426325498429440,
    5455641985297007523311648768, 66316444023760314108661989376, 5455709042347628173065191424, 167156355645722594017017856, 117924750290164286016716800, 5455709042347628173065191424,
    5454517675671428968849866752, 118668771217258093477888000, 159772771509593559743332352, 5454450636279985407969460224, 66301986621738448490634149888, 5454517675671428968849866752,
    167120394919486097847222272, 3618835375537718443376640, 167156355645722594017017856, 167120394919486097847222272, 3640125199834940482519040, 3477446801784261490769920,
    118667336356343064402329600, 1442658970094789089191526400, 118668771217258093477888000, 3640125199834940482519040, 316912650057057350374175801344, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    33, 39, 38, 31, 38, 44,
    43, 36, 33, 38, 42, 38,
    31, 42, 47, 46, 40, 39,
    44, 47, 39, 39, 38, 39,
    44, 37, 38, 43, 46, 44,
    39, 31, 39, 39, 32, 31,
    36, 40, 37, 32, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 15077274715118953, 20170601155189619, 23774151937861913, 21170618880093757, 16142166902371074,
    18437601729582122, 23969201966206902, 22968887352642833, 16446614868538854
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    33515443284437260, 39046465471360098, 38046152032063557, 31524302721787576, 38607979673288992, 44139807535686064,
    43139492459841106, 36617053349308656, 33515443284437260, 38607979673288992, 42211783932278498, 38607997012991360,
    31581799756854311, 42211783932278498, 47743353306714503, 46743038755829361, 40220788863658572, 39046465471360098,
    44139807535686064, 47743353306714503, 39139825268205922, 39111328677451482, 38607997012991360, 39139825268205922,
    44139510191563266, 37617070793487278, 38046152032063557, 43139492459841106, 46743038755829361, 44139510191563266,
    39111018273802286, 31581799756854311, 39111328677451482, 39111018273802286, 32590262349174073, 31524302721787576,
    36617053349308656, 40220788863658572, 37617070793487278, 32590262349174073, 0, 0
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
noncomputable def positiveFloor : ℝ := 177933619 / 1000000000000
noncomputable def negativeCeiling : ℝ := 177138447 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3456157603768862632837120, coefficient := (-3456157603768862632837120) }, { argument := 159807487443426325498429440, coefficient := (-159807487443426325498429440) }, { argument := 159772771509593559743332352, coefficient := (-159772771509593559743332352) }, { argument := 3477446801784261490769920, coefficient := (-3477446801784261490769920) }, { argument := 117923332965140306015027200, coefficient := (-117923332965140306015027200) }, { argument := 5455641985297007523311648768, coefficient := (-5455641985297007523311648768) }, { argument := 5454450636279985407969460224, coefficient := (-5454450636279985407969460224) }, { argument := 118667336356343064402329600, coefficient := (-118667336356343064402329600) }, { argument := 3456157603768862632837120, coefficient := (-3456157603768862632837120) }, { argument := 117923332965140306015027200, coefficient := (-117923332965140306015027200) }, { argument := 1433682308011013315336601600, coefficient := (-1433682308011013315336601600) }, { argument := 117924750290164286016716800, coefficient := (-117924750290164286016716800) }, { argument := 3618835375537718443376640, coefficient := (-3618835375537718443376640) }, { argument := 1433682308011013315336601600, coefficient := (-1433682308011013315336601600) }, { argument := 66316444023760314108661989376, coefficient := (-66316444023760314108661989376) }, { argument := 66301986621738448490634149888, coefficient := (-66301986621738448490634149888) }, { argument := 1442658970094789089191526400, coefficient := (-1442658970094789089191526400) }, { argument := 159807487443426325498429440, coefficient := (-159807487443426325498429440) }, { argument := 5455641985297007523311648768, coefficient := (-5455641985297007523311648768) }, { argument := 66316444023760314108661989376, coefficient := (-66316444023760314108661989376) }, { argument := 5455709042347628173065191424, coefficient := (-5455709042347628173065191424) }, { argument := 167156355645722594017017856, coefficient := (-167156355645722594017017856) }, { argument := 117924750290164286016716800, coefficient := (-117924750290164286016716800) }, { argument := 5455709042347628173065191424, coefficient := (-5455709042347628173065191424) }, { argument := 5454517675671428968849866752, coefficient := (-5454517675671428968849866752) }, { argument := 118668771217258093477888000, coefficient := (-118668771217258093477888000) }, { argument := 159772771509593559743332352, coefficient := (-159772771509593559743332352) }, { argument := 5454450636279985407969460224, coefficient := (-5454450636279985407969460224) }, { argument := 66301986621738448490634149888, coefficient := (-66301986621738448490634149888) }, { argument := 5454517675671428968849866752, coefficient := (-5454517675671428968849866752) }, { argument := 167120394919486097847222272, coefficient := (-167120394919486097847222272) }, { argument := 3618835375537718443376640, coefficient := (-3618835375537718443376640) }, { argument := 167156355645722594017017856, coefficient := (-167156355645722594017017856) }, { argument := 167120394919486097847222272, coefficient := (-167120394919486097847222272) }, { argument := 3640125199834940482519040, coefficient := (-3640125199834940482519040) }, { argument := 3477446801784261490769920, coefficient := (-3477446801784261490769920) }, { argument := 118667336356343064402329600, coefficient := (-118667336356343064402329600) }, { argument := 1442658970094789089191526400, coefficient := (-1442658970094789089191526400) }, { argument := 118668771217258093477888000, coefficient := (-118668771217258093477888000) }, { argument := 3640125199834940482519040, coefficient := (-3640125199834940482519040) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 653027726717146018730737664, coefficient := 653027726717146018730737664 }, { argument := 22293366581796952603396931584, coefficient := 22293366581796952603396931584 }, { argument := 270989543847209130007648534528, coefficient := 270989543847209130007648534528 }, { argument := 22293640479052959042819325952, coefficient := 22293640479052959042819325952 }, { argument := 683071422281162701580271616, coefficient := 683071422281162701580271616 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 3353210768491248976889118720, coefficient := 3353210768491248976889118720 }, { argument := 155109517788988197449108553728, coefficient := 155109517788988197449108553728 }, { argument := 155075696200237885050088062976, coefficient := 155075696200237885050088062976 }, { argument := 3374225299340018898090065920, coefficient := 3374225299340018898090065920 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk2
