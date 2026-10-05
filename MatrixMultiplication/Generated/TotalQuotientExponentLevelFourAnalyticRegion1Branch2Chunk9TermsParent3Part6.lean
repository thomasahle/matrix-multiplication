import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 6, for level-four region 1, branch 2,
parent chunk 9, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard12

/-! Directed signed-log shard 12.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-12092933840946287091612467857457152)
def positiveArguments : Array ℕ := #[
    11375, 11375, 375, 12582915, 12582909, 7608333,
    13363187, 7608333, 21912173, 810657171, 1621253619, 43885069,
    7588295, 540231641, 2788348775, 540231705, 7588025, 70300699,
    5529794533, 4375, 3875, 181375, 49375, 2764897275,
    181375, 4375, 4375, 1875, 4375, 49375,
    1875, 35150341, 3875, 288968823, 7515, 1473073033,
    12105, 375, 12105, 8085, 289214583, 7515,
    45, 535, 489, 535, 489
  ]
def positiveCoefficients : Array ℕ := #[
    440048998339725019593048064000, 440048998339725019593048064000, 14507109835375550096474112000, 237684544211190807216374415360, 237684430874395218344889286656, 574869387995376902042485260288,
    2019387724579819699656787492864, 574869387995376902042485260288, 413909245368164809484514885632, 15312881013713306202833959256064, 15312307501193427615901336731648, 414482757888043396417137410048,
    143338839880509257707453153280, 20409374355552534583062286041088, 210681676761770139460701677158400, 20409376773404173812320635453440, 143333739724707758490622361600, 1327942658719630337619332694016,
    104454865439180009017383030095872, 84624807373024042229432320000, 74953400816107008831782912000, 3508302728521653864997322752000, 955051397495557048017879040000, 104454865760300929852518904627200,
    3508302728521653864997322752000, 84624807373024042229432320000, 84624807373024042229432320000, 72535549176877750482370560000, 84624807373024042229432320000, 955051397495557048017879040000,
    72535549176877750482370560000, 1327942337598709502483458162688, 74953400816107008831782912000, 1364616684329491039829316599808, 581444962201852047866682408960, 13912781435716661637146199719936,
    936579010971845514228368670720, 29014219670751100192948224000, 936579010971845514228368670720, 625546576101393720159963709440, 1365777253116321083837034528768, 581444962201852047866682408960,
    27853650883921056185230295040, 331148960508839223535515729920, 302676339605275477212835872768, 331148960508839223535515729920, 302676339605275477212835872768
  ]
def positiveScales : Array ℕ := #[
    13, 13, 8, 23, 23, 22,
    23, 22, 24, 29, 30, 25,
    22, 29, 31, 29, 22, 26,
    32, 12, 11, 17, 15, 31,
    17, 12, 12, 10, 12, 15,
    10, 25, 11, 28, 12, 30,
    13, 8, 13, 12, 28, 12,
    5, 9, 8, 9, 8
  ]
def negativeArguments : Array ℕ := #[
    125, 3, 5, 397, 1589, 2791,
    257, 1
  ]
def negativeCoefficients : Array ℕ := #[
    9903520314283042199192993792000, 475368975085586025561263702016, 3169126500570573503741758013440, 31453580518162942024636948283392, 251787100470332064872282674167808, 221125801577311766223581165387776,
    20361637766165934761540795236352, 1267650600228229401496703205376
  ]
def negativeScales : Array ℕ := #[
    6, 1, 2, 8, 10, 11,
    8, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13473578924860776, 13473578924860776, 8550746785383158, 23584962844686185, 23584962156755582, 22859148960365591,
    23671760782857784, 22859148960365591, 24385229225713248, 29594516683076592, 30594462648883921, 25387226839879627,
    22855344334771504, 29009002899088258, 31376763883087932, 29009003070001011, 22855293001159639, 26067035698300528,
    32364578730155292, 12095067301607053, 11919980594664560, 17468616088728825, 15591493127726274, 31364578734590505,
    17468616088728825, 12095067301607053, 12095067301607053, 10872674880106463, 12095067301607053, 15591493127726274,
    10872674880106463, 25067035349430332, 11919980594664560, 28106338607085747, 12875557388630600, 30456181813032772,
    13563315458886175, 8550746785383158, 13563315458886175, 12981032057285308, 28107565057900220, 12875557388630600,
    5491853096329661, 9063395081288509, 8933690654464738, 9063395081288509, 8933690654464738
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    6965784298236803, 1584962500724866, 2321928094887363, 8632995197156697, 10633903409362589, 11446566409066109,
    8005624549193879, 0
  ]

abbrev PositiveTerm := Fin 47
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
noncomputable def positiveFloor : ℝ := 24504500121 / 125000000000
noncomputable def negativeCeiling : ℝ := 68855062887 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 440048998339725019593048064000, coefficient := 440048998339725019593048064000 }, { argument := 440048998339725019593048064000, coefficient := 440048998339725019593048064000 }, { argument := 14507109835375550096474112000, coefficient := 14507109835375550096474112000 }, { argument := 9903520314283042199192993792000, coefficient := (-9903520314283042199192993792000) }, { argument := 237684544211190807216374415360, coefficient := 237684544211190807216374415360 }, { argument := 237684430874395218344889286656, coefficient := 237684430874395218344889286656 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 574869387995376902042485260288, coefficient := 574869387995376902042485260288 }, { argument := 2019387724579819699656787492864, coefficient := 2019387724579819699656787492864 }, { argument := 574869387995376902042485260288, coefficient := 574869387995376902042485260288 }, { argument := 3169126500570573503741758013440, coefficient := (-3169126500570573503741758013440) }, { argument := 413909245368164809484514885632, coefficient := 413909245368164809484514885632 }, { argument := 15312881013713306202833959256064, coefficient := 15312881013713306202833959256064 }, { argument := 15312307501193427615901336731648, coefficient := 15312307501193427615901336731648 }, { argument := 414482757888043396417137410048, coefficient := 414482757888043396417137410048 }, { argument := 31453580518162942024636948283392, coefficient := (-31453580518162942024636948283392) }, { argument := 143338839880509257707453153280, coefficient := 143338839880509257707453153280 }, { argument := 20409374355552534583062286041088, coefficient := 20409374355552534583062286041088 }, { argument := 210681676761770139460701677158400, coefficient := 210681676761770139460701677158400 }, { argument := 20409376773404173812320635453440, coefficient := 20409376773404173812320635453440 }, { argument := 143333739724707758490622361600, coefficient := 143333739724707758490622361600 }, { argument := 251787100470332064872282674167808, coefficient := (-251787100470332064872282674167808) }, { argument := 1327942658719630337619332694016, coefficient := 1327942658719630337619332694016 }, { argument := 104454865439180009017383030095872, coefficient := 104454865439180009017383030095872 }, { argument := 84624807373024042229432320000, coefficient := 84624807373024042229432320000 }, { argument := 74953400816107008831782912000, coefficient := 74953400816107008831782912000 }, { argument := 3508302728521653864997322752000, coefficient := 3508302728521653864997322752000 }, { argument := 955051397495557048017879040000, coefficient := 955051397495557048017879040000 }, { argument := 104454865760300929852518904627200, coefficient := 104454865760300929852518904627200 }, { argument := 3508302728521653864997322752000, coefficient := 3508302728521653864997322752000 }, { argument := 84624807373024042229432320000, coefficient := 84624807373024042229432320000 }, { argument := 84624807373024042229432320000, coefficient := 84624807373024042229432320000 }, { argument := 72535549176877750482370560000, coefficient := 72535549176877750482370560000 }, { argument := 84624807373024042229432320000, coefficient := 84624807373024042229432320000 }, { argument := 955051397495557048017879040000, coefficient := 955051397495557048017879040000 }, { argument := 72535549176877750482370560000, coefficient := 72535549176877750482370560000 }, { argument := 1327942337598709502483458162688, coefficient := 1327942337598709502483458162688 }, { argument := 74953400816107008831782912000, coefficient := 74953400816107008831782912000 }, { argument := 221125801577311766223581165387776, coefficient := (-221125801577311766223581165387776) }, { argument := 1364616684329491039829316599808, coefficient := 1364616684329491039829316599808 }, { argument := 581444962201852047866682408960, coefficient := 581444962201852047866682408960 }, { argument := 13912781435716661637146199719936, coefficient := 13912781435716661637146199719936 }, { argument := 936579010971845514228368670720, coefficient := 936579010971845514228368670720 }, { argument := 29014219670751100192948224000, coefficient := 29014219670751100192948224000 }, { argument := 936579010971845514228368670720, coefficient := 936579010971845514228368670720 }, { argument := 625546576101393720159963709440, coefficient := 625546576101393720159963709440 }, { argument := 1365777253116321083837034528768, coefficient := 1365777253116321083837034528768 }, { argument := 581444962201852047866682408960, coefficient := 581444962201852047866682408960 }, { argument := 27853650883921056185230295040, coefficient := 27853650883921056185230295040 }, { argument := 20361637766165934761540795236352, coefficient := (-20361637766165934761540795236352) }, { argument := 331148960508839223535515729920, coefficient := 331148960508839223535515729920 }, { argument := 302676339605275477212835872768, coefficient := 302676339605275477212835872768 }, { argument := 331148960508839223535515729920, coefficient := 331148960508839223535515729920 }, { argument := 302676339605275477212835872768, coefficient := 302676339605275477212835872768 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }] }

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

end TermShard12


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9
