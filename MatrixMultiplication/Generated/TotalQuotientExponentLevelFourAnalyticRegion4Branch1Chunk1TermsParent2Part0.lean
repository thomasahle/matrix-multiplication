import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 1, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk1

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
def constantNumerator : ℤ := (-2059629515460471244523866947584)
def positiveArguments : Array ℕ := #[
    5, 8388571, 8388645, 3187507, 41630153, 12728683,
    918829, 32635627, 32634331, 920077, 38367, 649691,
    14101729, 324845, 19179
  ]
def positiveCoefficients : Array ℕ := #[
    792281625142643375935439503360, 79227813059144605239798136832, 79228511969384069947289763840, 120420609765698993649379966976, 393185678407870418603764350976, 120219011940545288495207284736,
    8678094546177266484110163968, 308234782184471261633035894784, 308222541810547663512641994752, 8689881572918509118563549184, 362366069696519355827748864, 12272316010488250674125471744,
    133187064760221758259376160768, 12272297121022319195544616960, 362281067099827702213902336
  ]
def positiveScales : Array ℕ := #[
    2, 22, 23, 21, 25, 23,
    19, 24, 24, 19, 15, 19,
    23, 18, 14
  ]
def negativeArguments : Array ℕ := #[
    321844303557, 5449979081561, 118293354939259, 2724985346495, 160884403209, 1464744675161,
    52012787293103, 52010706377993, 1466748534767, 1464744675161, 9561348594203, 2924554655539,
    321844303557, 321847142715, 321847142715, 5450027158695, 118294398467205, 2725009385025,
    160885822455, 9561348594203, 339657934597589, 169822253354671, 4787139546457, 52012787293103,
    339657934597589, 103851454290637, 5449979081561, 5450027158695, 2924554655539, 103851454290637,
    6490456296073, 183034650199, 52010706377993, 169822253354671, 6490456296073, 118293354939259,
    118294398467205, 1466748534767, 4787139546457, 183034650199, 2724985346495, 2725009385025,
    160884403209, 160885822455, 1, 1, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    90591117848163875020603392, 3068065470111889703443628032, 33296619326553290930498043904, 3068060747766235982075002880, 90569867292722128861790208, 824577946655999726014431232,
    29280596183964942514190811136, 29279424732900694309853986816, 825706019327860274630754304, 824577946655999726014431232, 2691280372875752910689927168, 823188953556880605350723584,
    90591117848163875020603392, 90591917000095802893271040, 90591917000095802893271040, 3068092535132235633619107840, 33296913053557588199190036480, 3068087812744923615697305600,
    90570666257191722245160960, 2691280372875752910689927168, 95605209230445882602248208384, 95601429615914284985826148352, 2694919984699288803117891584, 29280596183964942514190811136,
    95605209230445882602248208384, 29231585677824805700078927872, 3068065470111889703443628032, 3068092535132235633619107840, 823188953556880605350723584, 29231585677824805700078927872,
    29230416556458852460640862208, 824314782432105481533128704, 29279424732900694309853986816, 95601429615914284985826148352, 29230416556458852460640862208, 33296619326553290930498043904,
    33296913053557588199190036480, 825706019327860274630754304, 2694919984699288803117891584, 824314782432105481533128704, 3068060747766235982075002880, 3068087812744923615697305600,
    90569867292722128861790208, 90570666257191722245160960, 158456325028528675187087900672, 633825300114114700748351602688, 633825300114114700748351602688, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    38, 42, 46, 41, 37, 40,
    45, 45, 40, 40, 43, 41,
    38, 38, 38, 42, 46, 41,
    37, 43, 48, 47, 42, 45,
    48, 46, 42, 42, 41, 46,
    42, 37, 45, 47, 42, 46,
    46, 40, 42, 37, 41, 41,
    37, 37, 0, 0, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 22999993635168450, 23000006363344048, 21603997079563259, 25311125524922087, 23601579819690758,
    19809436866036646, 24959944420268249, 24959887127976149, 19811395077805674, 15227578341406248, 19309394194481380,
    23749368725176471, 18309391973893206, 14227239879225015
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    38227571978034134, 42309387831109266, 46749362362039881, 41309385610521092, 37227233515852901, 40413786343922583,
    45563931585568931, 45563873865417370, 40415758689453999, 40413786343922583, 43120351258209152, 41411354089784806,
    38227571978034134, 38227584704750298, 38227584704750298, 42309400557825430, 46749375088756107, 41309398337237256,
    37227246242569065, 43120351258209152, 48271075885158696, 47271018849156444, 42122301000283038, 45563931585568931,
    48271075885158696, 46561514747623395, 42309387831109266, 42309400557825430, 41411354089784806, 46561514747623395,
    42561457045679134, 37413325834009139, 45563873865417370, 47271018849156444, 42561457045679134, 46749362362039881,
    46749375088756107, 40415758689453999, 42122301000283038, 37413325834009139, 41309385610521092, 41309398337237256,
    37227233515852901, 37227246242569065, 0, 0, 0, 0
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 48
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
noncomputable def positiveFloor : ℝ := 48438647 / 100000000000
noncomputable def negativeCeiling : ℝ := 110793249 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 90591117848163875020603392, coefficient := (-90591117848163875020603392) }, { argument := 3068065470111889703443628032, coefficient := (-3068065470111889703443628032) }, { argument := 33296619326553290930498043904, coefficient := (-33296619326553290930498043904) }, { argument := 3068060747766235982075002880, coefficient := (-3068060747766235982075002880) }, { argument := 90569867292722128861790208, coefficient := (-90569867292722128861790208) }, { argument := 824577946655999726014431232, coefficient := (-824577946655999726014431232) }, { argument := 29280596183964942514190811136, coefficient := (-29280596183964942514190811136) }, { argument := 29279424732900694309853986816, coefficient := (-29279424732900694309853986816) }, { argument := 825706019327860274630754304, coefficient := (-825706019327860274630754304) }, { argument := 824577946655999726014431232, coefficient := (-824577946655999726014431232) }, { argument := 2691280372875752910689927168, coefficient := (-2691280372875752910689927168) }, { argument := 823188953556880605350723584, coefficient := (-823188953556880605350723584) }, { argument := 90591117848163875020603392, coefficient := (-90591117848163875020603392) }, { argument := 90591917000095802893271040, coefficient := (-90591917000095802893271040) }, { argument := 90591917000095802893271040, coefficient := (-90591917000095802893271040) }, { argument := 3068092535132235633619107840, coefficient := (-3068092535132235633619107840) }, { argument := 33296913053557588199190036480, coefficient := (-33296913053557588199190036480) }, { argument := 3068087812744923615697305600, coefficient := (-3068087812744923615697305600) }, { argument := 90570666257191722245160960, coefficient := (-90570666257191722245160960) }, { argument := 2691280372875752910689927168, coefficient := (-2691280372875752910689927168) }, { argument := 95605209230445882602248208384, coefficient := (-95605209230445882602248208384) }, { argument := 95601429615914284985826148352, coefficient := (-95601429615914284985826148352) }, { argument := 2694919984699288803117891584, coefficient := (-2694919984699288803117891584) }, { argument := 29280596183964942514190811136, coefficient := (-29280596183964942514190811136) }, { argument := 95605209230445882602248208384, coefficient := (-95605209230445882602248208384) }, { argument := 29231585677824805700078927872, coefficient := (-29231585677824805700078927872) }, { argument := 3068065470111889703443628032, coefficient := (-3068065470111889703443628032) }, { argument := 3068092535132235633619107840, coefficient := (-3068092535132235633619107840) }, { argument := 823188953556880605350723584, coefficient := (-823188953556880605350723584) }, { argument := 29231585677824805700078927872, coefficient := (-29231585677824805700078927872) }, { argument := 29230416556458852460640862208, coefficient := (-29230416556458852460640862208) }, { argument := 824314782432105481533128704, coefficient := (-824314782432105481533128704) }, { argument := 29279424732900694309853986816, coefficient := (-29279424732900694309853986816) }, { argument := 95601429615914284985826148352, coefficient := (-95601429615914284985826148352) }, { argument := 29230416556458852460640862208, coefficient := (-29230416556458852460640862208) }, { argument := 33296619326553290930498043904, coefficient := (-33296619326553290930498043904) }, { argument := 33296913053557588199190036480, coefficient := (-33296913053557588199190036480) }, { argument := 825706019327860274630754304, coefficient := (-825706019327860274630754304) }, { argument := 2694919984699288803117891584, coefficient := (-2694919984699288803117891584) }, { argument := 824314782432105481533128704, coefficient := (-824314782432105481533128704) }, { argument := 3068060747766235982075002880, coefficient := (-3068060747766235982075002880) }, { argument := 3068087812744923615697305600, coefficient := (-3068087812744923615697305600) }, { argument := 90569867292722128861790208, coefficient := (-90569867292722128861790208) }, { argument := 90570666257191722245160960, coefficient := (-90570666257191722245160960) }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 79227813059144605239798136832, coefficient := 79227813059144605239798136832 }, { argument := 79228511969384069947289763840, coefficient := 79228511969384069947289763840 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 120420609765698993649379966976, coefficient := 120420609765698993649379966976 }, { argument := 393185678407870418603764350976, coefficient := 393185678407870418603764350976 }, { argument := 120219011940545288495207284736, coefficient := 120219011940545288495207284736 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 8678094546177266484110163968, coefficient := 8678094546177266484110163968 }, { argument := 308234782184471261633035894784, coefficient := 308234782184471261633035894784 }, { argument := 308222541810547663512641994752, coefficient := 308222541810547663512641994752 }, { argument := 8689881572918509118563549184, coefficient := 8689881572918509118563549184 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 362366069696519355827748864, coefficient := 362366069696519355827748864 }, { argument := 12272316010488250674125471744, coefficient := 12272316010488250674125471744 }, { argument := 133187064760221758259376160768, coefficient := 133187064760221758259376160768 }, { argument := 12272297121022319195544616960, coefficient := 12272297121022319195544616960 }, { argument := 362281067099827702213902336, coefficient := 362281067099827702213902336 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk1
