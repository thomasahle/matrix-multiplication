import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 13, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-115807633183034133045186616360960)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    186175755, 16929, 7587, 2565, 837, 843,
    16017, 24447, 252057, 7587, 24447, 7587,
    7587, 649953, 7587, 252057, 649953, 843,
    7587, 7587, 16017, 25291162771, 219735, 71703,
    92969611137, 723969, 6322788603, 1450251, 649953, 219735,
    71703, 101205914859, 101202807573, 1372092467, 2565, 837,
    4966752609, 8451, 343023003, 16929, 7587, 2565,
    837, 60512777451, 60509670165, 489, 285, 5415,
    8265, 85215, 2565, 8265, 2565, 2565,
    219735, 2565, 85215, 219735, 285, 2565,
    2565, 5415, 45507227675, 85215
  ]
def negativeCoefficients : Array ℕ := #[
    6868673010429302845640540160, 319779768754000895290638336, 286628756044255985890492416, 387611840913940479140167680, 15810482984647572175454208, 254781116483783098569326592,
    302552575824492429551075328, 230895386813428433078452224, 2380611057145348327257145344, 286628756044255985890492416, 230895386813428433078452224, 286628756044255985890492416,
    286628756044255985890492416, 12277265050562298062309425152, 286628756044255985890492416, 2380611057145348327257145344, 12277265050562298062309425152, 254781116483783098569326592,
    286628756044255985890492416, 286628756044255985890492416, 302552575824492429551075328, 116634901740791972924420521984, 16602707185813783856503848960, 677215687842404341515288576,
    428746655819134069705537486848, 13675387760946616702857117696, 116634863191708544889885032448, 13697233428296371681615675392, 12277265050562298062309425152, 16602707185813783856503848960,
    677215687842404341515288576, 233364951268701462642995232768, 233357786355000735060769898496, 6327659646053442129565319168, 387611840913940479140167680, 15810482984647572175454208,
    22905103563913050949247041536, 319269753173850973607559168, 6327657547736303745103822848, 319779768754000895290638336, 286628756044255985890492416, 387611840913940479140167680,
    15810482984647572175454208, 139532964853492404619000676352, 139525799939791677036775342080, 18917271225329717325802242048, 344543858590169314791260160, 409145832075826061314621440,
    312242871847340941529579520, 3219331678701894535080837120, 387611840913940479140167680, 312242871847340941529579520, 387611840913940479140167680, 387611840913940479140167680,
    16602707185813783856503848960, 387611840913940479140167680, 3219331678701894535080837120, 16602707185813783856503848960, 344543858590169314791260160, 387611840913940479140167680,
    387611840913940479140167680, 409145832075826061314621440, 209865045606189386802869043200, 3219331678701894535080837120
  ]
def negativeScales : Array ℕ := #[
    27, 14, 12, 11, 9, 9,
    13, 14, 17, 12, 14, 12,
    12, 19, 12, 17, 19, 9,
    12, 12, 13, 34, 17, 16,
    36, 19, 32, 20, 19, 17,
    16, 36, 36, 30, 11, 9,
    32, 13, 28, 14, 12, 11,
    9, 35, 35, 8, 8, 12,
    13, 16, 11, 13, 11, 11,
    17, 11, 16, 17, 8, 11,
    11, 12, 35, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    27472089967233592, 14047209134965508, 12889313825985969, 11324743110494417, 9709083812639846, 9719388821055554,
    13967316348309272, 14577369816072640, 17943390504459361, 12889313825985969, 14577369816072640, 12889313825985969,
    12889313825985969, 19309975870857117, 12889313825985969, 17943390504459361, 19309975870857117, 9719388821055554,
    12889313825985969, 12889313825985969, 13967316348309272, 34557914315864299, 17745405159170467, 16129745861023066,
    36436040170186410, 19465568397568892, 32557913839038068, 20467871183438319, 19309975870857117, 17745405159170467,
    16129745861023066, 36558502652850081, 36558458357663099, 30353730563767537, 11324743110494417, 9709083812639846,
    32209655742767162, 13044906349096087, 28353730085354916, 14047209134965508, 12889313825985969, 11324743110494417,
    9709083812639846, 35816520753631071, 35816446670413079, 8933690662845865, 8154818109052105, 12402745622495697,
    13012799104179677, 16378819783250212, 11324743110494417, 13012799104179677, 11324743110494417, 11324743110494417,
    17745405159170467, 11324743110494417, 16378819783250212, 17745405159170467, 8154818109052105, 11324743110494417,
    11324743110494417, 12402745622495697, 35405376648092144, 16378819783250212
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 749104637 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 6868673010429302845640540160, coefficient := (-6868673010429302845640540160) }, { argument := 319779768754000895290638336, coefficient := (-319779768754000895290638336) }, { argument := 286628756044255985890492416, coefficient := (-286628756044255985890492416) }, { argument := 387611840913940479140167680, coefficient := (-387611840913940479140167680) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 254781116483783098569326592, coefficient := (-254781116483783098569326592) }, { argument := 302552575824492429551075328, coefficient := (-302552575824492429551075328) }, { argument := 230895386813428433078452224, coefficient := (-230895386813428433078452224) }, { argument := 2380611057145348327257145344, coefficient := (-2380611057145348327257145344) }, { argument := 286628756044255985890492416, coefficient := (-286628756044255985890492416) }, { argument := 230895386813428433078452224, coefficient := (-230895386813428433078452224) }, { argument := 286628756044255985890492416, coefficient := (-286628756044255985890492416) }, { argument := 286628756044255985890492416, coefficient := (-286628756044255985890492416) }, { argument := 12277265050562298062309425152, coefficient := (-12277265050562298062309425152) }, { argument := 286628756044255985890492416, coefficient := (-286628756044255985890492416) }, { argument := 2380611057145348327257145344, coefficient := (-2380611057145348327257145344) }, { argument := 12277265050562298062309425152, coefficient := (-12277265050562298062309425152) }, { argument := 254781116483783098569326592, coefficient := (-254781116483783098569326592) }, { argument := 286628756044255985890492416, coefficient := (-286628756044255985890492416) }, { argument := 286628756044255985890492416, coefficient := (-286628756044255985890492416) }, { argument := 302552575824492429551075328, coefficient := (-302552575824492429551075328) }, { argument := 116634901740791972924420521984, coefficient := (-116634901740791972924420521984) }, { argument := 16602707185813783856503848960, coefficient := (-16602707185813783856503848960) }, { argument := 677215687842404341515288576, coefficient := (-677215687842404341515288576) }, { argument := 428746655819134069705537486848, coefficient := (-428746655819134069705537486848) }, { argument := 13675387760946616702857117696, coefficient := (-13675387760946616702857117696) }, { argument := 116634863191708544889885032448, coefficient := (-116634863191708544889885032448) }, { argument := 13697233428296371681615675392, coefficient := (-13697233428296371681615675392) }, { argument := 12277265050562298062309425152, coefficient := (-12277265050562298062309425152) }, { argument := 16602707185813783856503848960, coefficient := (-16602707185813783856503848960) }, { argument := 677215687842404341515288576, coefficient := (-677215687842404341515288576) }, { argument := 233364951268701462642995232768, coefficient := (-233364951268701462642995232768) }, { argument := 233357786355000735060769898496, coefficient := (-233357786355000735060769898496) }, { argument := 6327659646053442129565319168, coefficient := (-6327659646053442129565319168) }, { argument := 387611840913940479140167680, coefficient := (-387611840913940479140167680) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 22905103563913050949247041536, coefficient := (-22905103563913050949247041536) }, { argument := 319269753173850973607559168, coefficient := (-319269753173850973607559168) }, { argument := 6327657547736303745103822848, coefficient := (-6327657547736303745103822848) }, { argument := 319779768754000895290638336, coefficient := (-319779768754000895290638336) }, { argument := 286628756044255985890492416, coefficient := (-286628756044255985890492416) }, { argument := 387611840913940479140167680, coefficient := (-387611840913940479140167680) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 139532964853492404619000676352, coefficient := (-139532964853492404619000676352) }, { argument := 139525799939791677036775342080, coefficient := (-139525799939791677036775342080) }, { argument := 18917271225329717325802242048, coefficient := (-18917271225329717325802242048) }, { argument := 344543858590169314791260160, coefficient := (-344543858590169314791260160) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 312242871847340941529579520, coefficient := (-312242871847340941529579520) }, { argument := 3219331678701894535080837120, coefficient := (-3219331678701894535080837120) }, { argument := 387611840913940479140167680, coefficient := (-387611840913940479140167680) }, { argument := 312242871847340941529579520, coefficient := (-312242871847340941529579520) }, { argument := 387611840913940479140167680, coefficient := (-387611840913940479140167680) }, { argument := 387611840913940479140167680, coefficient := (-387611840913940479140167680) }, { argument := 16602707185813783856503848960, coefficient := (-16602707185813783856503848960) }, { argument := 387611840913940479140167680, coefficient := (-387611840913940479140167680) }, { argument := 3219331678701894535080837120, coefficient := (-3219331678701894535080837120) }, { argument := 16602707185813783856503848960, coefficient := (-16602707185813783856503848960) }, { argument := 344543858590169314791260160, coefficient := (-344543858590169314791260160) }, { argument := 387611840913940479140167680, coefficient := (-387611840913940479140167680) }, { argument := 387611840913940479140167680, coefficient := (-387611840913940479140167680) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 209865045606189386802869043200, coefficient := (-209865045606189386802869043200) }, { argument := 3219331678701894535080837120, coefficient := (-3219331678701894535080837120) }] }

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


end Parent1

namespace Parent1

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4666300422214854738813117645455360)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    27807, 163282339545, 280761, 11376803139, 562419, 252057,
    85215, 27807, 6276565011, 6276462573, 25291162771, 219735,
    71703, 92969611137, 723969, 6322788603, 1450251, 649953,
    219735, 71703, 1595997982323, 1595959636365, 20421, 32993163549,
    32991626979, 14409, 20105557896685353, 285, 93, 34687468793662839,
    939, 20105557794455017, 1881, 843, 285, 93,
    16562285087494599, 16562278022311481, 361705677, 101205914859, 101202807573, 20421,
    1065, 93, 1767, 2697, 27807, 837,
    2697, 837, 837, 71703, 837, 27807,
    71703, 93, 837, 837, 1767, 1450301845,
    2565, 837, 5246541495, 8451
  ]
def negativeCoefficients : Array ℕ := #[
    131314844789156224457244672, 753006882335789878668353863680, 2651712672193928919685005312, 209864975882108474199191322624, 2655948634929062991441690624, 2380611057145348327257145344,
    3219331678701894535080837120, 131314844789156224457244672, 231564376839833953298968215552, 231560597544695107980871335936, 116634901740791972924420521984, 16602707185813783856503848960,
    677215687842404341515288576, 428746655819134069705537486848, 13675387760946616702857117696, 116634863191708544889885032448, 13697233428296371681615675392, 12277265050562298062309425152,
    16602707185813783856503848960, 677215687842404341515288576, 3680120790258650246133628010496, 3680032370499464344212319764480, 789999173195210956053594243072, 152154111042611436897536311296,
    152147024864226101926104662016, 278710594157235068453460639744, 5659211440724255567853354221568, 344543858590169314791260160, 14053762653020064155959296, 19527308941695708765292245024768,
    283795336154534198762274816, 5659211411948974123130816561152, 284248683336889684702789632, 254781116483783098569326592, 344543858590169314791260160, 14053762653020064155959296,
    18647475237111149699172742987776, 18647467282422135316892975366144, 6832427062913895699078885408768, 233364951268701462642995232768, 233357786355000735060769898496, 789999173195210956053594243072,
    20600095966233281136993239040, 14053762653020064155959296, 16688843150461326185201664, 12736222404299433141338112, 131314844789156224457244672, 15810482984647572175454208,
    12736222404299433141338112, 15810482984647572175454208, 15810482984647572175454208, 677215687842404341515288576, 15810482984647572175454208, 131314844789156224457244672,
    677215687842404341515288576, 14053762653020064155959296, 15810482984647572175454208, 15810482984647572175454208, 16688843150461326185201664, 6688336741085944675701882880,
    387611840913940479140167680, 15810482984647572175454208, 24195402057590625282797076480, 319269753173850973607559168
  ]
def negativeScales : Array ℕ := #[
    14, 37, 18, 33, 19, 17,
    16, 14, 32, 32, 34, 17,
    16, 36, 19, 32, 20, 19,
    17, 16, 40, 40, 14, 34,
    34, 13, 54, 8, 6, 54,
    9, 54, 10, 9, 8, 6,
    53, 53, 28, 36, 36, 14,
    10, 6, 10, 11, 14, 9,
    11, 9, 9, 16, 9, 14,
    16, 6, 9, 9, 10, 30,
    11, 9, 32, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    14763160485605156, 37248577802641786, 18098983021851880, 33405376168781251, 19101285807721301, 17943390504459361,
    16378819783250212, 14763160485605156, 32547328082309688, 32547304536309551, 34557914315864299, 17745405159170467,
    16129745861023066, 36436040170186410, 19465568397568892, 32557913839038068, 20467871183438319, 19309975870857117,
    17745405159170467, 16129745861023066, 40537595966340819, 40537561303271907, 14317765895114651, 34941448075217434,
    34941380883907365, 13814682594827495, 54158443887343493, 8154818109052105, 6539158811108986, 54945264096258804,
    9874981350423323, 54158443880007849, 10877284136413052, 9719388821055554, 8154818109052105, 6539158811108986,
    53878751255415013, 53878750639986205, 28430241000486233, 36558502652850081, 36558458357663099, 14317765895114651,
    10056637715113201, 6539158811108986, 10787086325046961, 11397139806235610, 14763160485605156, 9709083812639846,
    11397139806235610, 9709083812639846, 9709083812639846, 16129745861023066, 9709083812639846, 14763160485605156,
    16129745861023066, 6539158811108986, 9709083812639846, 9709083812639846, 10787086325046961, 30433706047305950,
    11324743110494417, 9709083812639846, 32288719569678249, 13044906349096087
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 51982315193 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 131314844789156224457244672, coefficient := (-131314844789156224457244672) }, { argument := 753006882335789878668353863680, coefficient := (-753006882335789878668353863680) }, { argument := 2651712672193928919685005312, coefficient := (-2651712672193928919685005312) }, { argument := 209864975882108474199191322624, coefficient := (-209864975882108474199191322624) }, { argument := 2655948634929062991441690624, coefficient := (-2655948634929062991441690624) }, { argument := 2380611057145348327257145344, coefficient := (-2380611057145348327257145344) }, { argument := 3219331678701894535080837120, coefficient := (-3219331678701894535080837120) }, { argument := 131314844789156224457244672, coefficient := (-131314844789156224457244672) }, { argument := 231564376839833953298968215552, coefficient := (-231564376839833953298968215552) }, { argument := 231560597544695107980871335936, coefficient := (-231560597544695107980871335936) }, { argument := 116634901740791972924420521984, coefficient := (-116634901740791972924420521984) }, { argument := 16602707185813783856503848960, coefficient := (-16602707185813783856503848960) }, { argument := 677215687842404341515288576, coefficient := (-677215687842404341515288576) }, { argument := 428746655819134069705537486848, coefficient := (-428746655819134069705537486848) }, { argument := 13675387760946616702857117696, coefficient := (-13675387760946616702857117696) }, { argument := 116634863191708544889885032448, coefficient := (-116634863191708544889885032448) }, { argument := 13697233428296371681615675392, coefficient := (-13697233428296371681615675392) }, { argument := 12277265050562298062309425152, coefficient := (-12277265050562298062309425152) }, { argument := 16602707185813783856503848960, coefficient := (-16602707185813783856503848960) }, { argument := 677215687842404341515288576, coefficient := (-677215687842404341515288576) }, { argument := 3680120790258650246133628010496, coefficient := (-3680120790258650246133628010496) }, { argument := 3680032370499464344212319764480, coefficient := (-3680032370499464344212319764480) }, { argument := 789999173195210956053594243072, coefficient := (-789999173195210956053594243072) }, { argument := 152154111042611436897536311296, coefficient := (-152154111042611436897536311296) }, { argument := 152147024864226101926104662016, coefficient := (-152147024864226101926104662016) }, { argument := 278710594157235068453460639744, coefficient := (-278710594157235068453460639744) }, { argument := 5659211440724255567853354221568, coefficient := (-5659211440724255567853354221568) }, { argument := 344543858590169314791260160, coefficient := (-344543858590169314791260160) }, { argument := 14053762653020064155959296, coefficient := (-14053762653020064155959296) }, { argument := 19527308941695708765292245024768, coefficient := (-19527308941695708765292245024768) }, { argument := 283795336154534198762274816, coefficient := (-283795336154534198762274816) }, { argument := 5659211411948974123130816561152, coefficient := (-5659211411948974123130816561152) }, { argument := 284248683336889684702789632, coefficient := (-284248683336889684702789632) }, { argument := 254781116483783098569326592, coefficient := (-254781116483783098569326592) }, { argument := 344543858590169314791260160, coefficient := (-344543858590169314791260160) }, { argument := 14053762653020064155959296, coefficient := (-14053762653020064155959296) }, { argument := 18647475237111149699172742987776, coefficient := (-18647475237111149699172742987776) }, { argument := 18647467282422135316892975366144, coefficient := (-18647467282422135316892975366144) }, { argument := 6832427062913895699078885408768, coefficient := (-6832427062913895699078885408768) }, { argument := 233364951268701462642995232768, coefficient := (-233364951268701462642995232768) }, { argument := 233357786355000735060769898496, coefficient := (-233357786355000735060769898496) }, { argument := 789999173195210956053594243072, coefficient := (-789999173195210956053594243072) }, { argument := 20600095966233281136993239040, coefficient := (-20600095966233281136993239040) }, { argument := 14053762653020064155959296, coefficient := (-14053762653020064155959296) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 12736222404299433141338112, coefficient := (-12736222404299433141338112) }, { argument := 131314844789156224457244672, coefficient := (-131314844789156224457244672) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 12736222404299433141338112, coefficient := (-12736222404299433141338112) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 677215687842404341515288576, coefficient := (-677215687842404341515288576) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 131314844789156224457244672, coefficient := (-131314844789156224457244672) }, { argument := 677215687842404341515288576, coefficient := (-677215687842404341515288576) }, { argument := 14053762653020064155959296, coefficient := (-14053762653020064155959296) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 6688336741085944675701882880, coefficient := (-6688336741085944675701882880) }, { argument := 387611840913940479140167680, coefficient := (-387611840913940479140167680) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 24195402057590625282797076480, coefficient := (-24195402057590625282797076480) }, { argument := 319269753173850973607559168, coefficient := (-319269753173850973607559168) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13
