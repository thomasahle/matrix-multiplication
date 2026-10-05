import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 0, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk0

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-488990300108892459505696028753920)
def positiveArguments : Array ℕ := #[
    1, 1, 1, 1, 386995, 10585297,
    3095959, 1263469, 47, 20426823, 1163, 37,
    20426833, 19, 19, 643, 35, 1163,
    643, 1263459, 37, 35, 47, 1179615,
    87174109, 2907, 805820495, 2983, 95, 2907,
    1653, 2983, 46569, 57, 43587083, 2907,
    95, 57, 95, 1463, 1653, 1179615,
    3150745, 109681767, 455, 403, 18863, 5135,
    54840903, 18863, 455, 455, 195, 455,
    5135, 195, 1575353, 403
  ]
def positiveCoefficients : Array ℕ := #[
    19807040628566084398385987584, 19807040628566084398385987584, 19807040628566084398385987584, 19807040628566084398385987584, 29240515472610213591588536320, 99975303528041213743201255424,
    29240506027877247852298108928, 11933127315489655537006542848, 909112216350201139379044352, 385851777146843099411861471232, 22495691651389019682932523008, 715684085211860471426056192,
    385851966041502414197670019072, 735026898325694538221355008, 735026898325694538221355008, 12437428832195304949377138688, 676998458984192337835458560, 22495691651389019682932523008,
    12437428832195304949377138688, 11933032868159998144102268928, 715684085211860471426056192, 676998458984192337835458560, 909112216350201139379044352, 5570574338690276538754007040,
    411668090515625084650063396864, 56229557721915632173933658112, 3805379696797426526574891499520, 57699611518567021250376368128, 1837567245814236345553387520, 56229557721915632173933658112,
    31973670077167712412628942848, 57699611518567021250376368128, 900775463898138656590270562304, 35281291119633337834625040384, 411668359690514608219840577536, 56229557721915632173933658112,
    1837567245814236345553387520, 35281291119633337834625040384, 1837567245814236345553387520, 56597071171078479443044335616, 31973670077167712412628942848, 5570574338690276538754007040,
    119031780672552962470612828160, 4143660002101743341610159046656, 70407839734356003134887690240, 62361229479001031348043382784, 2918907870130016015677772529664, 794602762716303463950875361280,
    4143661475480085996939465719808, 2918907870130016015677772529664, 70407839734356003134887690240, 70407839734356003134887690240, 60349576915162288401332305920, 70407839734356003134887690240,
    794602762716303463950875361280, 60349576915162288401332305920, 119030307294210307141306155008, 62361229479001031348043382784
  ]
def positiveScales : Array ℕ := #[
    0, 0, 0, 0, 18, 23,
    21, 20, 5, 24, 10, 5,
    24, 4, 4, 9, 5, 10,
    9, 20, 5, 5, 5, 20,
    26, 11, 29, 11, 6, 11,
    10, 11, 15, 5, 25, 11,
    6, 5, 6, 10, 10, 20,
    21, 26, 8, 8, 14, 12,
    25, 14, 8, 8, 7, 8,
    12, 7, 20, 8
  ]
def negativeArguments : Array ℕ := #[
    1, 1, 1, 11, 19, 13
  ]
def negativeCoefficients : Array ℕ := #[
    158456325028528675187087900672, 79228162514264337593543950336, 158456325028528675187087900672, 871509787656907713528983453696, 6021340351084089657109340225536, 16479457802966982219457141669888
  ]
def negativeScales : Array ℕ := #[
    0, 0, 0, 3, 4, 3
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 0, 0, 0, 18561955401215154, 23335558412953919,
    21561954935222288, 20268958836618398, 5554588851677541, 24283961502224936, 10183635381473218, 5209453365628949,
    24283962208499567, 4247927513443585, 4247927513443585, 9328674927327946, 5129283016944966, 10183635381473218,
    9328674927327946, 20268947418049758, 5209453365628949, 5129283016944966, 5554588851677541, 20169884642282394,
    26377396377611558, 11505315356136216, 29585883258130528, 11542548262335146, 6569855608330797, 11505315356136216,
    10690871009288692, 11542548262335146, 15507082282310403, 5832890014087662, 25377397320937408, 11505315356136216,
    6569855608330797, 5832890014087662, 6569855608330797, 10514714054138458, 10690871009288692, 20169884642282394,
    21587261566420675, 26708748477679130, 8829722735013603, 8654636028526477, 14203271522207836, 12326148561205557,
    25708748990664088, 14203271522207836, 8829722735013603, 8829722735013603, 7607330313749179, 8829722735013603,
    12326148561205557, 7607330313749179, 20587243708595042, 8654636028526477
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0, 0, 3459431618637364, 4247927513443586, 3700439718214233
  ]

abbrev PositiveTerm := Fin 58
abbrev NegativeTerm := Fin 6
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
noncomputable def positiveFloor : ℝ := 1521919171 / 250000000000
noncomputable def negativeCeiling : ℝ := 1078212453 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 19807040628566084398385987584, coefficient := 19807040628566084398385987584 }, { argument := 19807040628566084398385987584, coefficient := 19807040628566084398385987584 }, { argument := 19807040628566084398385987584, coefficient := 19807040628566084398385987584 }, { argument := 19807040628566084398385987584, coefficient := 19807040628566084398385987584 }, { argument := 79228162514264337593543950336, coefficient := (-79228162514264337593543950336) }, { argument := 29240515472610213591588536320, coefficient := 29240515472610213591588536320 }, { argument := 99975303528041213743201255424, coefficient := 99975303528041213743201255424 }, { argument := 29240506027877247852298108928, coefficient := 29240506027877247852298108928 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 11933127315489655537006542848, coefficient := 11933127315489655537006542848 }, { argument := 909112216350201139379044352, coefficient := 909112216350201139379044352 }, { argument := 385851777146843099411861471232, coefficient := 385851777146843099411861471232 }, { argument := 22495691651389019682932523008, coefficient := 22495691651389019682932523008 }, { argument := 715684085211860471426056192, coefficient := 715684085211860471426056192 }, { argument := 385851966041502414197670019072, coefficient := 385851966041502414197670019072 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 12437428832195304949377138688, coefficient := 12437428832195304949377138688 }, { argument := 676998458984192337835458560, coefficient := 676998458984192337835458560 }, { argument := 22495691651389019682932523008, coefficient := 22495691651389019682932523008 }, { argument := 12437428832195304949377138688, coefficient := 12437428832195304949377138688 }, { argument := 11933032868159998144102268928, coefficient := 11933032868159998144102268928 }, { argument := 715684085211860471426056192, coefficient := 715684085211860471426056192 }, { argument := 676998458984192337835458560, coefficient := 676998458984192337835458560 }, { argument := 909112216350201139379044352, coefficient := 909112216350201139379044352 }, { argument := 871509787656907713528983453696, coefficient := (-871509787656907713528983453696) }, { argument := 5570574338690276538754007040, coefficient := 5570574338690276538754007040 }, { argument := 411668090515625084650063396864, coefficient := 411668090515625084650063396864 }, { argument := 56229557721915632173933658112, coefficient := 56229557721915632173933658112 }, { argument := 3805379696797426526574891499520, coefficient := 3805379696797426526574891499520 }, { argument := 57699611518567021250376368128, coefficient := 57699611518567021250376368128 }, { argument := 1837567245814236345553387520, coefficient := 1837567245814236345553387520 }, { argument := 56229557721915632173933658112, coefficient := 56229557721915632173933658112 }, { argument := 31973670077167712412628942848, coefficient := 31973670077167712412628942848 }, { argument := 57699611518567021250376368128, coefficient := 57699611518567021250376368128 }, { argument := 900775463898138656590270562304, coefficient := 900775463898138656590270562304 }, { argument := 35281291119633337834625040384, coefficient := 35281291119633337834625040384 }, { argument := 411668359690514608219840577536, coefficient := 411668359690514608219840577536 }, { argument := 56229557721915632173933658112, coefficient := 56229557721915632173933658112 }, { argument := 1837567245814236345553387520, coefficient := 1837567245814236345553387520 }, { argument := 35281291119633337834625040384, coefficient := 35281291119633337834625040384 }, { argument := 1837567245814236345553387520, coefficient := 1837567245814236345553387520 }, { argument := 56597071171078479443044335616, coefficient := 56597071171078479443044335616 }, { argument := 31973670077167712412628942848, coefficient := 31973670077167712412628942848 }, { argument := 5570574338690276538754007040, coefficient := 5570574338690276538754007040 }, { argument := 6021340351084089657109340225536, coefficient := (-6021340351084089657109340225536) }, { argument := 119031780672552962470612828160, coefficient := 119031780672552962470612828160 }, { argument := 4143660002101743341610159046656, coefficient := 4143660002101743341610159046656 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 62361229479001031348043382784, coefficient := 62361229479001031348043382784 }, { argument := 2918907870130016015677772529664, coefficient := 2918907870130016015677772529664 }, { argument := 794602762716303463950875361280, coefficient := 794602762716303463950875361280 }, { argument := 4143661475480085996939465719808, coefficient := 4143661475480085996939465719808 }, { argument := 2918907870130016015677772529664, coefficient := 2918907870130016015677772529664 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 60349576915162288401332305920, coefficient := 60349576915162288401332305920 }, { argument := 70407839734356003134887690240, coefficient := 70407839734356003134887690240 }, { argument := 794602762716303463950875361280, coefficient := 794602762716303463950875361280 }, { argument := 60349576915162288401332305920, coefficient := 60349576915162288401332305920 }, { argument := 119030307294210307141306155008, coefficient := 119030307294210307141306155008 }, { argument := 62361229479001031348043382784, coefficient := 62361229479001031348043382784 }, { argument := 16479457802966982219457141669888, coefficient := (-16479457802966982219457141669888) }] }

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

end TermShard6


end Parent3

namespace Parent3

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-120625150201300237502617497894912)
def positiveArguments : Array ℕ := #[
    33114321, 28557, 230281007, 45999, 1425, 45999,
    30723, 33347793, 28557, 171, 2675, 2445,
    2675, 2445
  ]
def positiveCoefficients : Array ℕ := #[
    156377959593386432762442940416, 552372714091759445473348288512, 2174942618196540299085290143744, 889750060423253238516950237184, 27563508687213545183300812800, 889750060423253238516950237184,
    594269247296324034151965523968, 157480499940874974569774972928, 552372714091759445473348288512, 26460968339725003375968780288, 206968100318024514709697331200, 189172712253297173258022420480,
    206968100318024514709697331200, 189172712253297173258022420480
  ]
def positiveScales : Array ℕ := #[
    24, 14, 27, 15, 10, 15,
    14, 24, 14, 7, 11, 11,
    11, 11
  ]
def negativeArguments : Array ℕ := #[
    19, 5
  ]
def negativeCoefficients : Array ℕ := #[
    6021340351084089657109340225536, 792281625142643375935439503360
  ]
def negativeScales : Array ℕ := #[
    4, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    24980951939608539, 14801556807318634, 27778820185241299, 15489314877442509, 10476746203939458, 15489314877442509,
    14907031476611228, 24991087948094440, 14801556807318634, 7417852514885896, 11385323176175871, 11255618749839595,
    11385323176175871, 11255618749839595
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    4247927513443586, 2321928094887363
  ]

abbrev PositiveTerm := Fin 14
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 31414269 / 20000000000
noncomputable def negativeCeiling : ℝ := 20626889 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 156377959593386432762442940416, coefficient := 156377959593386432762442940416 }, { argument := 552372714091759445473348288512, coefficient := 552372714091759445473348288512 }, { argument := 2174942618196540299085290143744, coefficient := 2174942618196540299085290143744 }, { argument := 889750060423253238516950237184, coefficient := 889750060423253238516950237184 }, { argument := 27563508687213545183300812800, coefficient := 27563508687213545183300812800 }, { argument := 889750060423253238516950237184, coefficient := 889750060423253238516950237184 }, { argument := 594269247296324034151965523968, coefficient := 594269247296324034151965523968 }, { argument := 157480499940874974569774972928, coefficient := 157480499940874974569774972928 }, { argument := 552372714091759445473348288512, coefficient := 552372714091759445473348288512 }, { argument := 26460968339725003375968780288, coefficient := 26460968339725003375968780288 }, { argument := 6021340351084089657109340225536, coefficient := (-6021340351084089657109340225536) }, { argument := 206968100318024514709697331200, coefficient := 206968100318024514709697331200 }, { argument := 189172712253297173258022420480, coefficient := 189172712253297173258022420480 }, { argument := 206968100318024514709697331200, coefficient := 206968100318024514709697331200 }, { argument := 189172712253297173258022420480, coefficient := 189172712253297173258022420480 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }] }

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

end TermShard7


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk0
