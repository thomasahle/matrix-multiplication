import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 9, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent2

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-156634204736947958894647094280192)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2275, 559490720991, 2275, 45591, 76531, 73437,
    2275, 73437, 49049, 1183, 45591, 273,
    2275, 45591, 76531, 73437, 2275, 73437,
    49049, 1183, 45591, 273, 60492055, 5064947433,
    2532474633, 30245111, 75, 1503, 2523, 2421,
    75, 2421, 1617, 39, 1503, 9,
    28075, 562623, 944443, 906261, 28075, 906261,
    605297, 14599, 562623, 3369, 714321075, 59809485645,
    29904753645, 357149715, 1125, 22545, 37845, 36315,
    1125, 36315, 24255, 585, 22545, 135,
    50195535, 4202828721, 2101415121, 25097007
  ]
def negativeCoefficients : Array ℕ := #[
    171894139976455085778534400, 157482637660769859032580096, 171894139976455085778534400, 3444758565128159919001829376, 5782518868807949085589897216, 5548742838439970168931090432,
    171894139976455085778534400, 5548742838439970168931090432, 3706037657892371649385201664, 178769905575513289209675776, 3444758565128159919001829376, 165018374377396882347393024,
    171894139976455085778534400, 3444758565128159919001829376, 5782518868807949085589897216, 5548742838439970168931090432, 171894139976455085778534400, 5548742838439970168931090432,
    3706037657892371649385201664, 178769905575513289209675776, 3444758565128159919001829376, 165018374377396882347393024, 278970364269440562595102720, 23357947260835789061260050432,
    23357955714056260838662078464, 278961911048968785193074688, 90669436471097188102963200, 1817015506880787649583382528, 3050119842887709407783682048, 2926809409287017231963652096,
    90669436471097188102963200, 2926809409287017231963652096, 1954833050316855375499886592, 94296213929941075627081728, 1817015506880787649583382528, 87042659012253300578844672,
    2121287024105044629992243200, 42510591963065094385044553728, 71360095490893701352939061248, 68475145138110840656149610496, 2121287024105044629992243200, 68475145138110840656149610496,
    45734948239704762222632763392, 2206138505069246415191932928, 42510591963065094385044553728, 2036435543140842844792553472, 3294224514245521537027276800, 275822568718380062319134638080,
    275822668538323931179945820160, 3294124694301652676216094720, 170005193383307227693056000, 3406904075401476842968842240, 5718974705414455139594403840, 5487767642413157309931847680,
    170005193383307227693056000, 5487767642413157309931847680, 3665311969344103829062287360, 176805401118639516800778240, 3406904075401476842968842240, 163204985647974938585333760,
    7407553502303443023801876480, 620228046415384356350054105088, 620228270875366245247878168576, 7407329042321554125977812992
  ]
def negativeScales : Array ℕ := #[
    11, 39, 11, 15, 16, 16,
    11, 16, 15, 10, 15, 8,
    11, 15, 16, 16, 11, 16,
    15, 10, 15, 8, 25, 32,
    31, 24, 6, 10, 11, 11,
    6, 11, 10, 5, 10, 3,
    14, 19, 19, 19, 14, 19,
    19, 13, 19, 11, 29, 35,
    34, 28, 10, 14, 15, 15,
    10, 15, 14, 9, 14, 7,
    25, 31, 30, 24
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    11151650829973422, 39025323248436693, 11151650829973422, 15476461433394026, 16223756630453841, 16164219503476477,
    11151650829973422, 16164219503476477, 15581936102954605, 10208234358339789, 15476461433394026, 8092757140919853,
    11151650829973422, 15476461433394026, 16223756630453841, 16164219503476477, 11151650829973422, 16164219503476477,
    15581936102954605, 10208234358339789, 15476461433394026, 8092757140919853, 25850242337846561, 32237900149953690,
    31237900672063656, 24850198621359096, 6228818690495881, 10553629293917849, 11300924490976301, 11241387363998937,
    6228818690495881, 11241387363998937, 10659103963500476, 5285402218862249, 10553629293917849, 3169925001442313,
    14776998402576533, 19101809005595810, 19849104204358487, 19789567076199844, 14776998402576533, 19789567076199844,
    19207283675153107, 13833581931803590, 19101809005595810, 11718104713231945, 29411997445666249, 35799655260155029,
    34799655782265001, 28411953729180236, 10135709286104400, 14460519889524952, 15207815086584820, 15148277959607456,
    10135709286104400, 15148277959607456, 14565994559084324, 9192292814470767, 14460519889524952, 7076815597050831,
    25581055703294337, 31968713531387334, 30968714053497423, 24581011986808319
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
noncomputable def negativeCeiling : ℝ := 25873457 / 31250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 171894139976455085778534400, coefficient := (-171894139976455085778534400) }, { argument := 157482637660769859032580096, coefficient := (-157482637660769859032580096) }, { argument := 171894139976455085778534400, coefficient := (-171894139976455085778534400) }, { argument := 3444758565128159919001829376, coefficient := (-3444758565128159919001829376) }, { argument := 5782518868807949085589897216, coefficient := (-5782518868807949085589897216) }, { argument := 5548742838439970168931090432, coefficient := (-5548742838439970168931090432) }, { argument := 171894139976455085778534400, coefficient := (-171894139976455085778534400) }, { argument := 5548742838439970168931090432, coefficient := (-5548742838439970168931090432) }, { argument := 3706037657892371649385201664, coefficient := (-3706037657892371649385201664) }, { argument := 178769905575513289209675776, coefficient := (-178769905575513289209675776) }, { argument := 3444758565128159919001829376, coefficient := (-3444758565128159919001829376) }, { argument := 165018374377396882347393024, coefficient := (-165018374377396882347393024) }, { argument := 171894139976455085778534400, coefficient := (-171894139976455085778534400) }, { argument := 3444758565128159919001829376, coefficient := (-3444758565128159919001829376) }, { argument := 5782518868807949085589897216, coefficient := (-5782518868807949085589897216) }, { argument := 5548742838439970168931090432, coefficient := (-5548742838439970168931090432) }, { argument := 171894139976455085778534400, coefficient := (-171894139976455085778534400) }, { argument := 5548742838439970168931090432, coefficient := (-5548742838439970168931090432) }, { argument := 3706037657892371649385201664, coefficient := (-3706037657892371649385201664) }, { argument := 178769905575513289209675776, coefficient := (-178769905575513289209675776) }, { argument := 3444758565128159919001829376, coefficient := (-3444758565128159919001829376) }, { argument := 165018374377396882347393024, coefficient := (-165018374377396882347393024) }, { argument := 278970364269440562595102720, coefficient := (-278970364269440562595102720) }, { argument := 23357947260835789061260050432, coefficient := (-23357947260835789061260050432) }, { argument := 23357955714056260838662078464, coefficient := (-23357955714056260838662078464) }, { argument := 278961911048968785193074688, coefficient := (-278961911048968785193074688) }, { argument := 90669436471097188102963200, coefficient := (-90669436471097188102963200) }, { argument := 1817015506880787649583382528, coefficient := (-1817015506880787649583382528) }, { argument := 3050119842887709407783682048, coefficient := (-3050119842887709407783682048) }, { argument := 2926809409287017231963652096, coefficient := (-2926809409287017231963652096) }, { argument := 90669436471097188102963200, coefficient := (-90669436471097188102963200) }, { argument := 2926809409287017231963652096, coefficient := (-2926809409287017231963652096) }, { argument := 1954833050316855375499886592, coefficient := (-1954833050316855375499886592) }, { argument := 94296213929941075627081728, coefficient := (-94296213929941075627081728) }, { argument := 1817015506880787649583382528, coefficient := (-1817015506880787649583382528) }, { argument := 87042659012253300578844672, coefficient := (-87042659012253300578844672) }, { argument := 2121287024105044629992243200, coefficient := (-2121287024105044629992243200) }, { argument := 42510591963065094385044553728, coefficient := (-42510591963065094385044553728) }, { argument := 71360095490893701352939061248, coefficient := (-71360095490893701352939061248) }, { argument := 68475145138110840656149610496, coefficient := (-68475145138110840656149610496) }, { argument := 2121287024105044629992243200, coefficient := (-2121287024105044629992243200) }, { argument := 68475145138110840656149610496, coefficient := (-68475145138110840656149610496) }, { argument := 45734948239704762222632763392, coefficient := (-45734948239704762222632763392) }, { argument := 2206138505069246415191932928, coefficient := (-2206138505069246415191932928) }, { argument := 42510591963065094385044553728, coefficient := (-42510591963065094385044553728) }, { argument := 2036435543140842844792553472, coefficient := (-2036435543140842844792553472) }, { argument := 3294224514245521537027276800, coefficient := (-3294224514245521537027276800) }, { argument := 275822568718380062319134638080, coefficient := (-275822568718380062319134638080) }, { argument := 275822668538323931179945820160, coefficient := (-275822668538323931179945820160) }, { argument := 3294124694301652676216094720, coefficient := (-3294124694301652676216094720) }, { argument := 170005193383307227693056000, coefficient := (-170005193383307227693056000) }, { argument := 3406904075401476842968842240, coefficient := (-3406904075401476842968842240) }, { argument := 5718974705414455139594403840, coefficient := (-5718974705414455139594403840) }, { argument := 5487767642413157309931847680, coefficient := (-5487767642413157309931847680) }, { argument := 170005193383307227693056000, coefficient := (-170005193383307227693056000) }, { argument := 5487767642413157309931847680, coefficient := (-5487767642413157309931847680) }, { argument := 3665311969344103829062287360, coefficient := (-3665311969344103829062287360) }, { argument := 176805401118639516800778240, coefficient := (-176805401118639516800778240) }, { argument := 3406904075401476842968842240, coefficient := (-3406904075401476842968842240) }, { argument := 163204985647974938585333760, coefficient := (-163204985647974938585333760) }, { argument := 7407553502303443023801876480, coefficient := (-7407553502303443023801876480) }, { argument := 620228046415384356350054105088, coefficient := (-620228046415384356350054105088) }, { argument := 620228270875366245247878168576, coefficient := (-620228270875366245247878168576) }, { argument := 7407329042321554125977812992, coefficient := (-7407329042321554125977812992) }] }

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

end TermShard2


end Parent2

namespace Parent2

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-481722391740631798169976690442240)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    45841977, 2713788483, 45591, 27393196353, 1503, 3507,
    45591, 45591, 1503, 562623, 22545, 2713788483,
    45591, 3507, 22545, 3507, 45591, 45591,
    47894073, 965799643, 940365093, 965799643, 940365093, 10497271525451,
    5552700797, 55043480464309, 2473687727, 466772113, 9880248685, 4869668525,
    10498680811595, 5552700797, 466083985, 10930549619965, 497460553212675, 1098372795,
    10324704273, 121919380245, 8567307801, 248730218238825, 121919380245, 1098372795,
    8567307801, 8567307801, 8567307801, 8567307801, 8567307801, 5465333177495,
    10324704273, 2275, 45591, 76531, 73437, 2275,
    73437, 49049, 1183, 45591, 273, 714321075,
    59809485645, 29904753645, 357149715, 773682464861
  ]
def negativeCoefficients : Array ℕ := #[
    422817608775939784930492416, 50060561616081484262594838528, 3444758565128159919001829376, 505315282484664852508676456448, 1817015506880787649583382528, 132490714043390766115454976,
    3444758565128159919001829376, 3444758565128159919001829376, 1817015506880787649583382528, 42510591963065094385044553728, 3406904075401476842968842240, 50060561616081484262594838528,
    3444758565128159919001829376, 132490714043390766115454976, 3406904075401476842968842240, 132490714043390766115454976, 3444758565128159919001829376, 3444758565128159919001829376,
    441744853639281322946985984, 4453964710225262659105718272, 4336668551605270340092035072, 4453964710225262659105718272, 4336668551605270340092035072, 23637754065214020858935246848,
    51214625260071027002337918976, 247893798108237188550847627264, 45631484418245301195172216832, 2152606427313908789020721152, 45564604719200085106480906240, 44914764502236841748149043200,
    23640927495490509260518850560, 51214625260071027002337918976, 2149432997037420387437117440, 49226819195429090665053552640, 2240363162080123926795308236800, 20261401846890046226662686720,
    23807147170095804316328656896, 281126950625599391394944778240, 632155737622969442271875825664, 2240362636352308835709773414400, 281126950625599391394944778240, 20261401846890046226662686720,
    19754866800717795070996119552, 19754866800717795070996119552, 19754866800717795070996119552, 632155737622969442271875825664, 19754866800717795070996119552, 49227344923244181750588375040,
    23807147170095804316328656896, 171894139976455085778534400, 3444758565128159919001829376, 5782518868807949085589897216, 5548742838439970168931090432, 171894139976455085778534400,
    5548742838439970168931090432, 3706037657892371649385201664, 178769905575513289209675776, 3444758565128159919001829376, 165018374377396882347393024, 3294224514245521537027276800,
    275822568718380062319134638080, 275822668538323931179945820160, 3294124694301652676216094720, 1742178030225543232674070528
  ]
def negativeScales : Array ℕ := #[
    25, 31, 15, 34, 10, 11,
    15, 15, 10, 19, 14, 31,
    15, 11, 14, 11, 15, 15,
    25, 29, 29, 29, 29, 43,
    32, 45, 31, 28, 33, 32,
    43, 32, 28, 43, 48, 30,
    33, 36, 32, 47, 36, 30,
    32, 32, 32, 32, 32, 42,
    33, 11, 15, 16, 16, 11,
    16, 15, 10, 15, 8, 29,
    35, 34, 28, 39
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    25450165927909198, 31337661133173844, 15476461433394026, 34673098564482965, 10553629293917849, 11776021715645854,
    15476461433394026, 15476461433394026, 10553629293917849, 19101809005595810, 14460519889524952, 31337661133173844,
    15476461433394026, 11776021715645854, 14460519889524952, 11776021715645854, 15476461433394026, 15476461433394026,
    25513343794441069, 29847148690969260, 29808645746019874, 29847148690969260, 29808645746019874, 43255079621595673,
    32370542513500652, 45645636929791102, 31204016243086596, 28798143130452514, 33201900208761905, 32181176426373084,
    43255273294176135, 32370542513500652, 28796014701324680, 43313431179290453, 48821575459215207, 30032720651695488,
    33265381408485763, 36827136519157872, 32996194797950116, 47821575120669641, 36827136519157872, 30032720651695488,
    32996194797950116, 32996194797950116, 32996194797950116, 32996194797950116, 32996194797950116, 42313446586762925,
    33265381408485763, 11151650829973422, 15476461433394026, 16223756630453841, 16164219503476477, 11151650829973422,
    16164219503476477, 15581936102954605, 10208234358339789, 15476461433394026, 8092757140919853, 29411997445666249,
    35799655260155029, 34799655782265001, 28411953729180236, 39492950619994443
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
noncomputable def negativeCeiling : ℝ := 2120929761 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 422817608775939784930492416, coefficient := (-422817608775939784930492416) }, { argument := 50060561616081484262594838528, coefficient := (-50060561616081484262594838528) }, { argument := 3444758565128159919001829376, coefficient := (-3444758565128159919001829376) }, { argument := 505315282484664852508676456448, coefficient := (-505315282484664852508676456448) }, { argument := 1817015506880787649583382528, coefficient := (-1817015506880787649583382528) }, { argument := 132490714043390766115454976, coefficient := (-132490714043390766115454976) }, { argument := 3444758565128159919001829376, coefficient := (-3444758565128159919001829376) }, { argument := 3444758565128159919001829376, coefficient := (-3444758565128159919001829376) }, { argument := 1817015506880787649583382528, coefficient := (-1817015506880787649583382528) }, { argument := 42510591963065094385044553728, coefficient := (-42510591963065094385044553728) }, { argument := 3406904075401476842968842240, coefficient := (-3406904075401476842968842240) }, { argument := 50060561616081484262594838528, coefficient := (-50060561616081484262594838528) }, { argument := 3444758565128159919001829376, coefficient := (-3444758565128159919001829376) }, { argument := 132490714043390766115454976, coefficient := (-132490714043390766115454976) }, { argument := 3406904075401476842968842240, coefficient := (-3406904075401476842968842240) }, { argument := 132490714043390766115454976, coefficient := (-132490714043390766115454976) }, { argument := 3444758565128159919001829376, coefficient := (-3444758565128159919001829376) }, { argument := 3444758565128159919001829376, coefficient := (-3444758565128159919001829376) }, { argument := 441744853639281322946985984, coefficient := (-441744853639281322946985984) }, { argument := 4453964710225262659105718272, coefficient := (-4453964710225262659105718272) }, { argument := 4336668551605270340092035072, coefficient := (-4336668551605270340092035072) }, { argument := 4453964710225262659105718272, coefficient := (-4453964710225262659105718272) }, { argument := 4336668551605270340092035072, coefficient := (-4336668551605270340092035072) }, { argument := 23637754065214020858935246848, coefficient := (-23637754065214020858935246848) }, { argument := 51214625260071027002337918976, coefficient := (-51214625260071027002337918976) }, { argument := 247893798108237188550847627264, coefficient := (-247893798108237188550847627264) }, { argument := 45631484418245301195172216832, coefficient := (-45631484418245301195172216832) }, { argument := 2152606427313908789020721152, coefficient := (-2152606427313908789020721152) }, { argument := 45564604719200085106480906240, coefficient := (-45564604719200085106480906240) }, { argument := 44914764502236841748149043200, coefficient := (-44914764502236841748149043200) }, { argument := 23640927495490509260518850560, coefficient := (-23640927495490509260518850560) }, { argument := 51214625260071027002337918976, coefficient := (-51214625260071027002337918976) }, { argument := 2149432997037420387437117440, coefficient := (-2149432997037420387437117440) }, { argument := 49226819195429090665053552640, coefficient := (-49226819195429090665053552640) }, { argument := 2240363162080123926795308236800, coefficient := (-2240363162080123926795308236800) }, { argument := 20261401846890046226662686720, coefficient := (-20261401846890046226662686720) }, { argument := 23807147170095804316328656896, coefficient := (-23807147170095804316328656896) }, { argument := 281126950625599391394944778240, coefficient := (-281126950625599391394944778240) }, { argument := 632155737622969442271875825664, coefficient := (-632155737622969442271875825664) }, { argument := 2240362636352308835709773414400, coefficient := (-2240362636352308835709773414400) }, { argument := 281126950625599391394944778240, coefficient := (-281126950625599391394944778240) }, { argument := 20261401846890046226662686720, coefficient := (-20261401846890046226662686720) }, { argument := 19754866800717795070996119552, coefficient := (-19754866800717795070996119552) }, { argument := 19754866800717795070996119552, coefficient := (-19754866800717795070996119552) }, { argument := 19754866800717795070996119552, coefficient := (-19754866800717795070996119552) }, { argument := 632155737622969442271875825664, coefficient := (-632155737622969442271875825664) }, { argument := 19754866800717795070996119552, coefficient := (-19754866800717795070996119552) }, { argument := 49227344923244181750588375040, coefficient := (-49227344923244181750588375040) }, { argument := 23807147170095804316328656896, coefficient := (-23807147170095804316328656896) }, { argument := 171894139976455085778534400, coefficient := (-171894139976455085778534400) }, { argument := 3444758565128159919001829376, coefficient := (-3444758565128159919001829376) }, { argument := 5782518868807949085589897216, coefficient := (-5782518868807949085589897216) }, { argument := 5548742838439970168931090432, coefficient := (-5548742838439970168931090432) }, { argument := 171894139976455085778534400, coefficient := (-171894139976455085778534400) }, { argument := 5548742838439970168931090432, coefficient := (-5548742838439970168931090432) }, { argument := 3706037657892371649385201664, coefficient := (-3706037657892371649385201664) }, { argument := 178769905575513289209675776, coefficient := (-178769905575513289209675776) }, { argument := 3444758565128159919001829376, coefficient := (-3444758565128159919001829376) }, { argument := 165018374377396882347393024, coefficient := (-165018374377396882347393024) }, { argument := 3294224514245521537027276800, coefficient := (-3294224514245521537027276800) }, { argument := 275822568718380062319134638080, coefficient := (-275822568718380062319134638080) }, { argument := 275822668538323931179945820160, coefficient := (-275822668538323931179945820160) }, { argument := 3294124694301652676216094720, coefficient := (-3294124694301652676216094720) }, { argument := 1742178030225543232674070528, coefficient := (-1742178030225543232674070528) }] }

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

end TermShard3


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9
