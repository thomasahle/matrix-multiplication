import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 12, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12

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
def constantNumerator : ℤ := (-294425223335559766742944387694592)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    5289985, 5195777, 5289985, 5195777, 71590234665885, 173237579711,
    381766238002787, 158193690277, 7323361395, 157974433757, 152989095889, 71611796389789,
    173237579711, 28524629, 8506259105685, 450807914403947, 86122215, 805401621,
    9954983465, 662831677, 225403945557097, 9954983465, 86122215, 672111677,
    670063677, 672111677, 662831677, 670063677, 4253141197719, 805401621,
    16625, 4275, 16625, 14725, 689225, 187625,
    4275, 689225, 16625, 16625, 7125, 16625,
    187625, 7125, 16625, 14725, 58549891321, 6861526578493,
    818058787, 274732947237815, 26968971, 62927599, 818058787, 818058787,
    26968971, 10095384811, 404534565, 6861527497533, 818058787, 62927599,
    404534565, 62927599, 818058787, 818058787
  ]
def negativeCoefficients : Array ℕ := #[
    49962495717766360271547269120, 49072726314529993198963523584, 49962495717766360271547269120, 49072726314529993198963523584, 80603438541161512801916682240, 199729331054854706721179303936,
    859661143605993811137764786176, 182384907413468379174878052352, 8443260838303097796710891520, 182132121856535117938747768832, 176384418620787067257213681664, 80627714884096392780983566336,
    199729331054854706721179303936, 8418984495368217817644007424, 19154392669339927276557434880, 1015129177662643082791386873856, 6354697836663959407306997760, 7428518789568908177354784768,
    91818516118432663774922014720, 195633380953067419336821440512, 1015129125218781616615941210112, 91818516118432663774922014720, 6354697836663959407306997760, 6199136047285369173773910016,
    6180246581353890592919126016, 6199136047285369173773910016, 195633380953067419336821440512, 6180246581353890592919126016, 19154445113201393452003098624, 7428518789568908177354784768,
    157018685555415703355392000, 161504933714141866308403200, 157018685555415703355392000, 139073692920511051543347200, 6509546078311662444819251200, 1772068022696834366439424000,
    161504933714141866308403200, 6509546078311662444819251200, 157018685555415703355392000, 157018685555415703355392000, 134587444761784888590336000, 157018685555415703355392000,
    1772068022696834366439424000, 134587444761784888590336000, 157018685555415703355392000, 139073692920511051543347200, 263685268735838637801865216, 30901568542093829173336342528,
    1886315135129784298162356224, 309321799701655443078706626560, 994979411936589519909814272, 72550582120376319160090624, 1886315135129784298162356224, 1886315135129784298162356224,
    994979411936589519909814272, 23278372491766458976223363072, 1865586397381105349830901760, 30901572681082030711916986368, 1886315135129784298162356224, 72550582120376319160090624,
    1865586397381105349830901760, 72550582120376319160090624, 1886315135129784298162356224, 1886315135129784298162356224
  ]
def negativeScales : Array ℕ := #[
    22, 22, 22, 22, 46, 37,
    48, 37, 32, 37, 37, 46,
    37, 24, 42, 48, 26, 29,
    33, 29, 47, 33, 26, 29,
    29, 29, 29, 29, 41, 29,
    14, 12, 14, 13, 19, 17,
    12, 19, 14, 14, 12, 14,
    17, 12, 14, 13, 35, 42,
    29, 47, 24, 25, 29, 29,
    24, 33, 28, 42, 29, 25,
    28, 25, 29, 29
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    22334832200839980, 22308908081730818, 22334832200839980, 22308908081730818, 46024828042255307, 37333960965637631,
    48439682850180996, 37202901101298489, 32769858846390160, 37200900138388260, 37154637874015734, 46025262491294264,
    37333960965637631, 24765704787032810, 42951661950346277, 48679506172218686, 26359882089248749, 29585133135044485,
    33212771773650542, 29304067310298542, 47679506097685806, 33212771773650542, 26359882089248749, 29324125727918357,
    29319722962321378, 29324125727918357, 29304067310298542, 29319722962321378, 41951665900375404, 29585133135044485,
    14021066720163277, 12061708704660623, 14021066720163277, 13845980015209050, 19394615507285060, 17517492546283257,
    12061708704660623, 19394615507285060, 14021066720163277, 14021066720163277, 12798674299455620, 14021066720163277,
    17517492546283257, 12798674299455620, 14021066720163277, 13845980015209050, 35768947442042670, 42641666727046951,
    29607629280348623, 47965023277236982, 24684797140914520, 25907189567166222, 29607629280348623, 29607629280348623,
    24684797140914520, 33232976852543554, 28591687736477113, 42641666920283011, 29607629280348623, 25907189567166222,
    28591687736477113, 25907189567166222, 29607629280348623, 29607629280348623
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
noncomputable def negativeCeiling : ℝ := 681886139 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 49962495717766360271547269120, coefficient := (-49962495717766360271547269120) }, { argument := 49072726314529993198963523584, coefficient := (-49072726314529993198963523584) }, { argument := 49962495717766360271547269120, coefficient := (-49962495717766360271547269120) }, { argument := 49072726314529993198963523584, coefficient := (-49072726314529993198963523584) }, { argument := 80603438541161512801916682240, coefficient := (-80603438541161512801916682240) }, { argument := 199729331054854706721179303936, coefficient := (-199729331054854706721179303936) }, { argument := 859661143605993811137764786176, coefficient := (-859661143605993811137764786176) }, { argument := 182384907413468379174878052352, coefficient := (-182384907413468379174878052352) }, { argument := 8443260838303097796710891520, coefficient := (-8443260838303097796710891520) }, { argument := 182132121856535117938747768832, coefficient := (-182132121856535117938747768832) }, { argument := 176384418620787067257213681664, coefficient := (-176384418620787067257213681664) }, { argument := 80627714884096392780983566336, coefficient := (-80627714884096392780983566336) }, { argument := 199729331054854706721179303936, coefficient := (-199729331054854706721179303936) }, { argument := 8418984495368217817644007424, coefficient := (-8418984495368217817644007424) }, { argument := 19154392669339927276557434880, coefficient := (-19154392669339927276557434880) }, { argument := 1015129177662643082791386873856, coefficient := (-1015129177662643082791386873856) }, { argument := 6354697836663959407306997760, coefficient := (-6354697836663959407306997760) }, { argument := 7428518789568908177354784768, coefficient := (-7428518789568908177354784768) }, { argument := 91818516118432663774922014720, coefficient := (-91818516118432663774922014720) }, { argument := 195633380953067419336821440512, coefficient := (-195633380953067419336821440512) }, { argument := 1015129125218781616615941210112, coefficient := (-1015129125218781616615941210112) }, { argument := 91818516118432663774922014720, coefficient := (-91818516118432663774922014720) }, { argument := 6354697836663959407306997760, coefficient := (-6354697836663959407306997760) }, { argument := 6199136047285369173773910016, coefficient := (-6199136047285369173773910016) }, { argument := 6180246581353890592919126016, coefficient := (-6180246581353890592919126016) }, { argument := 6199136047285369173773910016, coefficient := (-6199136047285369173773910016) }, { argument := 195633380953067419336821440512, coefficient := (-195633380953067419336821440512) }, { argument := 6180246581353890592919126016, coefficient := (-6180246581353890592919126016) }, { argument := 19154445113201393452003098624, coefficient := (-19154445113201393452003098624) }, { argument := 7428518789568908177354784768, coefficient := (-7428518789568908177354784768) }, { argument := 157018685555415703355392000, coefficient := (-157018685555415703355392000) }, { argument := 161504933714141866308403200, coefficient := (-161504933714141866308403200) }, { argument := 157018685555415703355392000, coefficient := (-157018685555415703355392000) }, { argument := 139073692920511051543347200, coefficient := (-139073692920511051543347200) }, { argument := 6509546078311662444819251200, coefficient := (-6509546078311662444819251200) }, { argument := 1772068022696834366439424000, coefficient := (-1772068022696834366439424000) }, { argument := 161504933714141866308403200, coefficient := (-161504933714141866308403200) }, { argument := 6509546078311662444819251200, coefficient := (-6509546078311662444819251200) }, { argument := 157018685555415703355392000, coefficient := (-157018685555415703355392000) }, { argument := 157018685555415703355392000, coefficient := (-157018685555415703355392000) }, { argument := 134587444761784888590336000, coefficient := (-134587444761784888590336000) }, { argument := 157018685555415703355392000, coefficient := (-157018685555415703355392000) }, { argument := 1772068022696834366439424000, coefficient := (-1772068022696834366439424000) }, { argument := 134587444761784888590336000, coefficient := (-134587444761784888590336000) }, { argument := 157018685555415703355392000, coefficient := (-157018685555415703355392000) }, { argument := 139073692920511051543347200, coefficient := (-139073692920511051543347200) }, { argument := 263685268735838637801865216, coefficient := (-263685268735838637801865216) }, { argument := 30901568542093829173336342528, coefficient := (-30901568542093829173336342528) }, { argument := 1886315135129784298162356224, coefficient := (-1886315135129784298162356224) }, { argument := 309321799701655443078706626560, coefficient := (-309321799701655443078706626560) }, { argument := 994979411936589519909814272, coefficient := (-994979411936589519909814272) }, { argument := 72550582120376319160090624, coefficient := (-72550582120376319160090624) }, { argument := 1886315135129784298162356224, coefficient := (-1886315135129784298162356224) }, { argument := 1886315135129784298162356224, coefficient := (-1886315135129784298162356224) }, { argument := 994979411936589519909814272, coefficient := (-994979411936589519909814272) }, { argument := 23278372491766458976223363072, coefficient := (-23278372491766458976223363072) }, { argument := 1865586397381105349830901760, coefficient := (-1865586397381105349830901760) }, { argument := 30901572681082030711916986368, coefficient := (-30901572681082030711916986368) }, { argument := 1886315135129784298162356224, coefficient := (-1886315135129784298162356224) }, { argument := 72550582120376319160090624, coefficient := (-72550582120376319160090624) }, { argument := 1865586397381105349830901760, coefficient := (-1865586397381105349830901760) }, { argument := 72550582120376319160090624, coefficient := (-72550582120376319160090624) }, { argument := 1886315135129784298162356224, coefficient := (-1886315135129784298162356224) }, { argument := 1886315135129784298162356224, coefficient := (-1886315135129784298162356224) }] }

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

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-8546814922878652331184327344783360)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    243396858493, 5289983, 5195775, 5289983, 5195775, 129467158604387,
    596219833909, 687644876349597, 545508542663, 25215942601, 544755873367, 526826037019,
    129505726426211, 596219833909, 3142576853, 312225236686955, 16841970582710165, 3057778905,
    28739363307, 339771805655, 23842590259, 8420984837432215, 339771805655, 3057778905,
    23851000259, 23849144259, 23851000259, 23842590259, 23849144259, 156113072266345,
    28739363307, 261625, 67275, 261625, 231725, 10846225,
    2952625, 67275, 10846225, 261625, 261625, 112125,
    261625, 2952625, 112125, 261625, 231725, 3431408044107,
    439400166797279, 85771988393, 17541390884382797, 2827647969, 6597845261, 85771988393,
    85771988393, 2827647969, 1058482889729, 42414719535, 439400174517215, 85771988393,
    6597845261, 42414719535, 6597845261, 85771988393
  ]
def negativeCoefficients : Array ℕ := #[
    274040500303056036148805632, 49962476828300428792966414336, 49072707425064061720382668800, 49962476828300428792966414336, 49072707425064061720382668800, 291534123623717099078969982976,
    687394667986808682374898909184, 3096877208891275846908339290112, 628928529782914334649208537088, 29072002483624810418406424576, 628060761165698638379002888192, 607389067266007944019044204544,
    291620970637714628120651235328, 687394667986808682374898909184, 28985155469627281376725172224, 703068729799517727528677539840, 37924746220239177238060120145920, 225624259578091328113653841920,
    265073839882793995544146477056, 3133841771189982383294371594240, 7037090568993493333678388936704, 37924744175952320310113090928640, 3133841771189982383294371594240, 225624259578091328113653841920,
    219986648839876615341994934272, 219969530261376212878095286272, 219986648839876615341994934272, 7037090568993493333678388936704, 219969530261376212878095286272, 703070774086374655475706757120,
    265073839882793995544146477056, 1235489131080770929033216000, 1270788820540221527005593600, 1235489131080770929033216000, 1094290373242968537143705600, 51219849405662817657919897600,
    13943377336482986199089152000, 1270788820540221527005593600, 51219849405662817657919897600, 1235489131080770929033216000, 1235489131080770929033216000, 1058990683783517939171328000,
    1235489131080770929033216000, 13943377336482986199089152000, 1058990683783517939171328000, 1235489131080770929033216000, 1094290373242968537143705600, 30907375977592815405596934144,
    3957764854909518986425315360768, 197776739822357149707598299136, 39499700725233289925758503878656, 104321796829375199845766135808, 7606797685475274988753780736, 197776739822357149707598299136,
    197776739822357149707598299136, 104321796829375199845766135808, 2440695371653923946391570219008, 195603369055078499710811504640, 3957764924444520772273470177280, 197776739822357149707598299136,
    7606797685475274988753780736, 195603369055078499710811504640, 7606797685475274988753780736, 197776739822357149707598299136
  ]
def negativeScales : Array ℕ := #[
    37, 22, 22, 22, 22, 46,
    39, 49, 38, 34, 38, 38,
    46, 39, 31, 48, 53, 31,
    34, 38, 34, 52, 38, 31,
    34, 34, 34, 34, 34, 47,
    34, 17, 16, 17, 17, 23,
    21, 16, 23, 17, 17, 16,
    17, 21, 16, 17, 17, 41,
    48, 36, 53, 31, 32, 36,
    36, 31, 39, 35, 48, 36,
    32, 35, 32, 36
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    37824519592220634, 22334831655395971, 22308907526397008, 22334831655395971, 22308907526397008, 46879579513307526,
    39117053412726780, 49288657027942916, 38988810852874516, 34553617104781919, 38986818908977098, 38938535701179469,
    46880009223227031, 39117053412726780, 31549300880761020, 48149580481279072, 53902910472579636, 31509836949308126,
    34742309049689389, 38305775186073257, 34472821927577129, 52902910394812924, 38305775186073257, 31509836949308126,
    34473330719860867, 34473218450096308, 34473330719860867, 34472821927577129, 34473218450096308, 47149584676143810,
    34742309049689389, 17997140903537453, 16037782865415143, 17997140903537453, 17822054175365864, 23370689668039577,
    21493566707037514, 16037782865415143, 23370689668039577, 17997140903537453, 17997140903537453, 16774748459963978,
    17997140903537453, 21493566707037514, 16774748459963978, 17997140903537453, 17822054175365864, 41641937832094551,
    48642528745852205, 36319787514958093, 53961612676732915, 31396955375480559, 32619347796826575, 36319787514958093,
    36319787514958093, 31396955375480559, 39945135096759702, 35303845971089072, 48642528771199290, 36319787514958093,
    32619347796826575, 35303845971089072, 32619347796826575, 36319787514958093
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
noncomputable def negativeCeiling : ℝ := 47511075709 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 274040500303056036148805632, coefficient := (-274040500303056036148805632) }, { argument := 49962476828300428792966414336, coefficient := (-49962476828300428792966414336) }, { argument := 49072707425064061720382668800, coefficient := (-49072707425064061720382668800) }, { argument := 49962476828300428792966414336, coefficient := (-49962476828300428792966414336) }, { argument := 49072707425064061720382668800, coefficient := (-49072707425064061720382668800) }, { argument := 291534123623717099078969982976, coefficient := (-291534123623717099078969982976) }, { argument := 687394667986808682374898909184, coefficient := (-687394667986808682374898909184) }, { argument := 3096877208891275846908339290112, coefficient := (-3096877208891275846908339290112) }, { argument := 628928529782914334649208537088, coefficient := (-628928529782914334649208537088) }, { argument := 29072002483624810418406424576, coefficient := (-29072002483624810418406424576) }, { argument := 628060761165698638379002888192, coefficient := (-628060761165698638379002888192) }, { argument := 607389067266007944019044204544, coefficient := (-607389067266007944019044204544) }, { argument := 291620970637714628120651235328, coefficient := (-291620970637714628120651235328) }, { argument := 687394667986808682374898909184, coefficient := (-687394667986808682374898909184) }, { argument := 28985155469627281376725172224, coefficient := (-28985155469627281376725172224) }, { argument := 703068729799517727528677539840, coefficient := (-703068729799517727528677539840) }, { argument := 37924746220239177238060120145920, coefficient := (-37924746220239177238060120145920) }, { argument := 225624259578091328113653841920, coefficient := (-225624259578091328113653841920) }, { argument := 265073839882793995544146477056, coefficient := (-265073839882793995544146477056) }, { argument := 3133841771189982383294371594240, coefficient := (-3133841771189982383294371594240) }, { argument := 7037090568993493333678388936704, coefficient := (-7037090568993493333678388936704) }, { argument := 37924744175952320310113090928640, coefficient := (-37924744175952320310113090928640) }, { argument := 3133841771189982383294371594240, coefficient := (-3133841771189982383294371594240) }, { argument := 225624259578091328113653841920, coefficient := (-225624259578091328113653841920) }, { argument := 219986648839876615341994934272, coefficient := (-219986648839876615341994934272) }, { argument := 219969530261376212878095286272, coefficient := (-219969530261376212878095286272) }, { argument := 219986648839876615341994934272, coefficient := (-219986648839876615341994934272) }, { argument := 7037090568993493333678388936704, coefficient := (-7037090568993493333678388936704) }, { argument := 219969530261376212878095286272, coefficient := (-219969530261376212878095286272) }, { argument := 703070774086374655475706757120, coefficient := (-703070774086374655475706757120) }, { argument := 265073839882793995544146477056, coefficient := (-265073839882793995544146477056) }, { argument := 1235489131080770929033216000, coefficient := (-1235489131080770929033216000) }, { argument := 1270788820540221527005593600, coefficient := (-1270788820540221527005593600) }, { argument := 1235489131080770929033216000, coefficient := (-1235489131080770929033216000) }, { argument := 1094290373242968537143705600, coefficient := (-1094290373242968537143705600) }, { argument := 51219849405662817657919897600, coefficient := (-51219849405662817657919897600) }, { argument := 13943377336482986199089152000, coefficient := (-13943377336482986199089152000) }, { argument := 1270788820540221527005593600, coefficient := (-1270788820540221527005593600) }, { argument := 51219849405662817657919897600, coefficient := (-51219849405662817657919897600) }, { argument := 1235489131080770929033216000, coefficient := (-1235489131080770929033216000) }, { argument := 1235489131080770929033216000, coefficient := (-1235489131080770929033216000) }, { argument := 1058990683783517939171328000, coefficient := (-1058990683783517939171328000) }, { argument := 1235489131080770929033216000, coefficient := (-1235489131080770929033216000) }, { argument := 13943377336482986199089152000, coefficient := (-13943377336482986199089152000) }, { argument := 1058990683783517939171328000, coefficient := (-1058990683783517939171328000) }, { argument := 1235489131080770929033216000, coefficient := (-1235489131080770929033216000) }, { argument := 1094290373242968537143705600, coefficient := (-1094290373242968537143705600) }, { argument := 30907375977592815405596934144, coefficient := (-30907375977592815405596934144) }, { argument := 3957764854909518986425315360768, coefficient := (-3957764854909518986425315360768) }, { argument := 197776739822357149707598299136, coefficient := (-197776739822357149707598299136) }, { argument := 39499700725233289925758503878656, coefficient := (-39499700725233289925758503878656) }, { argument := 104321796829375199845766135808, coefficient := (-104321796829375199845766135808) }, { argument := 7606797685475274988753780736, coefficient := (-7606797685475274988753780736) }, { argument := 197776739822357149707598299136, coefficient := (-197776739822357149707598299136) }, { argument := 197776739822357149707598299136, coefficient := (-197776739822357149707598299136) }, { argument := 104321796829375199845766135808, coefficient := (-104321796829375199845766135808) }, { argument := 2440695371653923946391570219008, coefficient := (-2440695371653923946391570219008) }, { argument := 195603369055078499710811504640, coefficient := (-195603369055078499710811504640) }, { argument := 3957764924444520772273470177280, coefficient := (-3957764924444520772273470177280) }, { argument := 197776739822357149707598299136, coefficient := (-197776739822357149707598299136) }, { argument := 7606797685475274988753780736, coefficient := (-7606797685475274988753780736) }, { argument := 195603369055078499710811504640, coefficient := (-195603369055078499710811504640) }, { argument := 7606797685475274988753780736, coefficient := (-7606797685475274988753780736) }, { argument := 197776739822357149707598299136, coefficient := (-197776739822357149707598299136) }] }

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

end TermShard1


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12
