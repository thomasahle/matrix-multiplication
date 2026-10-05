import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 16, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-15275065285478153880377789469687808)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    42040917, 42040917, 46585881, 3100747843969, 48400005661, 85231552692551,
    20429829287, 1997869741, 20429829287, 40795211163, 388297290023, 48400005661,
    1997869741, 539739335437299, 18978863213450253, 41883631559, 108015681389, 90380468101,
    2528448705167, 4742459054272921, 90380468101, 81562861457, 41883631559, 41883631559,
    81562861457, 2528448705167, 81562861457, 134934275648103, 108015681389, 23698805955999,
    6441574240952001, 296884902855, 218427928245684195, 93950918625, 11274110235, 296884902855,
    590011768965, 93950918625, 9105723033135, 582495695475, 25766312775698745, 296884902855,
    11274110235, 582495695475, 11274110235, 296884902855, 296884902855, 23698805955999,
    21588579, 4281767325, 4281767325, 21588579, 13660375, 8800597125,
    93598051325, 4400311825, 13660375, 1018946528973035, 9239603175, 18606670941379121,
    96677799075, 4281767325, 37213328495371387, 4281767325
  ]
def negativeCoefficients : Array ℕ := #[
    96939754565383142699433984, 96939754565383142699433984, 107419728031911050018291712, 6982263417334328636381069312, 111602814699320062435521462272, 191924394473190739312428187648,
    94215958081716271084048744448, 4606773975604423349535506432, 94215958081716271084048744448, 94067352469599999363095986176, 6994942122626224856741445632, 111602814699320062435521462272,
    4606773975604423349535506432, 303846233744077365388706316288, 10684150162001271712373261991936, 193154158061604399565909262336, 249067203816279357334988259328, 3334450728642433845137802002432,
    5830205770964743323739419049984, 10679068414821680940786183569408, 3334450728642433845137802002432, 188071153902088494314174808064, 193154158061604399565909262336, 193154158061604399565909262336,
    188071153902088494314174808064, 5830205770964743323739419049984, 188071153902088494314174808064, 303844976764152231724050284544, 249067203816279357334988259328, 213459867345125575247693611008,
    14505135675615408659239689781248, 2738279911157153595500884131840, 122963992031821597333138534563840, 1733088551365287085760053248000, 103985313081917225145603194880, 2738279911157153595500884131840,
    2720949025643500724643283599360, 1733088551365287085760053248000, 41992735599580906087966090199040, 2686287254616194982928082534400, 14505144576918564808064174653440, 2738279911157153595500884131840,
    103985313081917225145603194880, 2686287254616194982928082534400, 103985313081917225145603194880, 2738279911157153595500884131840, 2738279911157153595500884131840, 213459867345125575247693611008,
    99559747932015119529148416, 19746166506861737412447436800, 19746166506861737412447436800, 99559747932015119529148416, 503978883151800232312832000, 162342362860699068036808704000,
    1726579298590206195297104691200, 162342852160585623182665318400, 503978883151800232312832000, 286807950512088795766021160960, 21305074388982400892377497600, 10474624539775055669785633226752,
    222923827143254877629998694400, 19746166506861737412447436800, 10474620771560652442118360399872, 19746166506861737412447436800
  ]
def negativeScales : Array ℕ := #[
    25, 25, 25, 41, 35, 46,
    34, 30, 34, 35, 38, 35,
    30, 48, 54, 35, 36, 36,
    41, 52, 36, 36, 35, 35,
    36, 41, 36, 46, 36, 44,
    52, 38, 57, 36, 33, 38,
    39, 36, 43, 39, 54, 38,
    33, 39, 33, 38, 38, 44,
    24, 31, 31, 24, 23, 33,
    36, 32, 23, 49, 33, 54,
    36, 31, 55, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    25325290802039798, 25325290802039798, 25473389441029040, 41495753347912015, 35494288165115373, 46276452848096175,
    34249958097740285, 30895815382038907, 34249958097740285, 35247680757029219, 38498370682287515, 35494288165115373,
    30895815382038907, 48939256169818170, 54075243099311619, 35285667486773129, 36652449817467425, 36395291977947632,
    41201389649345368, 52074556740974090, 36395291977947632, 36247193338958493, 35285667486773129, 35285667486773129,
    36247193338958493, 41201389649345368, 36247193338958493, 46939250201527228, 36652449817467425, 44429879605538802,
    52516334731537684, 38111112775246535, 57599934944465654, 36451188216844206, 33392294527790593, 38111112775246535,
    39101952775961059, 36451188216844206, 43049910716520779, 39083456432343670, 54516335616869767, 38111112775246535,
    33392294527790593, 39083456432343670, 33392294527790593, 38111112775246535, 38111112775246535, 44429879605538802,
    24363764949854435, 31995559276577170, 31995559276577170, 24363764949854435, 23703493752838642, 33034954268650977,
    36445759442645761, 32034958616927321, 23703493752838642, 49855999770760033, 33105183745697582, 54046669473326650,
    36492465578579254, 31995559276577170, 55046668954321392, 31995559276577170
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
noncomputable def negativeCeiling : ℝ := 88180698497 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 96939754565383142699433984, coefficient := (-96939754565383142699433984) }, { argument := 96939754565383142699433984, coefficient := (-96939754565383142699433984) }, { argument := 107419728031911050018291712, coefficient := (-107419728031911050018291712) }, { argument := 6982263417334328636381069312, coefficient := (-6982263417334328636381069312) }, { argument := 111602814699320062435521462272, coefficient := (-111602814699320062435521462272) }, { argument := 191924394473190739312428187648, coefficient := (-191924394473190739312428187648) }, { argument := 94215958081716271084048744448, coefficient := (-94215958081716271084048744448) }, { argument := 4606773975604423349535506432, coefficient := (-4606773975604423349535506432) }, { argument := 94215958081716271084048744448, coefficient := (-94215958081716271084048744448) }, { argument := 94067352469599999363095986176, coefficient := (-94067352469599999363095986176) }, { argument := 6994942122626224856741445632, coefficient := (-6994942122626224856741445632) }, { argument := 111602814699320062435521462272, coefficient := (-111602814699320062435521462272) }, { argument := 4606773975604423349535506432, coefficient := (-4606773975604423349535506432) }, { argument := 303846233744077365388706316288, coefficient := (-303846233744077365388706316288) }, { argument := 10684150162001271712373261991936, coefficient := (-10684150162001271712373261991936) }, { argument := 193154158061604399565909262336, coefficient := (-193154158061604399565909262336) }, { argument := 249067203816279357334988259328, coefficient := (-249067203816279357334988259328) }, { argument := 3334450728642433845137802002432, coefficient := (-3334450728642433845137802002432) }, { argument := 5830205770964743323739419049984, coefficient := (-5830205770964743323739419049984) }, { argument := 10679068414821680940786183569408, coefficient := (-10679068414821680940786183569408) }, { argument := 3334450728642433845137802002432, coefficient := (-3334450728642433845137802002432) }, { argument := 188071153902088494314174808064, coefficient := (-188071153902088494314174808064) }, { argument := 193154158061604399565909262336, coefficient := (-193154158061604399565909262336) }, { argument := 193154158061604399565909262336, coefficient := (-193154158061604399565909262336) }, { argument := 188071153902088494314174808064, coefficient := (-188071153902088494314174808064) }, { argument := 5830205770964743323739419049984, coefficient := (-5830205770964743323739419049984) }, { argument := 188071153902088494314174808064, coefficient := (-188071153902088494314174808064) }, { argument := 303844976764152231724050284544, coefficient := (-303844976764152231724050284544) }, { argument := 249067203816279357334988259328, coefficient := (-249067203816279357334988259328) }, { argument := 213459867345125575247693611008, coefficient := (-213459867345125575247693611008) }, { argument := 14505135675615408659239689781248, coefficient := (-14505135675615408659239689781248) }, { argument := 2738279911157153595500884131840, coefficient := (-2738279911157153595500884131840) }, { argument := 122963992031821597333138534563840, coefficient := (-122963992031821597333138534563840) }, { argument := 1733088551365287085760053248000, coefficient := (-1733088551365287085760053248000) }, { argument := 103985313081917225145603194880, coefficient := (-103985313081917225145603194880) }, { argument := 2738279911157153595500884131840, coefficient := (-2738279911157153595500884131840) }, { argument := 2720949025643500724643283599360, coefficient := (-2720949025643500724643283599360) }, { argument := 1733088551365287085760053248000, coefficient := (-1733088551365287085760053248000) }, { argument := 41992735599580906087966090199040, coefficient := (-41992735599580906087966090199040) }, { argument := 2686287254616194982928082534400, coefficient := (-2686287254616194982928082534400) }, { argument := 14505144576918564808064174653440, coefficient := (-14505144576918564808064174653440) }, { argument := 2738279911157153595500884131840, coefficient := (-2738279911157153595500884131840) }, { argument := 103985313081917225145603194880, coefficient := (-103985313081917225145603194880) }, { argument := 2686287254616194982928082534400, coefficient := (-2686287254616194982928082534400) }, { argument := 103985313081917225145603194880, coefficient := (-103985313081917225145603194880) }, { argument := 2738279911157153595500884131840, coefficient := (-2738279911157153595500884131840) }, { argument := 2738279911157153595500884131840, coefficient := (-2738279911157153595500884131840) }, { argument := 213459867345125575247693611008, coefficient := (-213459867345125575247693611008) }, { argument := 99559747932015119529148416, coefficient := (-99559747932015119529148416) }, { argument := 19746166506861737412447436800, coefficient := (-19746166506861737412447436800) }, { argument := 19746166506861737412447436800, coefficient := (-19746166506861737412447436800) }, { argument := 99559747932015119529148416, coefficient := (-99559747932015119529148416) }, { argument := 503978883151800232312832000, coefficient := (-503978883151800232312832000) }, { argument := 162342362860699068036808704000, coefficient := (-162342362860699068036808704000) }, { argument := 1726579298590206195297104691200, coefficient := (-1726579298590206195297104691200) }, { argument := 162342852160585623182665318400, coefficient := (-162342852160585623182665318400) }, { argument := 503978883151800232312832000, coefficient := (-503978883151800232312832000) }, { argument := 286807950512088795766021160960, coefficient := (-286807950512088795766021160960) }, { argument := 21305074388982400892377497600, coefficient := (-21305074388982400892377497600) }, { argument := 10474624539775055669785633226752, coefficient := (-10474624539775055669785633226752) }, { argument := 222923827143254877629998694400, coefficient := (-222923827143254877629998694400) }, { argument := 19746166506861737412447436800, coefficient := (-19746166506861737412447436800) }, { argument := 10474620771560652442118360399872, coefficient := (-10474620771560652442118360399872) }, { argument := 19746166506861737412447436800, coefficient := (-19746166506861737412447436800) }] }

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


end Parent1

namespace Parent1

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4030310185406908504319481272598528)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    8338178475, 157523966325, 8338178475, 96677799075, 157523966325, 127368873929415,
    8338178475, 8338178475, 9239603175, 1639245, 1056071655, 11231766159,
    528037419, 1639245, 33755115, 1321005077, 1321005077, 33755115,
    808153428743, 93548316769687, 25860911980937, 42040917, 8338178475, 8338178475,
    42040917, 794232459, 157523966325, 157523966325, 794232459, 43166785,
    27809886915, 295769842187, 13904985367, 43166785, 42040917, 8338178475,
    8338178475, 42040917, 85787155, 55267749945, 587795762321, 27633958261,
    85787155, 87052665, 3406802567, 3406802567, 87052665, 487447389,
    96677799075, 96677799075, 487447389, 13660375, 8800597125, 93598051325,
    4400311825, 13660375, 794232459, 157523966325, 157523966325, 794232459,
    1323963545, 852953873355, 9071523134419, 426478222079
  ]
def negativeCoefficients : Array ℕ := #[
    19226530546154849585804083200, 726451073068229181647408332800, 19226530546154849585804083200, 222923827143254877629998694400, 726451073068229181647408332800, 286809206583556538321778769920,
    19226530546154849585804083200, 19226530546154849585804083200, 21305074388982400892377497600, 30238732989108013938769920, 9740541771641944082208522240, 103594757915412371717826281472,
    9740571129635137390959919104, 30238732989108013938769920, 4981375740669075131172126720, 194945940603919839265036435456, 194945940603919839265036435456, 4981375740669075131172126720,
    7279198961090326983193133056, 26331510284068718454790684672, 7279199597550566797236764672, 96939754565383142699433984, 19226530546154849585804083200, 19226530546154849585804083200,
    96939754565383142699433984, 3662750726551503607940775936, 726451073068229181647408332800, 726451073068229181647408332800, 3662750726551503607940775936, 796286635379844367054274560,
    256500933319904527498157752320, 2727995291772525788569425412096, 256501706413725284628611203072, 796286635379844367054274560, 96939754565383142699433984, 19226530546154849585804083200,
    19226530546154849585804083200, 96939754565383142699433984, 791246846548326364731146240, 254877509691297536817789665280, 2710729498786623726616454365184, 254878277892119428396784549888,
    791246846548326364731146240, 6423352928757491616511426560, 251377660252422950631231193088, 251377660252422950631231193088, 6423352928757491616511426560, 1123977154285118059947491328,
    222923827143254877629998694400, 222923827143254877629998694400, 1123977154285118059947491328, 503978883151800232312832000, 162342362860699068036808704000, 1726579298590206195297104691200,
    162342852160585623182665318400, 503978883151800232312832000, 3662750726551503607940775936, 726451073068229181647408332800, 726451073068229181647408332800, 3662750726551503607940775936,
    12211408338768119628939919360, 3933555452114738418531874897920, 41835016404840696112048846667776, 3933567307850989649715980664832
  ]
def negativeScales : Array ℕ := #[
    32, 37, 32, 36, 37, 46,
    32, 32, 33, 20, 29, 33,
    28, 20, 25, 30, 30, 25,
    39, 46, 44, 25, 32, 32,
    25, 29, 37, 37, 29, 25,
    34, 38, 33, 25, 25, 32,
    32, 25, 26, 35, 39, 34,
    26, 26, 31, 31, 26, 28,
    36, 36, 28, 23, 33, 36,
    32, 23, 29, 37, 37, 29,
    30, 39, 43, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32957085118451481, 37196780386454935, 32957085118451481, 36492465578579254, 37196780386454935, 46856006089009485,
    32957085118451481, 32957085118451481, 33105183745697582, 20644600063725062, 29976060595677288, 33386865753592156,
    28976064943954778, 20644600063725062, 25008602798256405, 30298988865270963, 30298988865270963, 25008602798256405,
    39555838259850386, 46410776928585187, 44555838385993111, 25325290802039798, 32957085118451481, 32957085118451481,
    25325290802039798, 29564986081788365, 37196780386454935, 37196780386454935, 29564986081788365, 25363418311162450,
    34694878827117496, 38105684001048099, 33694883175393847, 25363418311162450, 25325290802039798, 32957085118451481,
    32957085118451481, 25325290802039798, 26354258311876974, 35685718827819420, 39096524001762623, 34685723176095770,
    26354258311876974, 26375385128928030, 31665771195974250, 31665771195974250, 26375385128928030, 28860671276030903,
    36492465578579254, 36492465578579254, 28860671276030903, 23703493752838642, 33034954268650977, 36445759442645761,
    32034958616927321, 23703493752838642, 29564986081788365, 37196780386454935, 37196780386454935, 29564986081788365,
    30302216252436693, 39633676768341585, 43044481942322343, 38633681116617930
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
noncomputable def negativeCeiling : ℝ := 16060201273 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 19226530546154849585804083200, coefficient := (-19226530546154849585804083200) }, { argument := 726451073068229181647408332800, coefficient := (-726451073068229181647408332800) }, { argument := 19226530546154849585804083200, coefficient := (-19226530546154849585804083200) }, { argument := 222923827143254877629998694400, coefficient := (-222923827143254877629998694400) }, { argument := 726451073068229181647408332800, coefficient := (-726451073068229181647408332800) }, { argument := 286809206583556538321778769920, coefficient := (-286809206583556538321778769920) }, { argument := 19226530546154849585804083200, coefficient := (-19226530546154849585804083200) }, { argument := 19226530546154849585804083200, coefficient := (-19226530546154849585804083200) }, { argument := 21305074388982400892377497600, coefficient := (-21305074388982400892377497600) }, { argument := 30238732989108013938769920, coefficient := (-30238732989108013938769920) }, { argument := 9740541771641944082208522240, coefficient := (-9740541771641944082208522240) }, { argument := 103594757915412371717826281472, coefficient := (-103594757915412371717826281472) }, { argument := 9740571129635137390959919104, coefficient := (-9740571129635137390959919104) }, { argument := 30238732989108013938769920, coefficient := (-30238732989108013938769920) }, { argument := 4981375740669075131172126720, coefficient := (-4981375740669075131172126720) }, { argument := 194945940603919839265036435456, coefficient := (-194945940603919839265036435456) }, { argument := 194945940603919839265036435456, coefficient := (-194945940603919839265036435456) }, { argument := 4981375740669075131172126720, coefficient := (-4981375740669075131172126720) }, { argument := 7279198961090326983193133056, coefficient := (-7279198961090326983193133056) }, { argument := 26331510284068718454790684672, coefficient := (-26331510284068718454790684672) }, { argument := 7279199597550566797236764672, coefficient := (-7279199597550566797236764672) }, { argument := 96939754565383142699433984, coefficient := (-96939754565383142699433984) }, { argument := 19226530546154849585804083200, coefficient := (-19226530546154849585804083200) }, { argument := 19226530546154849585804083200, coefficient := (-19226530546154849585804083200) }, { argument := 96939754565383142699433984, coefficient := (-96939754565383142699433984) }, { argument := 3662750726551503607940775936, coefficient := (-3662750726551503607940775936) }, { argument := 726451073068229181647408332800, coefficient := (-726451073068229181647408332800) }, { argument := 726451073068229181647408332800, coefficient := (-726451073068229181647408332800) }, { argument := 3662750726551503607940775936, coefficient := (-3662750726551503607940775936) }, { argument := 796286635379844367054274560, coefficient := (-796286635379844367054274560) }, { argument := 256500933319904527498157752320, coefficient := (-256500933319904527498157752320) }, { argument := 2727995291772525788569425412096, coefficient := (-2727995291772525788569425412096) }, { argument := 256501706413725284628611203072, coefficient := (-256501706413725284628611203072) }, { argument := 796286635379844367054274560, coefficient := (-796286635379844367054274560) }, { argument := 96939754565383142699433984, coefficient := (-96939754565383142699433984) }, { argument := 19226530546154849585804083200, coefficient := (-19226530546154849585804083200) }, { argument := 19226530546154849585804083200, coefficient := (-19226530546154849585804083200) }, { argument := 96939754565383142699433984, coefficient := (-96939754565383142699433984) }, { argument := 791246846548326364731146240, coefficient := (-791246846548326364731146240) }, { argument := 254877509691297536817789665280, coefficient := (-254877509691297536817789665280) }, { argument := 2710729498786623726616454365184, coefficient := (-2710729498786623726616454365184) }, { argument := 254878277892119428396784549888, coefficient := (-254878277892119428396784549888) }, { argument := 791246846548326364731146240, coefficient := (-791246846548326364731146240) }, { argument := 6423352928757491616511426560, coefficient := (-6423352928757491616511426560) }, { argument := 251377660252422950631231193088, coefficient := (-251377660252422950631231193088) }, { argument := 251377660252422950631231193088, coefficient := (-251377660252422950631231193088) }, { argument := 6423352928757491616511426560, coefficient := (-6423352928757491616511426560) }, { argument := 1123977154285118059947491328, coefficient := (-1123977154285118059947491328) }, { argument := 222923827143254877629998694400, coefficient := (-222923827143254877629998694400) }, { argument := 222923827143254877629998694400, coefficient := (-222923827143254877629998694400) }, { argument := 1123977154285118059947491328, coefficient := (-1123977154285118059947491328) }, { argument := 503978883151800232312832000, coefficient := (-503978883151800232312832000) }, { argument := 162342362860699068036808704000, coefficient := (-162342362860699068036808704000) }, { argument := 1726579298590206195297104691200, coefficient := (-1726579298590206195297104691200) }, { argument := 162342852160585623182665318400, coefficient := (-162342852160585623182665318400) }, { argument := 503978883151800232312832000, coefficient := (-503978883151800232312832000) }, { argument := 3662750726551503607940775936, coefficient := (-3662750726551503607940775936) }, { argument := 726451073068229181647408332800, coefficient := (-726451073068229181647408332800) }, { argument := 726451073068229181647408332800, coefficient := (-726451073068229181647408332800) }, { argument := 3662750726551503607940775936, coefficient := (-3662750726551503607940775936) }, { argument := 12211408338768119628939919360, coefficient := (-12211408338768119628939919360) }, { argument := 3933555452114738418531874897920, coefficient := (-3933555452114738418531874897920) }, { argument := 41835016404840696112048846667776, coefficient := (-41835016404840696112048846667776) }, { argument := 3933567307850989649715980664832, coefficient := (-3933567307850989649715980664832) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16
