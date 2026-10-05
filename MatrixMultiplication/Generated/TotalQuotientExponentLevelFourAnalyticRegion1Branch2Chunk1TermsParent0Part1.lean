import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 1, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-364774418010318192429799401586688)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    955913811, 1593291339, 11140996707, 79903483317, 62637057945, 81992463273,
    2611224945, 79903483317, 45435314043, 81992463273, 1280022468039, 1566734967,
    5570498619, 79903483317, 2611224945, 1566734967, 2611224945, 40212864153,
    45435314043, 1593291339, 60888075, 5098105845, 2549053845, 30443115,
    25818695, 2707043605, 29179224375, 1353522835, 25818695, 444595453,
    67475973, 3062634341, 1669671417, 53119383, 3062635791, 27277521,
    27277521, 923128737, 50248065, 1669671417, 923128737, 444594003,
    53119383, 50248065, 67475973, 81832563, 396318093, 81832563,
    2769386211, 13412238621, 2769386211, 1863175095, 156002038857, 78001047657,
    931559319, 150744195, 730059645, 150744195, 1059452505, 88707041703,
    44353536903, 529710201, 22867987, 2397667193
  ]
def negativeCoefficients : Array ℕ := #[
    2204187178505170299043971072, 7347759391347751547836563456, 205515114980069879828302528512, 184244888418327471981575798784, 144431222180191316958920048640, 189061748246257601968022224896,
    6021074784912662483058032640, 184244888418327471981575798784, 104766701257480327205209767936, 189061748246257601968022224896, 2951530859564187149195047600128, 115604635870323119674714226688,
    205515124775290982968074436608, 184244888418327471981575798784, 6021074784912662483058032640, 115604635870323119674714226688, 6021074784912662483058032640, 185449103375310004478187405312,
    104766701257480327205209767936, 7347759391347751547836563456, 70199171041614544188211200, 5877715861462360995366174720, 5877717988602536994998845440, 70197043901438544555540480,
    119067714745541107940065280, 12484035144451772582377553920, 134565421078743136295976960000, 12484044667583400634933575680, 119067714745541107940065280, 512583658614122718196400128,
    311178001263883928670830592, 7061953984972638504859205632, 7700000329146744873280339968, 244969915888589475762143232, 7061957328445001864715436032, 251590724426118921053011968,
    251590724426118921053011968, 4257179889631433322028597248, 231728298813530585180405760, 7700000329146744873280339968, 4257179889631433322028597248, 512581986877941038268284928,
    244969915888589475762143232, 231728298813530585180405760, 311178001263883928670830592, 188693043319589190789758976, 1827694608337905233084547072, 188693043319589190789758976,
    3192884917223574991521447936, 30926516662138764865088520192, 3192884917223574991521447936, 2148094633873405052159262720, 179858105360748246458204946432, 179858170451237632046964670464,
    2148029543384019463399538688, 173796224110147938885304320, 1683402928732281135735767040, 173796224110147938885304320, 1221465576124093068874874880, 102272255989445081319371440128,
    102272293001684143712979910656, 1221428563885030675266404352, 105459975917479267032629248, 11057288270800141430105833472
  ]
def negativeScales : Array ℕ := #[
    29, 30, 33, 36, 35, 36,
    31, 36, 35, 36, 40, 30,
    32, 36, 31, 30, 31, 35,
    35, 30, 25, 32, 31, 24,
    24, 31, 34, 30, 24, 28,
    26, 31, 30, 25, 31, 24,
    24, 29, 25, 30, 29, 28,
    25, 25, 26, 26, 28, 26,
    31, 33, 31, 30, 37, 36,
    29, 27, 29, 27, 29, 36,
    35, 28, 24, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    29832305305263379, 30569362946903501, 33375159255153258, 36217539346327529, 35866297402239781, 36254772252526504,
    31282079598522239, 36217539346327529, 35403094999483613, 36254772252526504, 40219306272501717, 30545114004357179,
    32375159323914705, 36217539346327529, 31282079598522239, 30545114004357179, 31282079598522239, 35226938044329778,
    35403094999483613, 30569362946903501, 25859656368594626, 32247314180361563, 31247314702471529, 24859612652106899,
    24621912746020716, 31334070980626907, 34764222484072990, 30334072081150045, 24621912746020716, 28727917952837923,
    26007870539640660, 31512125982622255, 30636917069451459, 25662735053621334, 31512126665664068, 24701209201481082,
    24701209201481082, 29781956615736132, 25582564704911453, 30636917069451459, 29781956615736132, 28727913247636345,
    25662735053621334, 25582564704911453, 26007870539640660, 26286171702127764, 28562083590866803, 26286171702127764,
    31366919116012127, 33642831004766990, 31366919116012127, 30795116114904183, 37182773928166852, 36182774450276818,
    29795072398417646, 27167527205629145, 29443439094366311, 27167527205629145, 29980671784813928, 36368329581322930,
    35368330103432896, 28980628068315566, 24446826039452413, 31158984274068816
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
noncomputable def negativeCeiling : ℝ := 2681242683 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2204187178505170299043971072, coefficient := (-2204187178505170299043971072) }, { argument := 7347759391347751547836563456, coefficient := (-7347759391347751547836563456) }, { argument := 205515114980069879828302528512, coefficient := (-205515114980069879828302528512) }, { argument := 184244888418327471981575798784, coefficient := (-184244888418327471981575798784) }, { argument := 144431222180191316958920048640, coefficient := (-144431222180191316958920048640) }, { argument := 189061748246257601968022224896, coefficient := (-189061748246257601968022224896) }, { argument := 6021074784912662483058032640, coefficient := (-6021074784912662483058032640) }, { argument := 184244888418327471981575798784, coefficient := (-184244888418327471981575798784) }, { argument := 104766701257480327205209767936, coefficient := (-104766701257480327205209767936) }, { argument := 189061748246257601968022224896, coefficient := (-189061748246257601968022224896) }, { argument := 2951530859564187149195047600128, coefficient := (-2951530859564187149195047600128) }, { argument := 115604635870323119674714226688, coefficient := (-115604635870323119674714226688) }, { argument := 205515124775290982968074436608, coefficient := (-205515124775290982968074436608) }, { argument := 184244888418327471981575798784, coefficient := (-184244888418327471981575798784) }, { argument := 6021074784912662483058032640, coefficient := (-6021074784912662483058032640) }, { argument := 115604635870323119674714226688, coefficient := (-115604635870323119674714226688) }, { argument := 6021074784912662483058032640, coefficient := (-6021074784912662483058032640) }, { argument := 185449103375310004478187405312, coefficient := (-185449103375310004478187405312) }, { argument := 104766701257480327205209767936, coefficient := (-104766701257480327205209767936) }, { argument := 7347759391347751547836563456, coefficient := (-7347759391347751547836563456) }, { argument := 70199171041614544188211200, coefficient := (-70199171041614544188211200) }, { argument := 5877715861462360995366174720, coefficient := (-5877715861462360995366174720) }, { argument := 5877717988602536994998845440, coefficient := (-5877717988602536994998845440) }, { argument := 70197043901438544555540480, coefficient := (-70197043901438544555540480) }, { argument := 119067714745541107940065280, coefficient := (-119067714745541107940065280) }, { argument := 12484035144451772582377553920, coefficient := (-12484035144451772582377553920) }, { argument := 134565421078743136295976960000, coefficient := (-134565421078743136295976960000) }, { argument := 12484044667583400634933575680, coefficient := (-12484044667583400634933575680) }, { argument := 119067714745541107940065280, coefficient := (-119067714745541107940065280) }, { argument := 512583658614122718196400128, coefficient := (-512583658614122718196400128) }, { argument := 311178001263883928670830592, coefficient := (-311178001263883928670830592) }, { argument := 7061953984972638504859205632, coefficient := (-7061953984972638504859205632) }, { argument := 7700000329146744873280339968, coefficient := (-7700000329146744873280339968) }, { argument := 244969915888589475762143232, coefficient := (-244969915888589475762143232) }, { argument := 7061957328445001864715436032, coefficient := (-7061957328445001864715436032) }, { argument := 251590724426118921053011968, coefficient := (-251590724426118921053011968) }, { argument := 251590724426118921053011968, coefficient := (-251590724426118921053011968) }, { argument := 4257179889631433322028597248, coefficient := (-4257179889631433322028597248) }, { argument := 231728298813530585180405760, coefficient := (-231728298813530585180405760) }, { argument := 7700000329146744873280339968, coefficient := (-7700000329146744873280339968) }, { argument := 4257179889631433322028597248, coefficient := (-4257179889631433322028597248) }, { argument := 512581986877941038268284928, coefficient := (-512581986877941038268284928) }, { argument := 244969915888589475762143232, coefficient := (-244969915888589475762143232) }, { argument := 231728298813530585180405760, coefficient := (-231728298813530585180405760) }, { argument := 311178001263883928670830592, coefficient := (-311178001263883928670830592) }, { argument := 188693043319589190789758976, coefficient := (-188693043319589190789758976) }, { argument := 1827694608337905233084547072, coefficient := (-1827694608337905233084547072) }, { argument := 188693043319589190789758976, coefficient := (-188693043319589190789758976) }, { argument := 3192884917223574991521447936, coefficient := (-3192884917223574991521447936) }, { argument := 30926516662138764865088520192, coefficient := (-30926516662138764865088520192) }, { argument := 3192884917223574991521447936, coefficient := (-3192884917223574991521447936) }, { argument := 2148094633873405052159262720, coefficient := (-2148094633873405052159262720) }, { argument := 179858105360748246458204946432, coefficient := (-179858105360748246458204946432) }, { argument := 179858170451237632046964670464, coefficient := (-179858170451237632046964670464) }, { argument := 2148029543384019463399538688, coefficient := (-2148029543384019463399538688) }, { argument := 173796224110147938885304320, coefficient := (-173796224110147938885304320) }, { argument := 1683402928732281135735767040, coefficient := (-1683402928732281135735767040) }, { argument := 173796224110147938885304320, coefficient := (-173796224110147938885304320) }, { argument := 1221465576124093068874874880, coefficient := (-1221465576124093068874874880) }, { argument := 102272255989445081319371440128, coefficient := (-102272255989445081319371440128) }, { argument := 102272293001684143712979910656, coefficient := (-102272293001684143712979910656) }, { argument := 1221428563885030675266404352, coefficient := (-1221428563885030675266404352) }, { argument := 105459975917479267032629248, coefficient := (-105459975917479267032629248) }, { argument := 11057288270800141430105833472, coefficient := (-11057288270800141430105833472) }] }

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


end Parent0

namespace Parent0

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1093755092754674496952928737165312)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    25844455875, 1198834511, 22867987, 5009014251, 24258839061, 5009014251,
    1911885555, 160080523533, 80040290733, 955913811, 2769386211, 13412238621,
    2769386211, 29847334365, 2499091485219, 1249546194819, 14923214973, 1070369327,
    112226293453, 1209687273375, 56113189531, 1070369327, 36532845, 3058863507,
    1529432307, 18265869, 291382415, 30550920685, 329308389375, 15275471995,
    291382415, 3385736457, 59246167323, 59246196381, 3385707399, 375682371,
    3385707399, 7685842371, 5453624493, 168947475, 5453624493, 3642507561,
    191220135, 3385707399, 20273697, 202502025, 5452053705, 344115975,
    304788435, 14266065135, 3883594575, 2726027775, 14266065135, 344115975,
    344115975, 147478275, 344115975, 3883594575, 147478275, 405002205,
    304788435, 796645953, 11141000487, 39951756117
  ]
def negativeCoefficients : Array ℕ := #[
    119186515812601063576436736000, 11057296705573869133798309888, 105459975917479267032629248, 5775000246860058654960254976, 55937074460446941738877059072, 5775000246860058654960254976,
    2204253970706696687509831680, 184560278049918135254497886208, 184560344842119661642963746816, 2204187178505170299043971072, 3192884917223574991521447936, 30926516662138764865088520192,
    3192884917223574991521447936, 34411633644599449561061130240, 2881256315288849359928498847744, 2881257358012963634948434034688, 34410590920485174541125943296, 4936207259879432789172420608,
    517552428417129200486566592512, 5578697885293036879013216256000, 517552823218957552036817666048, 4936207259879432789172420608, 1347824083998999248413655040, 112852144540077331111030554624,
    112852185381168710303977832448, 1347783242907620055466377216, 1343764209271106789609308160, 140891253773098576286832394240, 1518666895031529681054597120000, 140891361248441235737107496960,
    1343764209271106789609308160, 3903488370206695258463404032, 136612360744444342543105130496, 136612427747630504274623987712, 3903454868613614392703975424, 433132284427587694777860096,
    3903454868613614392703975424, 8861172950544376184854020096, 6287600956030313003816583168, 194783177076527664306585600, 6287600956030313003816583168, 4199525297769936442449985536,
    440923611510648801350123520, 3903454868613614392703975424, 186991849993466557734322176, 14942012118331733856328089600, 201145278744509907963803074560, 12695638645000068442305331200,
    11244708514142917763184721920, 526324904968431408851001016320, 143279350422143629563160166400, 201145346812995539952048537600, 526324904968431408851001016320, 12695638645000068442305331200,
    12695638645000068442305331200, 10881975981428630093404569600, 12695638645000068442305331200, 143279350422143629563160166400, 10881975981428630093404569600, 14941944049846101868082626560,
    11244708514142917763184721920, 7347762006173723996165505024, 205515184708762478450407636992, 184244955096389769413963808768
  ]
def negativeScales : Array ℕ := #[
    34, 30, 24, 32, 34, 32,
    30, 37, 36, 29, 31, 33,
    31, 34, 41, 40, 33, 29,
    36, 40, 35, 29, 25, 31,
    30, 24, 28, 34, 38, 33,
    28, 31, 35, 35, 31, 28,
    31, 32, 32, 27, 32, 31,
    27, 31, 24, 27, 32, 28,
    28, 33, 31, 31, 33, 28,
    28, 27, 28, 31, 27, 28,
    28, 29, 33, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34589135777213169, 30158985374591954, 24446826039452413, 32221879570157397, 34497791458894778, 32221879570157397,
    30832349021750443, 37220006834365827, 36220007356475793, 29832305305263379, 31366919116012127, 33642831004766990,
    31366919116012127, 34796883041099933, 41184540854341040, 40184541376451006, 33796839324613378, 29995461555151818,
    36707619767835194, 40137771270888864, 35707620868358335, 29995461555151818, 25122690772348074, 31510348586195738,
    30510349108305704, 24122647055862061, 28118338572129962, 34830496807934487, 38260648309886585, 33830497908457651,
    28118338572129962, 31656822533395024, 35786002777411928, 35786003484999009, 31656810151447122, 28484938177800071,
    31656810151447122, 32839556243863906, 32344568221504381, 27331999548001325, 32344568221504381, 31762284821272558,
    27510659202581225, 31656810151447122, 24273105858947757, 27593361093979137, 32344152627346473, 28358319627396723,
    28183232920838631, 33731868414669020, 31854745455412046, 31344153115561014, 33731868414669020, 28358319627396723,
    28358319627396723, 27135927206060274, 28358319627396723, 31854745455412046, 27135927206060274, 28593354521752480,
    28183232920838631, 29569363460311139, 33375159744641450, 35217539868437495
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
noncomputable def negativeCeiling : ℝ := 8194340589 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 119186515812601063576436736000, coefficient := (-119186515812601063576436736000) }, { argument := 11057296705573869133798309888, coefficient := (-11057296705573869133798309888) }, { argument := 105459975917479267032629248, coefficient := (-105459975917479267032629248) }, { argument := 5775000246860058654960254976, coefficient := (-5775000246860058654960254976) }, { argument := 55937074460446941738877059072, coefficient := (-55937074460446941738877059072) }, { argument := 5775000246860058654960254976, coefficient := (-5775000246860058654960254976) }, { argument := 2204253970706696687509831680, coefficient := (-2204253970706696687509831680) }, { argument := 184560278049918135254497886208, coefficient := (-184560278049918135254497886208) }, { argument := 184560344842119661642963746816, coefficient := (-184560344842119661642963746816) }, { argument := 2204187178505170299043971072, coefficient := (-2204187178505170299043971072) }, { argument := 3192884917223574991521447936, coefficient := (-3192884917223574991521447936) }, { argument := 30926516662138764865088520192, coefficient := (-30926516662138764865088520192) }, { argument := 3192884917223574991521447936, coefficient := (-3192884917223574991521447936) }, { argument := 34411633644599449561061130240, coefficient := (-34411633644599449561061130240) }, { argument := 2881256315288849359928498847744, coefficient := (-2881256315288849359928498847744) }, { argument := 2881257358012963634948434034688, coefficient := (-2881257358012963634948434034688) }, { argument := 34410590920485174541125943296, coefficient := (-34410590920485174541125943296) }, { argument := 4936207259879432789172420608, coefficient := (-4936207259879432789172420608) }, { argument := 517552428417129200486566592512, coefficient := (-517552428417129200486566592512) }, { argument := 5578697885293036879013216256000, coefficient := (-5578697885293036879013216256000) }, { argument := 517552823218957552036817666048, coefficient := (-517552823218957552036817666048) }, { argument := 4936207259879432789172420608, coefficient := (-4936207259879432789172420608) }, { argument := 1347824083998999248413655040, coefficient := (-1347824083998999248413655040) }, { argument := 112852144540077331111030554624, coefficient := (-112852144540077331111030554624) }, { argument := 112852185381168710303977832448, coefficient := (-112852185381168710303977832448) }, { argument := 1347783242907620055466377216, coefficient := (-1347783242907620055466377216) }, { argument := 1343764209271106789609308160, coefficient := (-1343764209271106789609308160) }, { argument := 140891253773098576286832394240, coefficient := (-140891253773098576286832394240) }, { argument := 1518666895031529681054597120000, coefficient := (-1518666895031529681054597120000) }, { argument := 140891361248441235737107496960, coefficient := (-140891361248441235737107496960) }, { argument := 1343764209271106789609308160, coefficient := (-1343764209271106789609308160) }, { argument := 3903488370206695258463404032, coefficient := (-3903488370206695258463404032) }, { argument := 136612360744444342543105130496, coefficient := (-136612360744444342543105130496) }, { argument := 136612427747630504274623987712, coefficient := (-136612427747630504274623987712) }, { argument := 3903454868613614392703975424, coefficient := (-3903454868613614392703975424) }, { argument := 433132284427587694777860096, coefficient := (-433132284427587694777860096) }, { argument := 3903454868613614392703975424, coefficient := (-3903454868613614392703975424) }, { argument := 8861172950544376184854020096, coefficient := (-8861172950544376184854020096) }, { argument := 6287600956030313003816583168, coefficient := (-6287600956030313003816583168) }, { argument := 194783177076527664306585600, coefficient := (-194783177076527664306585600) }, { argument := 6287600956030313003816583168, coefficient := (-6287600956030313003816583168) }, { argument := 4199525297769936442449985536, coefficient := (-4199525297769936442449985536) }, { argument := 440923611510648801350123520, coefficient := (-440923611510648801350123520) }, { argument := 3903454868613614392703975424, coefficient := (-3903454868613614392703975424) }, { argument := 186991849993466557734322176, coefficient := (-186991849993466557734322176) }, { argument := 14942012118331733856328089600, coefficient := (-14942012118331733856328089600) }, { argument := 201145278744509907963803074560, coefficient := (-201145278744509907963803074560) }, { argument := 12695638645000068442305331200, coefficient := (-12695638645000068442305331200) }, { argument := 11244708514142917763184721920, coefficient := (-11244708514142917763184721920) }, { argument := 526324904968431408851001016320, coefficient := (-526324904968431408851001016320) }, { argument := 143279350422143629563160166400, coefficient := (-143279350422143629563160166400) }, { argument := 201145346812995539952048537600, coefficient := (-201145346812995539952048537600) }, { argument := 526324904968431408851001016320, coefficient := (-526324904968431408851001016320) }, { argument := 12695638645000068442305331200, coefficient := (-12695638645000068442305331200) }, { argument := 12695638645000068442305331200, coefficient := (-12695638645000068442305331200) }, { argument := 10881975981428630093404569600, coefficient := (-10881975981428630093404569600) }, { argument := 12695638645000068442305331200, coefficient := (-12695638645000068442305331200) }, { argument := 143279350422143629563160166400, coefficient := (-143279350422143629563160166400) }, { argument := 10881975981428630093404569600, coefficient := (-10881975981428630093404569600) }, { argument := 14941944049846101868082626560, coefficient := (-14941944049846101868082626560) }, { argument := 11244708514142917763184721920, coefficient := (-11244708514142917763184721920) }, { argument := 7347762006173723996165505024, coefficient := (-7347762006173723996165505024) }, { argument := 205515184708762478450407636992, coefficient := (-205515184708762478450407636992) }, { argument := 184244955096389769413963808768, coefficient := (-184244955096389769413963808768) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1
