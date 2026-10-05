import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 16, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent0

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-27049872613875287813622019085303808)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    67958549279907, 7350969907925013, 1206433890293, 556739024528663409, 381782876675, 45813945201,
    1206433890293, 2397596465519, 381782876675, 37002396407341, 2367053835385, 58807848779538871,
    1206433890293, 45813945201, 2367053835385, 45813945201, 1206433890293, 1206433890293,
    67958549279907, 27495, 20475, 21645, 1755, 376155,
    680355, 20475, 376155, 11115, 11115, 21645,
    21645, 680355, 21645, 27495, 1755, 165931623,
    6798249315, 139981217805, 6798249315, 165931623, 769537429711335, 2577905955,
    7342573226965245, 26973698895, 1194639345, 29370289403091555, 1194639345, 2326402935,
    43950152745, 2326402935, 26973698895, 43950152745, 384769639975905, 2326402935,
    2326402935, 2577905955, 7348953, 301087965, 6199634355, 301087965,
    7348953, 3818241825, 597724343075, 149431140575
  ]
def negativeCoefficients : Array ℕ := #[
    306058097213628654468697423872, 33105825338142817837776736616448, 2781847152010594637480445607936, 313416207926237745151590015172608, 1760662754437085213595218739200, 105639765266225112815713124352,
    2781847152010594637480445607936, 2764240524466223785344493420544, 1760662754437085213595218739200, 42660858540010574725412150050816, 2729027269377482081072589045760, 33105875731248967176128143818752,
    2781847152010594637480445607936, 105639765266225112815713124352, 2729027269377482081072589045760, 105639765266225112815713124352, 2781847152010594637480445607936, 2781847152010594637480445607936,
    306058097213628654468697423872, 519365865786003580602286080, 386761814947023943001702400, 408862490086853882601799680, 530416203355918550402334720, 7105367057455325581431275520,
    12851542593811109877456568320, 386761814947023943001702400, 7105367057455325581431275520, 419912827656768852401848320, 419912827656768852401848320, 408862490086853882601799680,
    408862490086853882601799680, 12851542593811109877456568320, 408862490086853882601799680, 519365865786003580602286080, 530416203355918550402334720, 1530449091608128765122576384,
    250811130526152537564858286080, 2582197699975029719068185722880, 250811130526152537564858286080, 1530449091608128765122576384, 866422120423904390807593943040, 23776985698988406025633136640,
    33068010048901257734261330411520, 248788460118683565487722332160, 22037206257599010462781931520, 33068006102881688621884448440320, 22037206257599010462781931520, 21457279777135878608498196480,
    810737219687458332288661585920, 21457279777135878608498196480, 248788460118683565487722332160, 810737219687458332288661585920, 866424203609482829759973949440, 21457279777135878608498196480,
    21457279777135878608498196480, 23776985698988406025633136640, 135564255200720030477058048, 22216370536116075588495605760, 228726136594524776980398735360, 22216370536116075588495605760,
    135564255200720030477058048, 70434129757308692882207539200, 2756516995832672779506601164800, 2756518006829540169250714419200
  ]
def negativeScales : Array ℕ := #[
    45, 52, 40, 58, 38, 35,
    40, 41, 38, 45, 41, 55,
    40, 35, 41, 35, 40, 40,
    45, 14, 14, 14, 10, 18,
    19, 14, 18, 13, 13, 14,
    14, 19, 14, 14, 10, 27,
    32, 37, 32, 27, 49, 31,
    52, 34, 30, 54, 30, 31,
    35, 31, 34, 35, 48, 31,
    31, 31, 22, 28, 32, 28,
    22, 31, 39, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    45949720299360625, 52706856039199783, 40133886000112010, 58949778835685668, 38473961441709742, 35415067752656075,
    40133886000112010, 41124726000826534, 38473961441709742, 45072683941386253, 41106229657209145, 55706858235243180,
    40133886000112010, 35415067752656075, 41106229657209145, 35415067752656075, 40133886000112010, 40133886000112010,
    45949720299360625, 14746881666358438, 14321575831415734, 14401746180099724, 10777255315595305, 18520967741799253,
    19375928195943988, 14321575831415734, 18520967741799253, 13440220327914385, 13440220327914385, 14401746180099724,
    14401746180099724, 19375928195943988, 14401746180099724, 14746881666358438, 10777255315595305, 27306013618253934,
    32662516125415289, 37026442308092716, 32662516125415289, 27306013618253934, 49450984828265304, 31263552487456989,
    52705207171910042, 34650834320360214, 30153927996282491, 54705206999752624, 30153927996282491, 31115453848467855,
    35355149128214343, 31115453848467855, 34650834320360214, 35355149128214343, 48450988297010873, 31115453848467855,
    31115453848467855, 31263552487456989, 22809107294974936, 28165609801330126, 32529535984037463, 28165609801330126,
    22809107294974936, 31830261332630486, 39120689343289482, 37120689872420956
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
noncomputable def negativeCeiling : ℝ := 35039435343 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 306058097213628654468697423872, coefficient := (-306058097213628654468697423872) }, { argument := 33105825338142817837776736616448, coefficient := (-33105825338142817837776736616448) }, { argument := 2781847152010594637480445607936, coefficient := (-2781847152010594637480445607936) }, { argument := 313416207926237745151590015172608, coefficient := (-313416207926237745151590015172608) }, { argument := 1760662754437085213595218739200, coefficient := (-1760662754437085213595218739200) }, { argument := 105639765266225112815713124352, coefficient := (-105639765266225112815713124352) }, { argument := 2781847152010594637480445607936, coefficient := (-2781847152010594637480445607936) }, { argument := 2764240524466223785344493420544, coefficient := (-2764240524466223785344493420544) }, { argument := 1760662754437085213595218739200, coefficient := (-1760662754437085213595218739200) }, { argument := 42660858540010574725412150050816, coefficient := (-42660858540010574725412150050816) }, { argument := 2729027269377482081072589045760, coefficient := (-2729027269377482081072589045760) }, { argument := 33105875731248967176128143818752, coefficient := (-33105875731248967176128143818752) }, { argument := 2781847152010594637480445607936, coefficient := (-2781847152010594637480445607936) }, { argument := 105639765266225112815713124352, coefficient := (-105639765266225112815713124352) }, { argument := 2729027269377482081072589045760, coefficient := (-2729027269377482081072589045760) }, { argument := 105639765266225112815713124352, coefficient := (-105639765266225112815713124352) }, { argument := 2781847152010594637480445607936, coefficient := (-2781847152010594637480445607936) }, { argument := 2781847152010594637480445607936, coefficient := (-2781847152010594637480445607936) }, { argument := 306058097213628654468697423872, coefficient := (-306058097213628654468697423872) }, { argument := 519365865786003580602286080, coefficient := (-519365865786003580602286080) }, { argument := 386761814947023943001702400, coefficient := (-386761814947023943001702400) }, { argument := 408862490086853882601799680, coefficient := (-408862490086853882601799680) }, { argument := 530416203355918550402334720, coefficient := (-530416203355918550402334720) }, { argument := 7105367057455325581431275520, coefficient := (-7105367057455325581431275520) }, { argument := 12851542593811109877456568320, coefficient := (-12851542593811109877456568320) }, { argument := 386761814947023943001702400, coefficient := (-386761814947023943001702400) }, { argument := 7105367057455325581431275520, coefficient := (-7105367057455325581431275520) }, { argument := 419912827656768852401848320, coefficient := (-419912827656768852401848320) }, { argument := 419912827656768852401848320, coefficient := (-419912827656768852401848320) }, { argument := 408862490086853882601799680, coefficient := (-408862490086853882601799680) }, { argument := 408862490086853882601799680, coefficient := (-408862490086853882601799680) }, { argument := 12851542593811109877456568320, coefficient := (-12851542593811109877456568320) }, { argument := 408862490086853882601799680, coefficient := (-408862490086853882601799680) }, { argument := 519365865786003580602286080, coefficient := (-519365865786003580602286080) }, { argument := 530416203355918550402334720, coefficient := (-530416203355918550402334720) }, { argument := 1530449091608128765122576384, coefficient := (-1530449091608128765122576384) }, { argument := 250811130526152537564858286080, coefficient := (-250811130526152537564858286080) }, { argument := 2582197699975029719068185722880, coefficient := (-2582197699975029719068185722880) }, { argument := 250811130526152537564858286080, coefficient := (-250811130526152537564858286080) }, { argument := 1530449091608128765122576384, coefficient := (-1530449091608128765122576384) }, { argument := 866422120423904390807593943040, coefficient := (-866422120423904390807593943040) }, { argument := 23776985698988406025633136640, coefficient := (-23776985698988406025633136640) }, { argument := 33068010048901257734261330411520, coefficient := (-33068010048901257734261330411520) }, { argument := 248788460118683565487722332160, coefficient := (-248788460118683565487722332160) }, { argument := 22037206257599010462781931520, coefficient := (-22037206257599010462781931520) }, { argument := 33068006102881688621884448440320, coefficient := (-33068006102881688621884448440320) }, { argument := 22037206257599010462781931520, coefficient := (-22037206257599010462781931520) }, { argument := 21457279777135878608498196480, coefficient := (-21457279777135878608498196480) }, { argument := 810737219687458332288661585920, coefficient := (-810737219687458332288661585920) }, { argument := 21457279777135878608498196480, coefficient := (-21457279777135878608498196480) }, { argument := 248788460118683565487722332160, coefficient := (-248788460118683565487722332160) }, { argument := 810737219687458332288661585920, coefficient := (-810737219687458332288661585920) }, { argument := 866424203609482829759973949440, coefficient := (-866424203609482829759973949440) }, { argument := 21457279777135878608498196480, coefficient := (-21457279777135878608498196480) }, { argument := 21457279777135878608498196480, coefficient := (-21457279777135878608498196480) }, { argument := 23776985698988406025633136640, coefficient := (-23776985698988406025633136640) }, { argument := 135564255200720030477058048, coefficient := (-135564255200720030477058048) }, { argument := 22216370536116075588495605760, coefficient := (-22216370536116075588495605760) }, { argument := 228726136594524776980398735360, coefficient := (-228726136594524776980398735360) }, { argument := 22216370536116075588495605760, coefficient := (-22216370536116075588495605760) }, { argument := 135564255200720030477058048, coefficient := (-135564255200720030477058048) }, { argument := 70434129757308692882207539200, coefficient := (-70434129757308692882207539200) }, { argument := 2756516995832672779506601164800, coefficient := (-2756516995832672779506601164800) }, { argument := 2756518006829540169250714419200, coefficient := (-2756518006829540169250714419200) }] }

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
def constantNumerator : ℤ := (-56973779360728248274229466205519872)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    15273186525, 48829435714775, 4935, 4089, 1439488934644989, 27495,
    390577313516619, 110121, 110121, 78819, 4089, 96939974991393,
    5094960221250015, 207444475, 534989161, 447644057, 12523219555, 5093530015711813,
    447644057, 403976125, 207445819, 207444475, 403973437, 12523219555,
    403973437, 96939462409659, 534989161, 135917109513471, 29403876119686527, 301608583193,
    556738938914250711, 95445754175, 11453490501, 301608583193, 599399336219, 95445754175,
    9250602494641, 591763675885, 58807841755487539, 301608583193, 11453490501, 591763675885,
    11453490501, 301608583193, 301608583193, 135917109513471, 14607009374348865, 53081079885,
    556268252346448005, 555409348065, 24598549215, 556268166985473075, 24598549215, 47902437945,
    904967679015, 47902437945, 555409348065, 904967679015, 14607037918938375, 47902437945,
    47902437945, 53081079885, 7348953, 301087965
  ]
def negativeCoefficients : Array ℕ := #[
    70435140754176082626320793600, 109954114244886139501753139200, 372878057487387186073436160, 19309756548453979278802944, 405180114354445295634333302784, 519365865786003580602286080,
    109937740225800919940610392064, 520031719460088200577417216, 520031719460088200577417216, 372212203813302566098305024, 19309756548453979278802944, 109144708812135678996205535232,
    5736415238472266852469162639360, 61226802237280627799464345600, 78950465081404761413840273408, 1056969645516294492804754702336, 1848101008879678545502184407040, 5734804970190039415748728717312,
    1056969645516294492804754702336, 59616353518111192298553344000, 61227198916065188849662296064, 61226802237280627799464345600, 59615956839326631248355393536, 1848101008879678545502184407040,
    59615956839326631248355393536, 109144131696409119165530505216, 78950465081404761413840273408, 306058121879071446240809975808, 33105821383967117210241202126848, 2781848172297703511346531794944,
    313416159729608104619507378552832, 1760663400188419943890209996800, 105639804011305196633412599808, 2781848172297703511346531794944, 2764241538295819311907629694976, 1760663400188419943890209996800,
    42660874186565415240459788222464, 2729028270292050913029825495040, 33105871777059596997823633031168, 2781848172297703511346531794944, 105639804011305196633412599808, 2729028270292050913029825495040,
    105639804011305196633412599808, 2781848172297703511346531794944, 2781848172297703511346531794944, 306058121879071446240809975808, 8223015246914361290879014010880, 244793273948681759404106711040,
    313151186748187534064280466882560, 2561373524975231092301506805760, 226881570976826996520879390720, 313151138694230673222999107174400, 226881570976826996520879390720, 220911003319542075559803617280,
    8346853584884319503583931269120, 220911003319542075559803617280, 2561373524975231092301506805760, 8346853584884319503583931269120, 8223031316089696375850139648000, 220911003319542075559803617280,
    220911003319542075559803617280, 244793273948681759404106711040, 135564255200720030477058048, 22216370536116075588495605760
  ]
def negativeScales : Array ℕ := #[
    33, 45, 12, 11, 50, 14,
    48, 16, 16, 16, 11, 46,
    52, 27, 28, 28, 33, 52,
    28, 28, 27, 27, 28, 33,
    28, 46, 28, 46, 54, 38,
    58, 36, 33, 38, 39, 36,
    43, 39, 55, 38, 33, 39,
    33, 38, 38, 46, 53, 35,
    58, 39, 34, 58, 34, 35,
    39, 35, 39, 39, 53, 35,
    35, 35, 22, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33830282040627275, 45472816339461232, 12268834369343761, 11997532370288072, 50354478122254051, 14746881666358438,
    48472601481878314, 16748730090759493, 16748730090759493, 16266255825241984, 11997532370288072, 46462156943853198,
    52177992305946988, 27628149992622093, 28994934443419028, 28737776792205819, 33543886456745744, 52177587270381761,
    28737776792205819, 28589694791283398, 27628159339585200, 27628149992622093, 28589685191762703, 33543886456745744,
    28589685191762703, 46462149315410124, 28994934443419028, 46949720415628474, 54706855866883582, 38133886529243483,
    58949778613830338, 36473961970841216, 33415068281787549, 38133886529243483, 39124726529958007, 36473961970841216,
    43072684470517727, 39106230186340618, 55706858062926646, 38133886529243483, 33415068281787549, 39106230186340618,
    33415068281787549, 38133886529243483, 38133886529243483, 46949720415628474, 53697510350586424, 35627478670175504,
    58948558392899203, 39014760503045081, 34517854178989608, 58948558171513414, 34517854178989608, 35479380031174619,
    39719075311033633, 35479380031174619, 39014760503045081, 39719075311033633, 53697513169856029, 35479380031174619,
    35479380031174619, 35627478670175504, 22809107294974936, 28165609801330126
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
noncomputable def negativeCeiling : ℝ := 77711897701 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 70435140754176082626320793600, coefficient := (-70435140754176082626320793600) }, { argument := 109954114244886139501753139200, coefficient := (-109954114244886139501753139200) }, { argument := 372878057487387186073436160, coefficient := (-372878057487387186073436160) }, { argument := 19309756548453979278802944, coefficient := (-19309756548453979278802944) }, { argument := 405180114354445295634333302784, coefficient := (-405180114354445295634333302784) }, { argument := 519365865786003580602286080, coefficient := (-519365865786003580602286080) }, { argument := 109937740225800919940610392064, coefficient := (-109937740225800919940610392064) }, { argument := 520031719460088200577417216, coefficient := (-520031719460088200577417216) }, { argument := 520031719460088200577417216, coefficient := (-520031719460088200577417216) }, { argument := 372212203813302566098305024, coefficient := (-372212203813302566098305024) }, { argument := 19309756548453979278802944, coefficient := (-19309756548453979278802944) }, { argument := 109144708812135678996205535232, coefficient := (-109144708812135678996205535232) }, { argument := 5736415238472266852469162639360, coefficient := (-5736415238472266852469162639360) }, { argument := 61226802237280627799464345600, coefficient := (-61226802237280627799464345600) }, { argument := 78950465081404761413840273408, coefficient := (-78950465081404761413840273408) }, { argument := 1056969645516294492804754702336, coefficient := (-1056969645516294492804754702336) }, { argument := 1848101008879678545502184407040, coefficient := (-1848101008879678545502184407040) }, { argument := 5734804970190039415748728717312, coefficient := (-5734804970190039415748728717312) }, { argument := 1056969645516294492804754702336, coefficient := (-1056969645516294492804754702336) }, { argument := 59616353518111192298553344000, coefficient := (-59616353518111192298553344000) }, { argument := 61227198916065188849662296064, coefficient := (-61227198916065188849662296064) }, { argument := 61226802237280627799464345600, coefficient := (-61226802237280627799464345600) }, { argument := 59615956839326631248355393536, coefficient := (-59615956839326631248355393536) }, { argument := 1848101008879678545502184407040, coefficient := (-1848101008879678545502184407040) }, { argument := 59615956839326631248355393536, coefficient := (-59615956839326631248355393536) }, { argument := 109144131696409119165530505216, coefficient := (-109144131696409119165530505216) }, { argument := 78950465081404761413840273408, coefficient := (-78950465081404761413840273408) }, { argument := 306058121879071446240809975808, coefficient := (-306058121879071446240809975808) }, { argument := 33105821383967117210241202126848, coefficient := (-33105821383967117210241202126848) }, { argument := 2781848172297703511346531794944, coefficient := (-2781848172297703511346531794944) }, { argument := 313416159729608104619507378552832, coefficient := (-313416159729608104619507378552832) }, { argument := 1760663400188419943890209996800, coefficient := (-1760663400188419943890209996800) }, { argument := 105639804011305196633412599808, coefficient := (-105639804011305196633412599808) }, { argument := 2781848172297703511346531794944, coefficient := (-2781848172297703511346531794944) }, { argument := 2764241538295819311907629694976, coefficient := (-2764241538295819311907629694976) }, { argument := 1760663400188419943890209996800, coefficient := (-1760663400188419943890209996800) }, { argument := 42660874186565415240459788222464, coefficient := (-42660874186565415240459788222464) }, { argument := 2729028270292050913029825495040, coefficient := (-2729028270292050913029825495040) }, { argument := 33105871777059596997823633031168, coefficient := (-33105871777059596997823633031168) }, { argument := 2781848172297703511346531794944, coefficient := (-2781848172297703511346531794944) }, { argument := 105639804011305196633412599808, coefficient := (-105639804011305196633412599808) }, { argument := 2729028270292050913029825495040, coefficient := (-2729028270292050913029825495040) }, { argument := 105639804011305196633412599808, coefficient := (-105639804011305196633412599808) }, { argument := 2781848172297703511346531794944, coefficient := (-2781848172297703511346531794944) }, { argument := 2781848172297703511346531794944, coefficient := (-2781848172297703511346531794944) }, { argument := 306058121879071446240809975808, coefficient := (-306058121879071446240809975808) }, { argument := 8223015246914361290879014010880, coefficient := (-8223015246914361290879014010880) }, { argument := 244793273948681759404106711040, coefficient := (-244793273948681759404106711040) }, { argument := 313151186748187534064280466882560, coefficient := (-313151186748187534064280466882560) }, { argument := 2561373524975231092301506805760, coefficient := (-2561373524975231092301506805760) }, { argument := 226881570976826996520879390720, coefficient := (-226881570976826996520879390720) }, { argument := 313151138694230673222999107174400, coefficient := (-313151138694230673222999107174400) }, { argument := 226881570976826996520879390720, coefficient := (-226881570976826996520879390720) }, { argument := 220911003319542075559803617280, coefficient := (-220911003319542075559803617280) }, { argument := 8346853584884319503583931269120, coefficient := (-8346853584884319503583931269120) }, { argument := 220911003319542075559803617280, coefficient := (-220911003319542075559803617280) }, { argument := 2561373524975231092301506805760, coefficient := (-2561373524975231092301506805760) }, { argument := 8346853584884319503583931269120, coefficient := (-8346853584884319503583931269120) }, { argument := 8223031316089696375850139648000, coefficient := (-8223031316089696375850139648000) }, { argument := 220911003319542075559803617280, coefficient := (-220911003319542075559803617280) }, { argument := 220911003319542075559803617280, coefficient := (-220911003319542075559803617280) }, { argument := 244793273948681759404106711040, coefficient := (-244793273948681759404106711040) }, { argument := 135564255200720030477058048, coefficient := (-135564255200720030477058048) }, { argument := 22216370536116075588495605760, coefficient := (-22216370536116075588495605760) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16
