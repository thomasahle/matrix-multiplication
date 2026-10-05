import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 17, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-87825739239367647357463670628024320)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    28287664723, 31345790639, 3207169915705577, 71609195, 59333333, 373976344511030161,
    398965515, 102622182731693903, 1597908037, 1597908037, 1143701143, 59333333,
    1237417545, 12367930965, 24735855885, 1237417545, 746203077477, 2674686459159,
    186604980705, 7383864133843945, 5829, 7383863655105559, 5829, 33048621147,
    118459307049, 8264556255, 308463300737, 5159, 308463374207, 5159,
    13676099, 1343222656766529, 2186903305, 205227022443941785, 22882476045, 1013442995,
    51306751357710351, 1013442995, 1973546885, 37284034395, 1973546885, 22882476045,
    37284034395, 5372907302610727, 1973546885, 1973546885, 2186903305, 102629428780632819,
    143218355, 118666637, 373976312566908365, 797930835, 1603471472069053, 3195815293,
    3195815293, 2287401727, 118666637, 277497873122854827, 335, 277497854201034837,
    335, 33048621147, 118459307049, 8264556255
  ]
def negativeCoefficients : Array ℕ := #[
    260907655794041497498035421184, 289113888852856794524850061312, 115550473898284013152872259649536, 169082431166638291844186767360, 8756054471129482970502529024, 421059931446313917550327144382464,
    235507671982103335068688711680, 115542305977600902710583961321472, 235809604894900903446981902336, 235809604894900903446981902336, 168780498253840723465893576704, 8756054471129482970502529024,
    5706581191233243100930375680, 228148057232662605847792189440, 228148001477378643060672430080, 5706581191233243100930375680, 860313574827042446456811159552, 3083703536845154244624786653184,
    860563580486160994269470392320, 8313491940433490226085290311680, 440426787658354591210143744, 8313491401421986026697120546816, 440426787658354591210143744, 76204932035961801784053202944,
    273148565035235107915482267648, 76227077059380227930629079040, 711267945603392739414454042624, 779606037923983989038645248, 711268115013678626344548696064, 779606037923983989038645248,
    64583551534007072037382651904, 3024668528244673825963027464192, 80682491162569164078196981760, 115532542725611580280388106321920, 844214358749809058281622077440, 74778894248234834999304519680,
    115532533148087513244332665602048, 74778894248234834999304519680, 72811028610123391973007032320, 2751076162079797350763887329280, 72811028610123391973007032320, 844214358749809058281622077440,
    2751076162079797350763887329280, 3024677915741735863423361613824, 72811028610123391973007032320, 72811028610123391973007032320, 80682491162569164078196981760, 115550464303426205329466962477056,
    169082389845931566734791147520, 8756052331307170420194541568, 421059895480430163264492284149760, 235507614428261825094887669760, 115542296385750524408942829764608, 235809547267272417178342653952,
    235809547267272417178342653952, 168780457006920974651336163328, 8756052331307170420194541568, 78108707374512136003304671936512, 25311884348181298345410560, 78108702048493294994829525123072,
    25311884348181298345410560, 76204932035961801784053202944, 273148565035235107915482267648, 76227077059380227930629079040
  ]
def negativeScales : Array ℕ := #[
    34, 34, 51, 26, 25, 58,
    28, 56, 30, 30, 30, 25,
    30, 33, 34, 30, 39, 41,
    37, 52, 12, 52, 12, 34,
    36, 32, 38, 12, 38, 12,
    23, 50, 31, 57, 34, 29,
    55, 29, 30, 35, 30, 34,
    35, 52, 30, 30, 31, 56,
    27, 26, 58, 29, 50, 31,
    31, 31, 26, 57, 8, 57,
    8, 34, 36, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34719454029517463, 34867552670805463, 51510222213028021, 26093641513281782, 25822339492476244, 58375724629893372,
    28571688810088958, 56510120229585048, 30573537234481467, 30573537234481467, 30091062969180006, 25822339492476244,
    30204685248768119, 33525885120473931, 34525884767905154, 30204685248768119, 39440777353864320, 41282506919758973,
    37441196537681164, 52713297430451168, 12509032686306867, 52713297336912947, 12509032686306867, 34943871039203999,
    36785600596183304, 32944290223088052, 38166307899442935, 12332875731152675, 38166308243064985, 12332875731152675,
    23705153435749265, 50254619893517136, 31026242286315114, 57509998317613100, 34413524119196588, 29916617801006457,
    55509998198015221, 29916617801006457, 30878143650261978, 35117838927072467, 30878143650261978, 34413524119196588,
    35117838927072467, 52254624371123298, 30878143650261978, 30878143650261978, 31026242286315114, 56510222093232283,
    27093641160713005, 26822339139907460, 58375724506661973, 29571688457520181, 50510120109818393, 31573536881912690,
    31573536881912690, 31091062616611229, 26822339139907460, 57945254336700872, 8388017285345139, 57945254238327428,
    8388017285345139, 34943871039203999, 36785600596183304, 32944290223088052
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
noncomputable def negativeCeiling : ℝ := 73689696661 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 260907655794041497498035421184, coefficient := (-260907655794041497498035421184) }, { argument := 289113888852856794524850061312, coefficient := (-289113888852856794524850061312) }, { argument := 115550473898284013152872259649536, coefficient := (-115550473898284013152872259649536) }, { argument := 169082431166638291844186767360, coefficient := (-169082431166638291844186767360) }, { argument := 8756054471129482970502529024, coefficient := (-8756054471129482970502529024) }, { argument := 421059931446313917550327144382464, coefficient := (-421059931446313917550327144382464) }, { argument := 235507671982103335068688711680, coefficient := (-235507671982103335068688711680) }, { argument := 115542305977600902710583961321472, coefficient := (-115542305977600902710583961321472) }, { argument := 235809604894900903446981902336, coefficient := (-235809604894900903446981902336) }, { argument := 235809604894900903446981902336, coefficient := (-235809604894900903446981902336) }, { argument := 168780498253840723465893576704, coefficient := (-168780498253840723465893576704) }, { argument := 8756054471129482970502529024, coefficient := (-8756054471129482970502529024) }, { argument := 5706581191233243100930375680, coefficient := (-5706581191233243100930375680) }, { argument := 228148057232662605847792189440, coefficient := (-228148057232662605847792189440) }, { argument := 228148001477378643060672430080, coefficient := (-228148001477378643060672430080) }, { argument := 5706581191233243100930375680, coefficient := (-5706581191233243100930375680) }, { argument := 860313574827042446456811159552, coefficient := (-860313574827042446456811159552) }, { argument := 3083703536845154244624786653184, coefficient := (-3083703536845154244624786653184) }, { argument := 860563580486160994269470392320, coefficient := (-860563580486160994269470392320) }, { argument := 8313491940433490226085290311680, coefficient := (-8313491940433490226085290311680) }, { argument := 440426787658354591210143744, coefficient := (-440426787658354591210143744) }, { argument := 8313491401421986026697120546816, coefficient := (-8313491401421986026697120546816) }, { argument := 440426787658354591210143744, coefficient := (-440426787658354591210143744) }, { argument := 76204932035961801784053202944, coefficient := (-76204932035961801784053202944) }, { argument := 273148565035235107915482267648, coefficient := (-273148565035235107915482267648) }, { argument := 76227077059380227930629079040, coefficient := (-76227077059380227930629079040) }, { argument := 711267945603392739414454042624, coefficient := (-711267945603392739414454042624) }, { argument := 779606037923983989038645248, coefficient := (-779606037923983989038645248) }, { argument := 711268115013678626344548696064, coefficient := (-711268115013678626344548696064) }, { argument := 779606037923983989038645248, coefficient := (-779606037923983989038645248) }, { argument := 64583551534007072037382651904, coefficient := (-64583551534007072037382651904) }, { argument := 3024668528244673825963027464192, coefficient := (-3024668528244673825963027464192) }, { argument := 80682491162569164078196981760, coefficient := (-80682491162569164078196981760) }, { argument := 115532542725611580280388106321920, coefficient := (-115532542725611580280388106321920) }, { argument := 844214358749809058281622077440, coefficient := (-844214358749809058281622077440) }, { argument := 74778894248234834999304519680, coefficient := (-74778894248234834999304519680) }, { argument := 115532533148087513244332665602048, coefficient := (-115532533148087513244332665602048) }, { argument := 74778894248234834999304519680, coefficient := (-74778894248234834999304519680) }, { argument := 72811028610123391973007032320, coefficient := (-72811028610123391973007032320) }, { argument := 2751076162079797350763887329280, coefficient := (-2751076162079797350763887329280) }, { argument := 72811028610123391973007032320, coefficient := (-72811028610123391973007032320) }, { argument := 844214358749809058281622077440, coefficient := (-844214358749809058281622077440) }, { argument := 2751076162079797350763887329280, coefficient := (-2751076162079797350763887329280) }, { argument := 3024677915741735863423361613824, coefficient := (-3024677915741735863423361613824) }, { argument := 72811028610123391973007032320, coefficient := (-72811028610123391973007032320) }, { argument := 72811028610123391973007032320, coefficient := (-72811028610123391973007032320) }, { argument := 80682491162569164078196981760, coefficient := (-80682491162569164078196981760) }, { argument := 115550464303426205329466962477056, coefficient := (-115550464303426205329466962477056) }, { argument := 169082389845931566734791147520, coefficient := (-169082389845931566734791147520) }, { argument := 8756052331307170420194541568, coefficient := (-8756052331307170420194541568) }, { argument := 421059895480430163264492284149760, coefficient := (-421059895480430163264492284149760) }, { argument := 235507614428261825094887669760, coefficient := (-235507614428261825094887669760) }, { argument := 115542296385750524408942829764608, coefficient := (-115542296385750524408942829764608) }, { argument := 235809547267272417178342653952, coefficient := (-235809547267272417178342653952) }, { argument := 235809547267272417178342653952, coefficient := (-235809547267272417178342653952) }, { argument := 168780457006920974651336163328, coefficient := (-168780457006920974651336163328) }, { argument := 8756052331307170420194541568, coefficient := (-8756052331307170420194541568) }, { argument := 78108707374512136003304671936512, coefficient := (-78108707374512136003304671936512) }, { argument := 25311884348181298345410560, coefficient := (-25311884348181298345410560) }, { argument := 78108702048493294994829525123072, coefficient := (-78108702048493294994829525123072) }, { argument := 25311884348181298345410560, coefficient := (-25311884348181298345410560) }, { argument := 76204932035961801784053202944, coefficient := (-76204932035961801784053202944) }, { argument := 273148565035235107915482267648, coefficient := (-273148565035235107915482267648) }, { argument := 76227077059380227930629079040, coefficient := (-76227077059380227930629079040) }] }

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


end Parent3

namespace Parent3

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1823026914249181055705446566854656)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    97613501079, 201, 97613524329, 201, 516952509, 11712101005,
    335, 11712103795, 335, 1045, 201, 5829,
    5159, 335, 201, 335, 10251, 335,
    201, 164217, 10519, 5829, 10251, 335,
    10519, 335, 10251, 335, 201, 4956015911,
    49535149147, 99070274083, 4956015911, 64357841181, 230683913727, 16094135865,
    4956015911, 49535149147, 99070274083, 4956015911, 1215841377987, 4358055559329,
    304048674855, 308461301889, 10251, 308461375359, 10251, 64357841181,
    230683913727, 16094135865, 613049885395, 335, 613050031405, 335,
    2695, 3547263629, 35454735433, 70909453537, 3547263629, 746203077477,
    2674686459159, 186604980705, 97613501079, 201
  ]
def negativeCoefficients : Array ℕ := #[
    450162818135771043050255548416, 485988179485080928231882752, 450162925357470971487024316416, 485988179485080928231882752, 2441239201736968613159988363264, 27006266225583929194981621760,
    25311884348181298345410560, 27006272658885924901187747840, 25311884348181298345410560, 40426479407913199602174525440, 30374261217817558014492672, 440426787658354591210143744,
    779606037923983989038645248, 25311884348181298345410560, 485988179485080928231882752, 25311884348181298345410560, 774543661054347729369563136, 809980299141801547053137920,
    485988179485080928231882752, 12407885707478472448920256512, 794793168532892768045891584, 440426787658354591210143744, 774543661054347729369563136, 25311884348181298345410560,
    794793168532892768045891584, 25311884348181298345410560, 774543661054347729369563136, 809980299141801547053137920, 30374261217817558014492672, 5713897320965593412598235136,
    228440554741935250214263717888, 228440498915170154141519446016, 5713897320965593412598235136, 74199539087647017526578118656, 265960444902728920865074839552, 74221101347291274564033576960,
    5713897320965593412598235136, 228440554741935250214263717888, 228440498915170154141519446016, 5713897320965593412598235136, 2803539341744068391950167834624, 10048991945243649496469584478208,
    2804354045500356806500511907840, 711263336573705458640725475328, 774543661054347729369563136, 711263505983991345570820128768, 774543661054347729369563136, 74199539087647017526578118656,
    265960444902728920865074839552, 74221101347291274564033576960, 706798396268658503169102315520, 809980299141801547053137920, 706798564606727390814829281280, 809980299141801547053137920,
    52128881341782810013330309120, 4089716520383824222333435904, 163506107683408200857584402432, 163506067725454694193481908224, 4089716520383824222333435904, 860313574827042446456811159552,
    3083703536845154244624786653184, 860563580486160994269470392320, 450162818135771043050255548416, 485988179485080928231882752
  ]
def negativeScales : Array ℕ := #[
    36, 7, 36, 7, 28, 33,
    8, 33, 8, 10, 7, 12,
    12, 8, 7, 8, 13, 8,
    7, 17, 13, 12, 13, 8,
    13, 8, 13, 8, 7, 32,
    35, 36, 32, 35, 37, 33,
    32, 35, 36, 32, 40, 41,
    38, 38, 13, 38, 13, 35,
    37, 33, 39, 8, 39, 8,
    11, 31, 35, 36, 31, 39,
    41, 37, 36, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36506361651914635, 7651051691200812, 36506361995541851, 7651051691200812, 28945456518967878, 33447280849444347,
    8388017285345139, 33447281193116134, 8388017285345139, 10029287226968246, 7651051691200812, 12509032686306867,
    12332875731152675, 8388017285345139, 7651051691200812, 8388017285345139, 13323477033150425, 8388017285345139,
    7651051691200812, 17325243959324613, 13360709939349401, 12509032686306867, 13323477033150425, 8388017285345139,
    13360709939349401, 8388017285345139, 13323477033150425, 8388017285345139, 7651051691200812, 32206533673160488,
    35527733544866338, 36527733192297561, 32206533673160488, 35905396886803484, 37747126448099542, 33905816070656362,
    32206533673160488, 35527733544866338, 36527733192297561, 32206533673160488, 40145092161740178, 41986821746794262,
    38145511345557022, 38166298550721600, 13323477033150425, 38166298894345878, 13323477033150425, 35905396886803484,
    37747126448099542, 33905816070656362, 39157213518139906, 8388017285345139, 39157213861746328, 8388017285345139,
    11396069557639874, 31724059407987903, 35045259279566881, 36045258926998104, 31724059407987903, 39440777353864320,
    41282506919758973, 37441196537681164, 36506361651914635, 7651051691200812
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
noncomputable def negativeCeiling : ℝ := 1720778351 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 450162818135771043050255548416, coefficient := (-450162818135771043050255548416) }, { argument := 485988179485080928231882752, coefficient := (-485988179485080928231882752) }, { argument := 450162925357470971487024316416, coefficient := (-450162925357470971487024316416) }, { argument := 485988179485080928231882752, coefficient := (-485988179485080928231882752) }, { argument := 2441239201736968613159988363264, coefficient := (-2441239201736968613159988363264) }, { argument := 27006266225583929194981621760, coefficient := (-27006266225583929194981621760) }, { argument := 25311884348181298345410560, coefficient := (-25311884348181298345410560) }, { argument := 27006272658885924901187747840, coefficient := (-27006272658885924901187747840) }, { argument := 25311884348181298345410560, coefficient := (-25311884348181298345410560) }, { argument := 40426479407913199602174525440, coefficient := (-40426479407913199602174525440) }, { argument := 30374261217817558014492672, coefficient := (-30374261217817558014492672) }, { argument := 440426787658354591210143744, coefficient := (-440426787658354591210143744) }, { argument := 779606037923983989038645248, coefficient := (-779606037923983989038645248) }, { argument := 25311884348181298345410560, coefficient := (-25311884348181298345410560) }, { argument := 485988179485080928231882752, coefficient := (-485988179485080928231882752) }, { argument := 25311884348181298345410560, coefficient := (-25311884348181298345410560) }, { argument := 774543661054347729369563136, coefficient := (-774543661054347729369563136) }, { argument := 809980299141801547053137920, coefficient := (-809980299141801547053137920) }, { argument := 485988179485080928231882752, coefficient := (-485988179485080928231882752) }, { argument := 12407885707478472448920256512, coefficient := (-12407885707478472448920256512) }, { argument := 794793168532892768045891584, coefficient := (-794793168532892768045891584) }, { argument := 440426787658354591210143744, coefficient := (-440426787658354591210143744) }, { argument := 774543661054347729369563136, coefficient := (-774543661054347729369563136) }, { argument := 25311884348181298345410560, coefficient := (-25311884348181298345410560) }, { argument := 794793168532892768045891584, coefficient := (-794793168532892768045891584) }, { argument := 25311884348181298345410560, coefficient := (-25311884348181298345410560) }, { argument := 774543661054347729369563136, coefficient := (-774543661054347729369563136) }, { argument := 809980299141801547053137920, coefficient := (-809980299141801547053137920) }, { argument := 30374261217817558014492672, coefficient := (-30374261217817558014492672) }, { argument := 5713897320965593412598235136, coefficient := (-5713897320965593412598235136) }, { argument := 228440554741935250214263717888, coefficient := (-228440554741935250214263717888) }, { argument := 228440498915170154141519446016, coefficient := (-228440498915170154141519446016) }, { argument := 5713897320965593412598235136, coefficient := (-5713897320965593412598235136) }, { argument := 74199539087647017526578118656, coefficient := (-74199539087647017526578118656) }, { argument := 265960444902728920865074839552, coefficient := (-265960444902728920865074839552) }, { argument := 74221101347291274564033576960, coefficient := (-74221101347291274564033576960) }, { argument := 5713897320965593412598235136, coefficient := (-5713897320965593412598235136) }, { argument := 228440554741935250214263717888, coefficient := (-228440554741935250214263717888) }, { argument := 228440498915170154141519446016, coefficient := (-228440498915170154141519446016) }, { argument := 5713897320965593412598235136, coefficient := (-5713897320965593412598235136) }, { argument := 2803539341744068391950167834624, coefficient := (-2803539341744068391950167834624) }, { argument := 10048991945243649496469584478208, coefficient := (-10048991945243649496469584478208) }, { argument := 2804354045500356806500511907840, coefficient := (-2804354045500356806500511907840) }, { argument := 711263336573705458640725475328, coefficient := (-711263336573705458640725475328) }, { argument := 774543661054347729369563136, coefficient := (-774543661054347729369563136) }, { argument := 711263505983991345570820128768, coefficient := (-711263505983991345570820128768) }, { argument := 774543661054347729369563136, coefficient := (-774543661054347729369563136) }, { argument := 74199539087647017526578118656, coefficient := (-74199539087647017526578118656) }, { argument := 265960444902728920865074839552, coefficient := (-265960444902728920865074839552) }, { argument := 74221101347291274564033576960, coefficient := (-74221101347291274564033576960) }, { argument := 706798396268658503169102315520, coefficient := (-706798396268658503169102315520) }, { argument := 809980299141801547053137920, coefficient := (-809980299141801547053137920) }, { argument := 706798564606727390814829281280, coefficient := (-706798564606727390814829281280) }, { argument := 809980299141801547053137920, coefficient := (-809980299141801547053137920) }, { argument := 52128881341782810013330309120, coefficient := (-52128881341782810013330309120) }, { argument := 4089716520383824222333435904, coefficient := (-4089716520383824222333435904) }, { argument := 163506107683408200857584402432, coefficient := (-163506107683408200857584402432) }, { argument := 163506067725454694193481908224, coefficient := (-163506067725454694193481908224) }, { argument := 4089716520383824222333435904, coefficient := (-4089716520383824222333435904) }, { argument := 860313574827042446456811159552, coefficient := (-860313574827042446456811159552) }, { argument := 3083703536845154244624786653184, coefficient := (-3083703536845154244624786653184) }, { argument := 860563580486160994269470392320, coefficient := (-860563580486160994269470392320) }, { argument := 450162818135771043050255548416, coefficient := (-450162818135771043050255548416) }, { argument := 485988179485080928231882752, coefficient := (-485988179485080928231882752) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17
