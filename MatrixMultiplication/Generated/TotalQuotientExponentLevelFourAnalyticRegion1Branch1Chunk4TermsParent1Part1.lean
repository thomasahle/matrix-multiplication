import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 4, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4

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
def constantNumerator : ℤ := (-9084214802966473985511884247269376)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    29078481555, 113082983825, 4571655, 2945255445, 31324030221, 1472632161,
    4571655, 8193740565, 1282684130815, 320671150315, 32775432705, 92729457310965,
    1828467135, 47445255, 678818326188205, 2945255445, 185491446642025, 2945255445,
    3069343035, 1828467135, 91240875, 726027645, 113655555895, 28413899395,
    2904152265, 52046846775, 186556448925, 13015492875, 19352613047, 25442995,
    19352626301, 25442995, 4906556728115, 46276069817055, 25973139115, 645268292697425,
    1011940485, 1686567475, 51608964735, 1686567475, 1011940485, 826755376245,
    52958218715, 46276070098655, 51608964735, 1686567475, 52958218715, 1686567475,
    51608964735, 1686567475, 4906556728115, 1284899380254759, 28270756325, 10840835376631643,
    319055678525, 28270756325, 21681665539875107, 28270756325, 28270756325, 1172024783645,
    7269623055, 319055678525, 1172024783645, 1284899453429799
  ]
def negativeCoefficients : Array ℕ := #[
    268201653648584378546588221440, 260751607713901479142516326400, 168664299556589280386088960, 54330373425614538245532549120, 577826368843930646395943387136, 54330537177361680565222244352,
    168664299556589280386088960, 75573917604463651551990251520, 2957668236069111063416542330880, 2957669320841425532952793579520, 75575002376778121088241500160, 835232698783860580051876577280,
    33729265286533932665442140160, 1750420952993776944713564160, 3057125960873463844378960199680, 54330373425614538245532549120, 835379209977438031539758694400, 54330373425614538245532549120,
    56619385441067938865542594560, 33729265286533932665442140160, 1683097070186323985301504000, 6696423078876526086885212160, 262071869018781992960959447040, 262071965137847832033791836160,
    6696519197942365159717601280, 480047431151000169405952819200, 1720679534309771200667477606400, 480186932116630287754985472000, 22312043752221337393270095872, 58667552154208969152266240,
    22312059033042959452419915776, 58667552154208969152266240, 22097167052410914054644695040, 833635563137039820005698437120, 479119850045259998226641059840, 5812060085092238750463400345600,
    298672114313928310582841180160, 15555839287183766176189644800, 476008682187823244991403130880, 497786857189880517638068633600, 298672114313928310582841180160, 7625472418577482179568163880960,
    488453353617570257932354846720, 833635568209894440275825131520, 476008682187823244991403130880, 15555839287183766176189644800, 488453353617570257932354846720, 15555839287183766176189644800,
    476008682187823244991403130880, 497786857189880517638068633600, 22097167052410914054644695040, 1446668092530978469540440047616, 260751703348740286280472985600, 48822782162583158074897678204928,
    2942769223507211802308195123200, 260751703348740286280472985600, 48822770423076627933823328321536, 260751703348740286280472985600, 260751703348740286280472985600, 10810020615972061582656180060160,
    268201752015847151602772213760, 2942769223507211802308195123200, 10810020615972061582656180060160, 1446668174918749188745724952576
  ]
def negativeScales : Array ℕ := #[
    34, 36, 22, 31, 34, 30,
    22, 32, 40, 38, 34, 46,
    30, 25, 49, 31, 47, 31,
    31, 30, 26, 29, 36, 34,
    31, 35, 37, 33, 34, 24,
    34, 24, 42, 45, 34, 49,
    29, 30, 35, 30, 29, 39,
    35, 45, 35, 30, 35, 30,
    35, 30, 42, 50, 34, 53,
    38, 34, 54, 34, 34, 40,
    32, 38, 40, 50
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34759232884490278, 36718590899829556, 22124285103985659, 31455745619876622, 34866550796239090, 30455749968152966,
    22124285103985659, 32931875075724998, 40222303079916128, 38222303609047602, 34931895783724042, 46398092945262343,
    30767987550125517, 25499760474740145, 49270018842543408, 31455745619876622, 47398345991432841, 31455745619876622,
    31515282746854377, 30767987550125517, 26443176946373545, 29435449241955043, 36725877253928141, 34725877783059616,
    31435469949951353, 35599091710292957, 37440821276182162, 33599510894109866, 34171809325343065, 24600765170426203,
    34171810313399483, 24600765170426203, 42157848078887429, 45395331576455321, 34596301337633500, 49196892464253795,
    29914477303303714, 30651442891842960, 35586902639630066, 30651442891842960, 29914477303303714, 39588669565804455,
    35624135545836000, 45395331585234436, 35586902639630066, 30651442891842960, 35624135545836000, 30651442891842960,
    35586902639630066, 30651442891842960, 42157848078887429, 50190576810518565, 34718591428961031, 53267325450838609,
    38215017254969109, 34718591428961031, 54267325103940519, 34718591428961031, 34718591428961031, 40092140215971388,
    32759233413621755, 38215017254969109, 40092140215971388, 50190576892680068
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
noncomputable def negativeCeiling : ℝ := 96099689229 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 268201653648584378546588221440, coefficient := (-268201653648584378546588221440) }, { argument := 260751607713901479142516326400, coefficient := (-260751607713901479142516326400) }, { argument := 168664299556589280386088960, coefficient := (-168664299556589280386088960) }, { argument := 54330373425614538245532549120, coefficient := (-54330373425614538245532549120) }, { argument := 577826368843930646395943387136, coefficient := (-577826368843930646395943387136) }, { argument := 54330537177361680565222244352, coefficient := (-54330537177361680565222244352) }, { argument := 168664299556589280386088960, coefficient := (-168664299556589280386088960) }, { argument := 75573917604463651551990251520, coefficient := (-75573917604463651551990251520) }, { argument := 2957668236069111063416542330880, coefficient := (-2957668236069111063416542330880) }, { argument := 2957669320841425532952793579520, coefficient := (-2957669320841425532952793579520) }, { argument := 75575002376778121088241500160, coefficient := (-75575002376778121088241500160) }, { argument := 835232698783860580051876577280, coefficient := (-835232698783860580051876577280) }, { argument := 33729265286533932665442140160, coefficient := (-33729265286533932665442140160) }, { argument := 1750420952993776944713564160, coefficient := (-1750420952993776944713564160) }, { argument := 3057125960873463844378960199680, coefficient := (-3057125960873463844378960199680) }, { argument := 54330373425614538245532549120, coefficient := (-54330373425614538245532549120) }, { argument := 835379209977438031539758694400, coefficient := (-835379209977438031539758694400) }, { argument := 54330373425614538245532549120, coefficient := (-54330373425614538245532549120) }, { argument := 56619385441067938865542594560, coefficient := (-56619385441067938865542594560) }, { argument := 33729265286533932665442140160, coefficient := (-33729265286533932665442140160) }, { argument := 1683097070186323985301504000, coefficient := (-1683097070186323985301504000) }, { argument := 6696423078876526086885212160, coefficient := (-6696423078876526086885212160) }, { argument := 262071869018781992960959447040, coefficient := (-262071869018781992960959447040) }, { argument := 262071965137847832033791836160, coefficient := (-262071965137847832033791836160) }, { argument := 6696519197942365159717601280, coefficient := (-6696519197942365159717601280) }, { argument := 480047431151000169405952819200, coefficient := (-480047431151000169405952819200) }, { argument := 1720679534309771200667477606400, coefficient := (-1720679534309771200667477606400) }, { argument := 480186932116630287754985472000, coefficient := (-480186932116630287754985472000) }, { argument := 22312043752221337393270095872, coefficient := (-22312043752221337393270095872) }, { argument := 58667552154208969152266240, coefficient := (-58667552154208969152266240) }, { argument := 22312059033042959452419915776, coefficient := (-22312059033042959452419915776) }, { argument := 58667552154208969152266240, coefficient := (-58667552154208969152266240) }, { argument := 22097167052410914054644695040, coefficient := (-22097167052410914054644695040) }, { argument := 833635563137039820005698437120, coefficient := (-833635563137039820005698437120) }, { argument := 479119850045259998226641059840, coefficient := (-479119850045259998226641059840) }, { argument := 5812060085092238750463400345600, coefficient := (-5812060085092238750463400345600) }, { argument := 298672114313928310582841180160, coefficient := (-298672114313928310582841180160) }, { argument := 15555839287183766176189644800, coefficient := (-15555839287183766176189644800) }, { argument := 476008682187823244991403130880, coefficient := (-476008682187823244991403130880) }, { argument := 497786857189880517638068633600, coefficient := (-497786857189880517638068633600) }, { argument := 298672114313928310582841180160, coefficient := (-298672114313928310582841180160) }, { argument := 7625472418577482179568163880960, coefficient := (-7625472418577482179568163880960) }, { argument := 488453353617570257932354846720, coefficient := (-488453353617570257932354846720) }, { argument := 833635568209894440275825131520, coefficient := (-833635568209894440275825131520) }, { argument := 476008682187823244991403130880, coefficient := (-476008682187823244991403130880) }, { argument := 15555839287183766176189644800, coefficient := (-15555839287183766176189644800) }, { argument := 488453353617570257932354846720, coefficient := (-488453353617570257932354846720) }, { argument := 15555839287183766176189644800, coefficient := (-15555839287183766176189644800) }, { argument := 476008682187823244991403130880, coefficient := (-476008682187823244991403130880) }, { argument := 497786857189880517638068633600, coefficient := (-497786857189880517638068633600) }, { argument := 22097167052410914054644695040, coefficient := (-22097167052410914054644695040) }, { argument := 1446668092530978469540440047616, coefficient := (-1446668092530978469540440047616) }, { argument := 260751703348740286280472985600, coefficient := (-260751703348740286280472985600) }, { argument := 48822782162583158074897678204928, coefficient := (-48822782162583158074897678204928) }, { argument := 2942769223507211802308195123200, coefficient := (-2942769223507211802308195123200) }, { argument := 260751703348740286280472985600, coefficient := (-260751703348740286280472985600) }, { argument := 48822770423076627933823328321536, coefficient := (-48822770423076627933823328321536) }, { argument := 260751703348740286280472985600, coefficient := (-260751703348740286280472985600) }, { argument := 260751703348740286280472985600, coefficient := (-260751703348740286280472985600) }, { argument := 10810020615972061582656180060160, coefficient := (-10810020615972061582656180060160) }, { argument := 268201752015847151602772213760, coefficient := (-268201752015847151602772213760) }, { argument := 2942769223507211802308195123200, coefficient := (-2942769223507211802308195123200) }, { argument := 10810020615972061582656180060160, coefficient := (-10810020615972061582656180060160) }, { argument := 1446668174918749188745724952576, coefficient := (-1446668174918749188745724952576) }] }

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
def constantNumerator : ℤ := (-3986101659525903303329340209496064)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    28270756325, 7269623055, 28270756325, 1292991362476827, 19446516903, 504600239,
    9563301677077219, 31324030221, 2586304441849575, 31324030221, 32643753923, 19446516903,
    970385075, 726027645, 113655555895, 28413899395, 2904152265, 2027799225,
    7268433075, 507097125, 175799951903, 4462462285, 175799961773, 4462462285,
    3379665375, 12114055125, 845161875, 14587784095, 14587794529, 25442995,
    4462462285, 1115615705, 6360615, 4571655, 2945255445, 31324030221,
    1472632161, 4571655, 726027645, 113655555895, 28413899395, 2904152265,
    4764265, 3069343035, 32643753923, 1534676143, 4764265, 30099031797,
    4711834617247, 1177959086347, 120397855329, 103417760475, 370690086825, 25861953375,
    186692823, 29225714373, 7306431273, 746782011, 3379665375, 12114055125,
    845161875, 1182793305, 1182794151, 2838165
  ]
def negativeCoefficients : Array ℕ := #[
    260751703348740286280472985600, 268201752015847151602772213760, 260751703348740286280472985600, 5823115418243908001175743496192, 358724920434707873413094965248, 18616462936731346724032872448,
    21534640934658301478373857165312, 577826368843930646395943387136, 5823839860290202305298012569600, 577826368843930646395943387136, 602170974222733176727370989568, 358724920434707873413094965248,
    17900445131472448773108531200, 6696423078876526086885212160, 262071869018781992960959447040, 262071965137847832033791836160, 6696519197942365159717601280, 299250346691532573136178380800,
    1072631398011285943273232793600, 299337308332444854704406528000, 202683545057818091305280995328, 10289737463747016766332600320, 202683556437153341774860648448, 10289737463747016766332600320,
    15585955556850654850842624000, 55866218646421142878814208000, 15590484808981502849187840000, 16818569987687231544591646720, 16818582017270210612432994304, 58667552154208969152266240,
    10289737463747016766332600320, 10289738697373026695658864640, 58666318528199039826001920, 168664299556589280386088960, 54330373425614538245532549120, 577826368843930646395943387136,
    54330537177361680565222244352, 168664299556589280386088960, 6696423078876526086885212160, 262071869018781992960959447040, 262071965137847832033791836160, 6696519197942365159717601280,
    175770354308663673859604480, 56619385441067938865542594560, 602170974222733176727370989568, 56619556091897364752604594176, 175770354308663673859604480, 277614568212852552916298366976,
    10864750912750076336752918790144, 10864754897571920122315198693376, 277618553034696338478578270208, 476930240039630038435784294400, 1709506290580486972091714764800, 477068835154833987185147904000,
    6887749452558712546510503936, 269559636705032907045558288384, 269559735570357770091900174336, 6887848317883575592852389888, 498750577819220955226963968000, 1787718996685476572122054656000,
    498895513887408091174010880000, 21818685389432084165956730880, 21818700995377570524237398016, 104709806787919739124449280
  ]
def negativeScales : Array ℕ := #[
    34, 32, 34, 50, 34, 28,
    53, 34, 51, 34, 34, 34,
    29, 29, 36, 34, 31, 30,
    32, 28, 37, 32, 37, 32,
    31, 33, 29, 33, 33, 24,
    32, 30, 22, 22, 31, 34,
    30, 22, 29, 36, 34, 31,
    22, 31, 34, 30, 22, 34,
    42, 40, 36, 36, 38, 34,
    27, 34, 32, 29, 31, 33,
    29, 30, 30, 21
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34718591428961031, 32759233413621755, 34718591428961031, 50199634060907583, 34178792723788737, 28910565654006687,
    53086430210009922, 34866550796239090, 51199813532524662, 34866550796239090, 34926087927769864, 34178792723788737,
    29853982122236808, 29435449241955043, 36725877253928141, 34725877783059616, 31435469949951353, 30917267676246872,
    32758997236481786, 28917686860107529, 37355143719536315, 32055192830080739, 37355143800534060, 32055192830080739,
    31654233264503624, 33495962830374827, 29654652448320721, 33764041701663265, 33764042733559176, 24600765170426203,
    32055192830080739, 30055193003043949, 22600734833983421, 22124285103985659, 31455745619876622, 34866550796239090,
    30455749968152966, 22124285103985659, 29435449241955043, 36725877253928141, 34725877783059616, 31435469949951353,
    22183822230963023, 31515282746854377, 34926087927769864, 30515287095130721, 22183822230963023, 34808998029852049,
    42099426040918407, 40099426570049881, 36809018737848682, 36589693012289434, 38431422578179903, 34590112196106328,
    27476091226452482, 34766519238615278, 32766519767746755, 29476111934448792, 31654233264503624, 33495962830374827,
    29654652448320721, 30139550836450749, 30139551868346654, 21436527033903115
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
noncomputable def negativeCeiling : ℝ := 37679332259 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 260751703348740286280472985600, coefficient := (-260751703348740286280472985600) }, { argument := 268201752015847151602772213760, coefficient := (-268201752015847151602772213760) }, { argument := 260751703348740286280472985600, coefficient := (-260751703348740286280472985600) }, { argument := 5823115418243908001175743496192, coefficient := (-5823115418243908001175743496192) }, { argument := 358724920434707873413094965248, coefficient := (-358724920434707873413094965248) }, { argument := 18616462936731346724032872448, coefficient := (-18616462936731346724032872448) }, { argument := 21534640934658301478373857165312, coefficient := (-21534640934658301478373857165312) }, { argument := 577826368843930646395943387136, coefficient := (-577826368843930646395943387136) }, { argument := 5823839860290202305298012569600, coefficient := (-5823839860290202305298012569600) }, { argument := 577826368843930646395943387136, coefficient := (-577826368843930646395943387136) }, { argument := 602170974222733176727370989568, coefficient := (-602170974222733176727370989568) }, { argument := 358724920434707873413094965248, coefficient := (-358724920434707873413094965248) }, { argument := 17900445131472448773108531200, coefficient := (-17900445131472448773108531200) }, { argument := 6696423078876526086885212160, coefficient := (-6696423078876526086885212160) }, { argument := 262071869018781992960959447040, coefficient := (-262071869018781992960959447040) }, { argument := 262071965137847832033791836160, coefficient := (-262071965137847832033791836160) }, { argument := 6696519197942365159717601280, coefficient := (-6696519197942365159717601280) }, { argument := 299250346691532573136178380800, coefficient := (-299250346691532573136178380800) }, { argument := 1072631398011285943273232793600, coefficient := (-1072631398011285943273232793600) }, { argument := 299337308332444854704406528000, coefficient := (-299337308332444854704406528000) }, { argument := 202683545057818091305280995328, coefficient := (-202683545057818091305280995328) }, { argument := 10289737463747016766332600320, coefficient := (-10289737463747016766332600320) }, { argument := 202683556437153341774860648448, coefficient := (-202683556437153341774860648448) }, { argument := 10289737463747016766332600320, coefficient := (-10289737463747016766332600320) }, { argument := 15585955556850654850842624000, coefficient := (-15585955556850654850842624000) }, { argument := 55866218646421142878814208000, coefficient := (-55866218646421142878814208000) }, { argument := 15590484808981502849187840000, coefficient := (-15590484808981502849187840000) }, { argument := 16818569987687231544591646720, coefficient := (-16818569987687231544591646720) }, { argument := 16818582017270210612432994304, coefficient := (-16818582017270210612432994304) }, { argument := 58667552154208969152266240, coefficient := (-58667552154208969152266240) }, { argument := 10289737463747016766332600320, coefficient := (-10289737463747016766332600320) }, { argument := 10289738697373026695658864640, coefficient := (-10289738697373026695658864640) }, { argument := 58666318528199039826001920, coefficient := (-58666318528199039826001920) }, { argument := 168664299556589280386088960, coefficient := (-168664299556589280386088960) }, { argument := 54330373425614538245532549120, coefficient := (-54330373425614538245532549120) }, { argument := 577826368843930646395943387136, coefficient := (-577826368843930646395943387136) }, { argument := 54330537177361680565222244352, coefficient := (-54330537177361680565222244352) }, { argument := 168664299556589280386088960, coefficient := (-168664299556589280386088960) }, { argument := 6696423078876526086885212160, coefficient := (-6696423078876526086885212160) }, { argument := 262071869018781992960959447040, coefficient := (-262071869018781992960959447040) }, { argument := 262071965137847832033791836160, coefficient := (-262071965137847832033791836160) }, { argument := 6696519197942365159717601280, coefficient := (-6696519197942365159717601280) }, { argument := 175770354308663673859604480, coefficient := (-175770354308663673859604480) }, { argument := 56619385441067938865542594560, coefficient := (-56619385441067938865542594560) }, { argument := 602170974222733176727370989568, coefficient := (-602170974222733176727370989568) }, { argument := 56619556091897364752604594176, coefficient := (-56619556091897364752604594176) }, { argument := 175770354308663673859604480, coefficient := (-175770354308663673859604480) }, { argument := 277614568212852552916298366976, coefficient := (-277614568212852552916298366976) }, { argument := 10864750912750076336752918790144, coefficient := (-10864750912750076336752918790144) }, { argument := 10864754897571920122315198693376, coefficient := (-10864754897571920122315198693376) }, { argument := 277618553034696338478578270208, coefficient := (-277618553034696338478578270208) }, { argument := 476930240039630038435784294400, coefficient := (-476930240039630038435784294400) }, { argument := 1709506290580486972091714764800, coefficient := (-1709506290580486972091714764800) }, { argument := 477068835154833987185147904000, coefficient := (-477068835154833987185147904000) }, { argument := 6887749452558712546510503936, coefficient := (-6887749452558712546510503936) }, { argument := 269559636705032907045558288384, coefficient := (-269559636705032907045558288384) }, { argument := 269559735570357770091900174336, coefficient := (-269559735570357770091900174336) }, { argument := 6887848317883575592852389888, coefficient := (-6887848317883575592852389888) }, { argument := 498750577819220955226963968000, coefficient := (-498750577819220955226963968000) }, { argument := 1787718996685476572122054656000, coefficient := (-1787718996685476572122054656000) }, { argument := 498895513887408091174010880000, coefficient := (-498895513887408091174010880000) }, { argument := 21818685389432084165956730880, coefficient := (-21818685389432084165956730880) }, { argument := 21818700995377570524237398016, coefficient := (-21818700995377570524237398016) }, { argument := 104709806787919739124449280, coefficient := (-104709806787919739124449280) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4
