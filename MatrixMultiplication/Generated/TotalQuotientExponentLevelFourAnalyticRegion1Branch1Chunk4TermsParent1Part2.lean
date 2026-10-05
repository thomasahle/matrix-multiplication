import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
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

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-5514886310492212497164932017553408)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1828467135, 19446516903, 914236323, 2838165, 8193740565, 1282684130815,
    320671150315, 32775432705, 2027799225, 7268433075, 507097125, 30099031797,
    4711834617247, 1177959086347, 120397855329, 1656711966825, 5938309822275, 414298351125,
    253512031705, 253512213031, 106121492775, 380381330925, 26538082875, 458529537905,
    458529865871, 74779542786011, 2889521775, 642956285532159, 32610317175, 2889521775,
    1285912384047143, 2889521775, 2889521775, 119791317015, 743019885, 32610317175,
    119791317015, 74779694014427, 2889521775, 743019885, 2889521775, 92729457851637,
    914236323, 23722699, 678818350473389, 1472632161, 185491447768425, 1472632161,
    1534676143, 914236323, 45620575, 175799952881, 1115615705, 175799962751,
    1115615705, 103417760475, 370690086825, 25861953375, 253512031705, 253512213031,
    7491024265, 7491029623, 141625, 91240875
  ]
def negativeCoefficients : Array ℕ := #[
    33729265286533932665442140160, 358724920434707873413094965248, 33729366946540522878781095936, 104709806787919739124449280, 75573917604463651551990251520, 2957668236069111063416542330880,
    2957669320841425532952793579520, 75575002376778121088241500160, 299250346691532573136178380800, 1072631398011285943273232793600, 299337308332444854704406528000, 277614568212852552916298366976,
    10864750912750076336752918790144, 10864754897571920122315198693376, 277618553034696338478578270208, 7640235413968191007883054284800, 27385620380475644239194724761600, 7642455653362732696671879168000,
    292279473029267294139795374080, 292279682083912038480930144256, 489399004485110562316458393600, 1754199265497623886394766131200, 489541223002019189464498176000, 528648564748114872604326625280,
    528648942867169052493501956096, 42097140128251900237742866432, 6662783584854494302489804800, 1447808843969074750434607890432, 75194271886215007128099225600, 6662783584854494302489804800,
    1447808633406454839963897823232, 6662783584854494302489804800, 6662783584854494302489804800, 276219970903539178083220193280, 6853148830136051282560942080, 75194271886215007128099225600,
    276219970903539178083220193280, 42097225262281643416537268224, 6662783584854494302489804800, 6853148830136051282560942080, 6662783584854494302489804800, 835232703653801015511198203904,
    33729366946540522878781095936, 1750426228762582025645326336, 3057126070244209457402891730944, 54330537177361680565222244352, 835379215050292651809885388800, 54330537177361680565222244352,
    56619556091897364752604594176, 33729366946540522878781095936, 1683102143040944255428198400, 202683546185375322810777337856, 10289738697373026695658864640, 202683557564710573280356990976,
    10289738697373026695658864640, 476930240039630038435784294400, 1709506290580486972091714764800, 477068835154833987185147904000, 292279473029267294139795374080, 292279682083912038480930144256,
    17273125933300399964715745280, 17273138288007243331687940096, 5225040258878230495232000, 1683097070186323985301504000
  ]
def negativeScales : Array ℕ := #[
    30, 34, 29, 21, 32, 40,
    38, 34, 30, 32, 28, 34,
    42, 40, 36, 40, 42, 38,
    37, 37, 36, 38, 34, 38,
    38, 46, 31, 49, 34, 31,
    50, 31, 31, 36, 29, 34,
    36, 46, 31, 29, 31, 46,
    29, 24, 49, 30, 47, 30,
    30, 29, 25, 37, 30, 37,
    30, 36, 38, 34, 37, 37,
    32, 32, 17, 26
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30767987550125517, 34178792723788737, 29767991898401891, 21436527033903115, 32931875075724998, 40222303079916128,
    38222303609047602, 34931895783724042, 30917267676246872, 32758997236481786, 28917686860107529, 34808998029852049,
    42099426040918407, 40099426570049881, 36809018737848682, 40591459938463838, 42433189504354092, 38591879122280735,
    37883263266282908, 37883264298178874, 36626925918495881, 38468655484378947, 34627345102312856, 38738223717376284,
    38738224749272193, 46087708883892383, 31428183595872854, 49191713980766553, 34924609428737878, 31428183595872854,
    50191713770947645, 31428183595872854, 31428183595872854, 36801732383663843, 29468825580370272, 34924609428737878,
    36801732383663843, 46087711801485311, 31428183595872854, 29468825580370272, 31428183595872854, 46398092953674177,
    29767991898401891, 24499764823016489, 49270018894156796, 30455749968152966, 47398346000193632, 30455749968152966,
    30515287095130721, 29767991898401891, 25443181294649889, 37355143727562232, 30055193003043949, 37355143808559976,
    30055193003043949, 36589693012289434, 38431422578179903, 34590112196106328, 37883263266282908, 37883264298178874,
    32802515849853154, 32802516881749073, 17111716430482603, 26443176946373545
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
noncomputable def negativeCeiling : ℝ := 44535718857 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 33729265286533932665442140160, coefficient := (-33729265286533932665442140160) }, { argument := 358724920434707873413094965248, coefficient := (-358724920434707873413094965248) }, { argument := 33729366946540522878781095936, coefficient := (-33729366946540522878781095936) }, { argument := 104709806787919739124449280, coefficient := (-104709806787919739124449280) }, { argument := 75573917604463651551990251520, coefficient := (-75573917604463651551990251520) }, { argument := 2957668236069111063416542330880, coefficient := (-2957668236069111063416542330880) }, { argument := 2957669320841425532952793579520, coefficient := (-2957669320841425532952793579520) }, { argument := 75575002376778121088241500160, coefficient := (-75575002376778121088241500160) }, { argument := 299250346691532573136178380800, coefficient := (-299250346691532573136178380800) }, { argument := 1072631398011285943273232793600, coefficient := (-1072631398011285943273232793600) }, { argument := 299337308332444854704406528000, coefficient := (-299337308332444854704406528000) }, { argument := 277614568212852552916298366976, coefficient := (-277614568212852552916298366976) }, { argument := 10864750912750076336752918790144, coefficient := (-10864750912750076336752918790144) }, { argument := 10864754897571920122315198693376, coefficient := (-10864754897571920122315198693376) }, { argument := 277618553034696338478578270208, coefficient := (-277618553034696338478578270208) }, { argument := 7640235413968191007883054284800, coefficient := (-7640235413968191007883054284800) }, { argument := 27385620380475644239194724761600, coefficient := (-27385620380475644239194724761600) }, { argument := 7642455653362732696671879168000, coefficient := (-7642455653362732696671879168000) }, { argument := 292279473029267294139795374080, coefficient := (-292279473029267294139795374080) }, { argument := 292279682083912038480930144256, coefficient := (-292279682083912038480930144256) }, { argument := 489399004485110562316458393600, coefficient := (-489399004485110562316458393600) }, { argument := 1754199265497623886394766131200, coefficient := (-1754199265497623886394766131200) }, { argument := 489541223002019189464498176000, coefficient := (-489541223002019189464498176000) }, { argument := 528648564748114872604326625280, coefficient := (-528648564748114872604326625280) }, { argument := 528648942867169052493501956096, coefficient := (-528648942867169052493501956096) }, { argument := 42097140128251900237742866432, coefficient := (-42097140128251900237742866432) }, { argument := 6662783584854494302489804800, coefficient := (-6662783584854494302489804800) }, { argument := 1447808843969074750434607890432, coefficient := (-1447808843969074750434607890432) }, { argument := 75194271886215007128099225600, coefficient := (-75194271886215007128099225600) }, { argument := 6662783584854494302489804800, coefficient := (-6662783584854494302489804800) }, { argument := 1447808633406454839963897823232, coefficient := (-1447808633406454839963897823232) }, { argument := 6662783584854494302489804800, coefficient := (-6662783584854494302489804800) }, { argument := 6662783584854494302489804800, coefficient := (-6662783584854494302489804800) }, { argument := 276219970903539178083220193280, coefficient := (-276219970903539178083220193280) }, { argument := 6853148830136051282560942080, coefficient := (-6853148830136051282560942080) }, { argument := 75194271886215007128099225600, coefficient := (-75194271886215007128099225600) }, { argument := 276219970903539178083220193280, coefficient := (-276219970903539178083220193280) }, { argument := 42097225262281643416537268224, coefficient := (-42097225262281643416537268224) }, { argument := 6662783584854494302489804800, coefficient := (-6662783584854494302489804800) }, { argument := 6853148830136051282560942080, coefficient := (-6853148830136051282560942080) }, { argument := 6662783584854494302489804800, coefficient := (-6662783584854494302489804800) }, { argument := 835232703653801015511198203904, coefficient := (-835232703653801015511198203904) }, { argument := 33729366946540522878781095936, coefficient := (-33729366946540522878781095936) }, { argument := 1750426228762582025645326336, coefficient := (-1750426228762582025645326336) }, { argument := 3057126070244209457402891730944, coefficient := (-3057126070244209457402891730944) }, { argument := 54330537177361680565222244352, coefficient := (-54330537177361680565222244352) }, { argument := 835379215050292651809885388800, coefficient := (-835379215050292651809885388800) }, { argument := 54330537177361680565222244352, coefficient := (-54330537177361680565222244352) }, { argument := 56619556091897364752604594176, coefficient := (-56619556091897364752604594176) }, { argument := 33729366946540522878781095936, coefficient := (-33729366946540522878781095936) }, { argument := 1683102143040944255428198400, coefficient := (-1683102143040944255428198400) }, { argument := 202683546185375322810777337856, coefficient := (-202683546185375322810777337856) }, { argument := 10289738697373026695658864640, coefficient := (-10289738697373026695658864640) }, { argument := 202683557564710573280356990976, coefficient := (-202683557564710573280356990976) }, { argument := 10289738697373026695658864640, coefficient := (-10289738697373026695658864640) }, { argument := 476930240039630038435784294400, coefficient := (-476930240039630038435784294400) }, { argument := 1709506290580486972091714764800, coefficient := (-1709506290580486972091714764800) }, { argument := 477068835154833987185147904000, coefficient := (-477068835154833987185147904000) }, { argument := 292279473029267294139795374080, coefficient := (-292279473029267294139795374080) }, { argument := 292279682083912038480930144256, coefficient := (-292279682083912038480930144256) }, { argument := 17273125933300399964715745280, coefficient := (-17273125933300399964715745280) }, { argument := 17273138288007243331687940096, coefficient := (-17273138288007243331687940096) }, { argument := 5225040258878230495232000, coefficient := (-5225040258878230495232000) }, { argument := 1683097070186323985301504000, coefficient := (-1683097070186323985301504000) }] }

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
def constantNumerator : ℤ := 56457077399554633455309445945884672
def positiveArguments : Array ℕ := #[
    223, 489, 535, 489, 535, 33,
    5511
  ]
def positiveCoefficients : Array ℕ := #[
    565372167701790313067529629597696, 37834542450659434651604484096, 41393620063604902941939466240, 37834542450659434651604484096, 41393620063604902941939466240, 40852021296417549071671099392,
    852785944562716336871134199808
  ]
def positiveScales : Array ℕ := #[
    7, 8, 9, 8, 9, 5,
    12
  ]
def negativeArguments : Array ℕ := #[
    970385075, 45620575, 141625, 726027645, 113655555895, 28413899395,
    2904152265, 3379665375, 12114055125, 845161875, 186692823, 29225714373,
    7306431273, 746782011, 106121492775, 380381330925, 26538082875, 7491024265,
    7491029623, 3379665375, 12114055125, 845161875, 14587784095, 14587794529,
    726027645, 113655555895, 28413899395, 2904152265, 103417760475, 370690086825,
    25861953375, 14587784095, 14587794529, 3379665375, 12114055125, 845161875,
    458529537905, 458529865871, 14587784095, 14587794529, 9832160204049, 2838165,
    73645, 70746681410153, 4571655, 19669335430005, 4571655, 4764265,
    2838165, 141625, 19352612069, 6360615, 19352625323, 6360615,
    1182793305, 1182794151, 1
  ]
def negativeCoefficients : Array ℕ := #[
    17900445131472448773108531200, 1683102143040944255428198400, 5225040258878230495232000, 6696423078876526086885212160, 262071869018781992960959447040, 262071965137847832033791836160,
    6696519197942365159717601280, 15585955556850654850842624000, 55866218646421142878814208000, 15590484808981502849187840000, 6887749452558712546510503936, 269559636705032907045558288384,
    269559735570357770091900174336, 6887848317883575592852389888, 489399004485110562316458393600, 1754199265497623886394766131200, 489541223002019189464498176000, 17273125933300399964715745280,
    17273138288007243331687940096, 15585955556850654850842624000, 55866218646421142878814208000, 15590484808981502849187840000, 16818569987687231544591646720, 16818582017270210612432994304,
    6696423078876526086885212160, 262071869018781992960959447040, 262071965137847832033791836160, 6696519197942365159717601280, 476930240039630038435784294400, 1709506290580486972091714764800,
    477068835154833987185147904000, 16818569987687231544591646720, 16818582017270210612432994304, 498750577819220955226963968000, 1787718996685476572122054656000, 498895513887408091174010880000,
    528648564748114872604326625280, 528648942867169052493501956096, 16818569987687231544591646720, 16818582017270210612432994304, 22140056515601048158341169152, 104709806787919739124449280,
    5434041869233359715041280, 79653682009116061822166761472, 168664299556589280386088960, 22145702928298953176902533120, 168664299556589280386088960, 175770354308663673859604480,
    104709806787919739124449280, 5225040258878230495232000, 22312042624664105887773753344, 58666318528199039826001920, 22312057905485727946923573248, 58666318528199039826001920,
    21818685389432084165956730880, 21818700995377570524237398016, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    29, 25, 17, 29, 36, 34,
    31, 31, 33, 29, 27, 34,
    32, 29, 36, 38, 34, 32,
    32, 31, 33, 29, 33, 33,
    29, 36, 34, 31, 36, 38,
    34, 33, 33, 31, 33, 29,
    38, 38, 33, 33, 43, 21,
    16, 46, 22, 44, 22, 22,
    21, 17, 34, 22, 34, 22,
    30, 30, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7800899899879537, 8933690654464738, 9063395081288509, 8933690654464738, 9063395081288509, 5044394119358453,
    12428098411832503
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    29853982122236808, 25443181294649889, 17111716430482603, 29435449241955043, 36725877253928141, 34725877783059616,
    31435469949951353, 31654233264503624, 33495962830374827, 29654652448320721, 27476091226452482, 34766519238615278,
    32766519767746755, 29476111934448792, 36626925918495881, 38468655484378947, 34627345102312856, 32802515849853154,
    32802516881749073, 31654233264503624, 33495962830374827, 29654652448320721, 33764041701663265, 33764042733559176,
    29435449241955043, 36725877253928141, 34725877783059616, 31435469949951353, 36589693012289434, 38431422578179903,
    34590112196106328, 33764041701663265, 33764042733559176, 31654233264503624, 33495962830374827, 29654652448320721,
    38738223717376284, 38738224749272193, 33764041701663265, 33764042733559176, 43160645561651849, 21436527033903115,
    16168299958848971, 46007727709036352, 22124285103985659, 44161013447479913, 22124285103985659, 22183822230963023,
    21436527033903115, 17111716430482603, 34171809252435299, 22600734833983421, 34171810240491767, 22600734833983421,
    30139550836450749, 30139551868346654, 0
  ]

abbrev PositiveTerm := Fin 7
abbrev NegativeTerm := Fin 57
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
noncomputable def positiveFloor : ℝ := 53235623919 / 1000000000000
noncomputable def negativeCeiling : ℝ := 4929447233 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 17900445131472448773108531200, coefficient := (-17900445131472448773108531200) }, { argument := 1683102143040944255428198400, coefficient := (-1683102143040944255428198400) }, { argument := 5225040258878230495232000, coefficient := (-5225040258878230495232000) }, { argument := 6696423078876526086885212160, coefficient := (-6696423078876526086885212160) }, { argument := 262071869018781992960959447040, coefficient := (-262071869018781992960959447040) }, { argument := 262071965137847832033791836160, coefficient := (-262071965137847832033791836160) }, { argument := 6696519197942365159717601280, coefficient := (-6696519197942365159717601280) }, { argument := 15585955556850654850842624000, coefficient := (-15585955556850654850842624000) }, { argument := 55866218646421142878814208000, coefficient := (-55866218646421142878814208000) }, { argument := 15590484808981502849187840000, coefficient := (-15590484808981502849187840000) }, { argument := 6887749452558712546510503936, coefficient := (-6887749452558712546510503936) }, { argument := 269559636705032907045558288384, coefficient := (-269559636705032907045558288384) }, { argument := 269559735570357770091900174336, coefficient := (-269559735570357770091900174336) }, { argument := 6887848317883575592852389888, coefficient := (-6887848317883575592852389888) }, { argument := 489399004485110562316458393600, coefficient := (-489399004485110562316458393600) }, { argument := 1754199265497623886394766131200, coefficient := (-1754199265497623886394766131200) }, { argument := 489541223002019189464498176000, coefficient := (-489541223002019189464498176000) }, { argument := 17273125933300399964715745280, coefficient := (-17273125933300399964715745280) }, { argument := 17273138288007243331687940096, coefficient := (-17273138288007243331687940096) }, { argument := 15585955556850654850842624000, coefficient := (-15585955556850654850842624000) }, { argument := 55866218646421142878814208000, coefficient := (-55866218646421142878814208000) }, { argument := 15590484808981502849187840000, coefficient := (-15590484808981502849187840000) }, { argument := 16818569987687231544591646720, coefficient := (-16818569987687231544591646720) }, { argument := 16818582017270210612432994304, coefficient := (-16818582017270210612432994304) }, { argument := 6696423078876526086885212160, coefficient := (-6696423078876526086885212160) }, { argument := 262071869018781992960959447040, coefficient := (-262071869018781992960959447040) }, { argument := 262071965137847832033791836160, coefficient := (-262071965137847832033791836160) }, { argument := 6696519197942365159717601280, coefficient := (-6696519197942365159717601280) }, { argument := 476930240039630038435784294400, coefficient := (-476930240039630038435784294400) }, { argument := 1709506290580486972091714764800, coefficient := (-1709506290580486972091714764800) }, { argument := 477068835154833987185147904000, coefficient := (-477068835154833987185147904000) }, { argument := 16818569987687231544591646720, coefficient := (-16818569987687231544591646720) }, { argument := 16818582017270210612432994304, coefficient := (-16818582017270210612432994304) }, { argument := 498750577819220955226963968000, coefficient := (-498750577819220955226963968000) }, { argument := 1787718996685476572122054656000, coefficient := (-1787718996685476572122054656000) }, { argument := 498895513887408091174010880000, coefficient := (-498895513887408091174010880000) }, { argument := 528648564748114872604326625280, coefficient := (-528648564748114872604326625280) }, { argument := 528648942867169052493501956096, coefficient := (-528648942867169052493501956096) }, { argument := 16818569987687231544591646720, coefficient := (-16818569987687231544591646720) }, { argument := 16818582017270210612432994304, coefficient := (-16818582017270210612432994304) }, { argument := 22140056515601048158341169152, coefficient := (-22140056515601048158341169152) }, { argument := 104709806787919739124449280, coefficient := (-104709806787919739124449280) }, { argument := 5434041869233359715041280, coefficient := (-5434041869233359715041280) }, { argument := 79653682009116061822166761472, coefficient := (-79653682009116061822166761472) }, { argument := 168664299556589280386088960, coefficient := (-168664299556589280386088960) }, { argument := 22145702928298953176902533120, coefficient := (-22145702928298953176902533120) }, { argument := 168664299556589280386088960, coefficient := (-168664299556589280386088960) }, { argument := 175770354308663673859604480, coefficient := (-175770354308663673859604480) }, { argument := 104709806787919739124449280, coefficient := (-104709806787919739124449280) }, { argument := 5225040258878230495232000, coefficient := (-5225040258878230495232000) }, { argument := 22312042624664105887773753344, coefficient := (-22312042624664105887773753344) }, { argument := 58666318528199039826001920, coefficient := (-58666318528199039826001920) }, { argument := 22312057905485727946923573248, coefficient := (-22312057905485727946923573248) }, { argument := 58666318528199039826001920, coefficient := (-58666318528199039826001920) }, { argument := 21818685389432084165956730880, coefficient := (-21818685389432084165956730880) }, { argument := 21818700995377570524237398016, coefficient := (-21818700995377570524237398016) }, { argument := 565372167701790313067529629597696, coefficient := 565372167701790313067529629597696 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 40852021296417549071671099392, coefficient := 40852021296417549071671099392 }, { argument := 852785944562716336871134199808, coefficient := 852785944562716336871134199808 }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4
