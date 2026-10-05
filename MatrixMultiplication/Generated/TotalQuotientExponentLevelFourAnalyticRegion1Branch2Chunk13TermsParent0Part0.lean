import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 13, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-15186151674652325124722698919870464)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    13482083, 2987, 70016925, 3709, 137, 3707,
    2909, 13494371, 2987, 67, 465438862442541, 32752066249129939,
    4165, 133, 7413, 86037, 16376035064431411, 7413,
    4165, 1029, 3801, 1029, 86037, 3801,
    232717491354829, 133, 499944722215207, 64208553845436469, 136603281085, 668004314331403199,
    105332634385, 4868131705, 136603281085, 107816213875, 105332634385, 1931284239775,
    3467935155, 32104284340779587, 136603281085, 4868131705, 3467935155, 4868131705,
    68519724385, 107816213875, 501511027992159, 109007566825119, 2657, 4007107191031179,
    1273, 2329, 32055783031889331, 1177, 1177, 76213,
    2279, 1273, 76213, 873135493202173, 2329, 2279,
    2657, 2647, 45543, 17647
  ]
def negativeCoefficients : Array ℕ := #[
    63667336878466634951602208768, 57776982771022357517557563392, 661291159707195467407923609600, 71742493839210553743763308544, 2649965396595267150955937792, 71703808212982885610172710912,
    56268243348143300307524255744, 63725365317808137151988105216, 57776982771022357517557563392, 2591936957253764950570041344, 262018785932496899163964833792, 18437774169399423986496299859968,
    40281408309559444101209784320, 41161506306238894140395880448, 1147106188902815497228400984064, 832098805937470802433562116096, 18437776353494869758478819262464, 1147106188902815497228400984064,
    40281408309559444101209784320, 39807509388270509464724963328, 36761016322841643944465399808, 39807509388270509464724963328, 832098805937470802433562116096, 36761016322841643944465399808,
    262016601837051127181445431296, 41161506306238894140395880448, 140721929042140773670602145792, 18073101198269131862882243313664, 157492860362750239878110248960, 188026498819049445490345895788544,
    121440259319357105690650869760, 5612573729952895323948974080, 157492860362750239878110248960, 124303631521778611353812992000, 121440259319357105690650869760, 2226619131544883622303917670400,
    127944224537010530616826920960, 18073105374266424729191940358144, 157492860362750239878110248960, 5612573729952895323948974080, 127944224537010530616826920960, 5612573729952895323948974080,
    157995727466401325158781419520, 124303631521778611353812992000, 141162804924230103821979746304, 490926437334170370109052289024, 401514487839508714649288704, 18046406452361652675618520694784,
    6155850273477691757603848192, 351948529235308918486335488, 18045801564685782448382800822272, 355726422421604634657292288, 355726422421604634657292288, 11516982936286216661485223936,
    344392742862717486144421888, 6155850273477691757603848192, 11516982936286216661485223936, 491531585228657570759862910976, 351948529235308918486335488, 344392742862717486144421888,
    401514487839508714649288704, 400003330564990428180905984, 430141473458664503934713856, 333342405292802516344373248
  ]
def negativeScales : Array ℕ := #[
    23, 11, 26, 11, 7, 11,
    11, 23, 11, 6, 48, 54,
    12, 7, 12, 16, 53, 12,
    12, 10, 11, 10, 16, 11,
    47, 7, 48, 55, 36, 59,
    36, 32, 36, 36, 36, 40,
    31, 54, 36, 32, 31, 32,
    35, 36, 48, 46, 11, 51,
    10, 11, 54, 10, 10, 16,
    11, 10, 16, 49, 11, 11,
    11, 11, 15, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    23684540076331082, 11544481522311915, 26061200367156680, 11856814554474635, 7098032082960527, 11856036401761948,
    11506307581100641, 23685854395693461, 11544481522311915, 6066089190457773, 48725585004085088, 54862435446073220,
    12024100780252910, 7055282435501190, 12855841797985584, 16392669600259067, 53862435616971484, 12855841797985584,
    12024100780252910, 10007027266893969, 11892163313654529, 10007027266893969, 16392669600259067, 11892163313654529,
    47725572978241981, 7055282435501190, 48828761917669470, 55833615025037841, 36991201200574282, 59212635033515656,
    36616161528293024, 32180721053997644, 36991201200574282, 36649783196994082, 36616161528293024, 40812697650294979,
    31691429776701251, 54833615358389045, 36991201200574282, 32180721053997644, 31691429776701251, 32180721053997644,
    35995800319323554, 36649783196994082, 48833274755050622, 46631421612449228, 11375582512490509, 51831482527227899,
    10314016703901359, 11185494924210867, 54831434169506443, 10200898605038445, 10200898605038445, 16217749485350390,
    11154185209265298, 10314016703901359, 16217749485350390, 49633198877140543, 11185494924210867, 11154185209265298,
    11375582512490509, 11370142479495401, 15474941707092834, 14107135324916144
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
noncomputable def negativeCeiling : ℝ := 41827999031 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 63667336878466634951602208768, coefficient := (-63667336878466634951602208768) }, { argument := 57776982771022357517557563392, coefficient := (-57776982771022357517557563392) }, { argument := 661291159707195467407923609600, coefficient := (-661291159707195467407923609600) }, { argument := 71742493839210553743763308544, coefficient := (-71742493839210553743763308544) }, { argument := 2649965396595267150955937792, coefficient := (-2649965396595267150955937792) }, { argument := 71703808212982885610172710912, coefficient := (-71703808212982885610172710912) }, { argument := 56268243348143300307524255744, coefficient := (-56268243348143300307524255744) }, { argument := 63725365317808137151988105216, coefficient := (-63725365317808137151988105216) }, { argument := 57776982771022357517557563392, coefficient := (-57776982771022357517557563392) }, { argument := 2591936957253764950570041344, coefficient := (-2591936957253764950570041344) }, { argument := 262018785932496899163964833792, coefficient := (-262018785932496899163964833792) }, { argument := 18437774169399423986496299859968, coefficient := (-18437774169399423986496299859968) }, { argument := 40281408309559444101209784320, coefficient := (-40281408309559444101209784320) }, { argument := 41161506306238894140395880448, coefficient := (-41161506306238894140395880448) }, { argument := 1147106188902815497228400984064, coefficient := (-1147106188902815497228400984064) }, { argument := 832098805937470802433562116096, coefficient := (-832098805937470802433562116096) }, { argument := 18437776353494869758478819262464, coefficient := (-18437776353494869758478819262464) }, { argument := 1147106188902815497228400984064, coefficient := (-1147106188902815497228400984064) }, { argument := 40281408309559444101209784320, coefficient := (-40281408309559444101209784320) }, { argument := 39807509388270509464724963328, coefficient := (-39807509388270509464724963328) }, { argument := 36761016322841643944465399808, coefficient := (-36761016322841643944465399808) }, { argument := 39807509388270509464724963328, coefficient := (-39807509388270509464724963328) }, { argument := 832098805937470802433562116096, coefficient := (-832098805937470802433562116096) }, { argument := 36761016322841643944465399808, coefficient := (-36761016322841643944465399808) }, { argument := 262016601837051127181445431296, coefficient := (-262016601837051127181445431296) }, { argument := 41161506306238894140395880448, coefficient := (-41161506306238894140395880448) }, { argument := 140721929042140773670602145792, coefficient := (-140721929042140773670602145792) }, { argument := 18073101198269131862882243313664, coefficient := (-18073101198269131862882243313664) }, { argument := 157492860362750239878110248960, coefficient := (-157492860362750239878110248960) }, { argument := 188026498819049445490345895788544, coefficient := (-188026498819049445490345895788544) }, { argument := 121440259319357105690650869760, coefficient := (-121440259319357105690650869760) }, { argument := 5612573729952895323948974080, coefficient := (-5612573729952895323948974080) }, { argument := 157492860362750239878110248960, coefficient := (-157492860362750239878110248960) }, { argument := 124303631521778611353812992000, coefficient := (-124303631521778611353812992000) }, { argument := 121440259319357105690650869760, coefficient := (-121440259319357105690650869760) }, { argument := 2226619131544883622303917670400, coefficient := (-2226619131544883622303917670400) }, { argument := 127944224537010530616826920960, coefficient := (-127944224537010530616826920960) }, { argument := 18073105374266424729191940358144, coefficient := (-18073105374266424729191940358144) }, { argument := 157492860362750239878110248960, coefficient := (-157492860362750239878110248960) }, { argument := 5612573729952895323948974080, coefficient := (-5612573729952895323948974080) }, { argument := 127944224537010530616826920960, coefficient := (-127944224537010530616826920960) }, { argument := 5612573729952895323948974080, coefficient := (-5612573729952895323948974080) }, { argument := 157995727466401325158781419520, coefficient := (-157995727466401325158781419520) }, { argument := 124303631521778611353812992000, coefficient := (-124303631521778611353812992000) }, { argument := 141162804924230103821979746304, coefficient := (-141162804924230103821979746304) }, { argument := 490926437334170370109052289024, coefficient := (-490926437334170370109052289024) }, { argument := 401514487839508714649288704, coefficient := (-401514487839508714649288704) }, { argument := 18046406452361652675618520694784, coefficient := (-18046406452361652675618520694784) }, { argument := 6155850273477691757603848192, coefficient := (-6155850273477691757603848192) }, { argument := 351948529235308918486335488, coefficient := (-351948529235308918486335488) }, { argument := 18045801564685782448382800822272, coefficient := (-18045801564685782448382800822272) }, { argument := 355726422421604634657292288, coefficient := (-355726422421604634657292288) }, { argument := 355726422421604634657292288, coefficient := (-355726422421604634657292288) }, { argument := 11516982936286216661485223936, coefficient := (-11516982936286216661485223936) }, { argument := 344392742862717486144421888, coefficient := (-344392742862717486144421888) }, { argument := 6155850273477691757603848192, coefficient := (-6155850273477691757603848192) }, { argument := 11516982936286216661485223936, coefficient := (-11516982936286216661485223936) }, { argument := 491531585228657570759862910976, coefficient := (-491531585228657570759862910976) }, { argument := 351948529235308918486335488, coefficient := (-351948529235308918486335488) }, { argument := 344392742862717486144421888, coefficient := (-344392742862717486144421888) }, { argument := 401514487839508714649288704, coefficient := (-401514487839508714649288704) }, { argument := 400003330564990428180905984, coefficient := (-400003330564990428180905984) }, { argument := 430141473458664503934713856, coefficient := (-430141473458664503934713856) }, { argument := 333342405292802516344373248, coefficient := (-333342405292802516344373248) }] }

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


end Parent0

namespace Parent0

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-113094290146705596675654164777271296)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    367557, 39571, 17647, 20023, 20023, 1247587,
    38621, 367557, 1247587, 2647, 39571, 38621,
    45543, 125153427324967, 219425361331673, 125153425814567, 465438751358931, 32752056948195373,
    4165, 133, 7413, 86037, 16376030413962445, 7413,
    4165, 1029, 3801, 1029, 86037, 3801,
    232717435814707, 133, 876628798037721, 112030463603429323, 477624230231, 1166147250578461761,
    370984067403, 16989843271, 477624230231, 374640397961, 370984067403, 6772492599533,
    24128655885, 56015245292258749, 477624230231, 16989843271, 24128655885, 16989843271,
    239592295663, 374640397961, 879306540960161, 1001942629945313, 70631, 73693458200414761,
    1130813, 61457, 147382049894022955, 31091, 31091, 1949579,
    60007, 1130813, 1949579, 4012639160331519
  ]
def negativeCoefficients : Array ℕ := #[
    6942955429376472743241842688, 373737528187269461502328832, 333342405292802516344373248, 378223776345995624455340032, 378223776345995624455340032, 11783126066527784126438703104,
    364765031869817135596306432, 6942955429376472743241842688, 11783126066527784126438703104, 400003330564990428180905984, 373737528187269461502328832, 364765031869817135596306432,
    430141473458664503934713856, 140910232166215458299374993408, 494101987764479482378955259904, 140910230465656239004275703808, 262018723397983823792776937472, 18437768933438743282125557989376,
    40281408309559444101209784320, 41161506306238894140395880448, 1147106188902815497228400984064, 832098805937470802433562116096, 18437771117532294164564861255680, 1147106188902815497228400984064,
    40281408309559444101209784320, 39807509388270509464724963328, 36761016322841643944465399808, 39807509388270509464724963328, 832098805937470802433562116096, 36761016322841643944465399808,
    262016539304432941353473671168, 41161506306238894140395880448, 493498141023115761335981309952, 63067544267318526703359833931776, 550663246154611607204010131456, 656482540395536101602960114450432,
    427715509175434693559690723328, 19587955667035834595720298496, 550663246154611607204010131456, 431930971303704045934069415936, 427715509175434693559690723328, 7808152357792322711640980062208,
    445095139953200846380109660160, 63067559456320858075921830117376, 550663246154611607204010131456, 19587955667035834595720298496, 445095139953200846380109660160, 19587955667035834595720298496,
    552462220015988994495978930176, 431930971303704045934069415936, 495005576276577607207440351232, 18049393819473305575289878740992, 333545467051565911088562176, 663771661782062280748630028582912,
    5340113409593272113035214848, 290222476937719785898115072, 663749744983821629624973713735680, 293646192637800278678044672, 293646192637800278678044672, 9206626525306520046072233984,
    283375045537558800338255872, 5340113409593272113035214848, 9206626525306520046072233984, 18071320227241288923089599463424
  ]
def negativeScales : Array ℕ := #[
    18, 15, 14, 14, 14, 20,
    15, 18, 20, 11, 15, 15,
    15, 46, 47, 46, 48, 54,
    12, 7, 12, 16, 53, 12,
    12, 10, 11, 10, 16, 11,
    47, 7, 49, 56, 38, 60,
    38, 33, 38, 38, 38, 42,
    34, 55, 38, 33, 34, 33,
    37, 38, 49, 49, 16, 56,
    20, 15, 57, 14, 14, 20,
    15, 20, 20, 51
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    18487608471979704, 15272155903713022, 14107135324916144, 14289370525595133, 14289370525595133, 20250708994178978,
    15237097899518053, 18487608471979704, 20250708994178978, 11370142479495401, 15272155903713022, 15237097899518053,
    15474941707092834, 46830691129367689, 47640723611486728, 46830691111956687, 48725584659765337, 54862435036376484,
    12024100780252910, 7055282435501190, 12855841797985584, 16392669600259067, 53862435207274649, 12855841797985584,
    12024100780252910, 10007027266893969, 11892163313654529, 10007027266893969, 16392669600259067, 11892163313654529,
    47725572633929794, 7055282435501190, 49638959401898740, 56636668699968864, 38797085071817022, 60016455678557580,
    38432566272730380, 33983953511080049, 38797085071817022, 38446715519411327, 38432566272730380, 42622824050619126,
    34490028499651057, 55636669047423263, 38797085071817022, 33983953511080049, 34490028499651057, 33983953511080049,
    37801790561958841, 38446715519411327, 49643359529107879, 49831721328406816, 16108013902001033, 56032386074550607,
    20108928943145099, 15907289728565838, 57032338438021394, 14924209406009814, 14924209406009814, 20894731189483595,
    15872843187536501, 20108928943145099, 20894731189483595, 51833472851057251
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
noncomputable def negativeCeiling : ℝ := 1517371559017 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 6942955429376472743241842688, coefficient := (-6942955429376472743241842688) }, { argument := 373737528187269461502328832, coefficient := (-373737528187269461502328832) }, { argument := 333342405292802516344373248, coefficient := (-333342405292802516344373248) }, { argument := 378223776345995624455340032, coefficient := (-378223776345995624455340032) }, { argument := 378223776345995624455340032, coefficient := (-378223776345995624455340032) }, { argument := 11783126066527784126438703104, coefficient := (-11783126066527784126438703104) }, { argument := 364765031869817135596306432, coefficient := (-364765031869817135596306432) }, { argument := 6942955429376472743241842688, coefficient := (-6942955429376472743241842688) }, { argument := 11783126066527784126438703104, coefficient := (-11783126066527784126438703104) }, { argument := 400003330564990428180905984, coefficient := (-400003330564990428180905984) }, { argument := 373737528187269461502328832, coefficient := (-373737528187269461502328832) }, { argument := 364765031869817135596306432, coefficient := (-364765031869817135596306432) }, { argument := 430141473458664503934713856, coefficient := (-430141473458664503934713856) }, { argument := 140910232166215458299374993408, coefficient := (-140910232166215458299374993408) }, { argument := 494101987764479482378955259904, coefficient := (-494101987764479482378955259904) }, { argument := 140910230465656239004275703808, coefficient := (-140910230465656239004275703808) }, { argument := 262018723397983823792776937472, coefficient := (-262018723397983823792776937472) }, { argument := 18437768933438743282125557989376, coefficient := (-18437768933438743282125557989376) }, { argument := 40281408309559444101209784320, coefficient := (-40281408309559444101209784320) }, { argument := 41161506306238894140395880448, coefficient := (-41161506306238894140395880448) }, { argument := 1147106188902815497228400984064, coefficient := (-1147106188902815497228400984064) }, { argument := 832098805937470802433562116096, coefficient := (-832098805937470802433562116096) }, { argument := 18437771117532294164564861255680, coefficient := (-18437771117532294164564861255680) }, { argument := 1147106188902815497228400984064, coefficient := (-1147106188902815497228400984064) }, { argument := 40281408309559444101209784320, coefficient := (-40281408309559444101209784320) }, { argument := 39807509388270509464724963328, coefficient := (-39807509388270509464724963328) }, { argument := 36761016322841643944465399808, coefficient := (-36761016322841643944465399808) }, { argument := 39807509388270509464724963328, coefficient := (-39807509388270509464724963328) }, { argument := 832098805937470802433562116096, coefficient := (-832098805937470802433562116096) }, { argument := 36761016322841643944465399808, coefficient := (-36761016322841643944465399808) }, { argument := 262016539304432941353473671168, coefficient := (-262016539304432941353473671168) }, { argument := 41161506306238894140395880448, coefficient := (-41161506306238894140395880448) }, { argument := 493498141023115761335981309952, coefficient := (-493498141023115761335981309952) }, { argument := 63067544267318526703359833931776, coefficient := (-63067544267318526703359833931776) }, { argument := 550663246154611607204010131456, coefficient := (-550663246154611607204010131456) }, { argument := 656482540395536101602960114450432, coefficient := (-656482540395536101602960114450432) }, { argument := 427715509175434693559690723328, coefficient := (-427715509175434693559690723328) }, { argument := 19587955667035834595720298496, coefficient := (-19587955667035834595720298496) }, { argument := 550663246154611607204010131456, coefficient := (-550663246154611607204010131456) }, { argument := 431930971303704045934069415936, coefficient := (-431930971303704045934069415936) }, { argument := 427715509175434693559690723328, coefficient := (-427715509175434693559690723328) }, { argument := 7808152357792322711640980062208, coefficient := (-7808152357792322711640980062208) }, { argument := 445095139953200846380109660160, coefficient := (-445095139953200846380109660160) }, { argument := 63067559456320858075921830117376, coefficient := (-63067559456320858075921830117376) }, { argument := 550663246154611607204010131456, coefficient := (-550663246154611607204010131456) }, { argument := 19587955667035834595720298496, coefficient := (-19587955667035834595720298496) }, { argument := 445095139953200846380109660160, coefficient := (-445095139953200846380109660160) }, { argument := 19587955667035834595720298496, coefficient := (-19587955667035834595720298496) }, { argument := 552462220015988994495978930176, coefficient := (-552462220015988994495978930176) }, { argument := 431930971303704045934069415936, coefficient := (-431930971303704045934069415936) }, { argument := 495005576276577607207440351232, coefficient := (-495005576276577607207440351232) }, { argument := 18049393819473305575289878740992, coefficient := (-18049393819473305575289878740992) }, { argument := 333545467051565911088562176, coefficient := (-333545467051565911088562176) }, { argument := 663771661782062280748630028582912, coefficient := (-663771661782062280748630028582912) }, { argument := 5340113409593272113035214848, coefficient := (-5340113409593272113035214848) }, { argument := 290222476937719785898115072, coefficient := (-290222476937719785898115072) }, { argument := 663749744983821629624973713735680, coefficient := (-663749744983821629624973713735680) }, { argument := 293646192637800278678044672, coefficient := (-293646192637800278678044672) }, { argument := 293646192637800278678044672, coefficient := (-293646192637800278678044672) }, { argument := 9206626525306520046072233984, coefficient := (-9206626525306520046072233984) }, { argument := 283375045537558800338255872, coefficient := (-283375045537558800338255872) }, { argument := 5340113409593272113035214848, coefficient := (-5340113409593272113035214848) }, { argument := 9206626525306520046072233984, coefficient := (-9206626525306520046072233984) }, { argument := 18071320227241288923089599463424, coefficient := (-18071320227241288923089599463424) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13
