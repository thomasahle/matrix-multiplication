import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 10, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-21207421872929495043164355877142528)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    15088841, 465806135, 1175, 2093, 96321, 13659,
    232903135, 96321, 1175, 2349, 2019, 2349,
    13659, 2019, 7544353, 2093, 119820223414407, 9302936685376179,
    297311399095, 343905439807511225, 304988986355, 9717163275, 297311399095, 169141826905,
    304988986355, 4762109241565, 5831793645, 9302941580128947, 297311399095, 9717163275,
    5831793645, 9717163275, 149626681155, 169141826905, 479297813417363, 1484119179723437,
    29234750919, 26033079085261159, 723404581251, 23014591149, 104131876708627551, 11818303563,
    11818303563, 399956273211, 21770559195, 723404581251, 399956273211, 2968688310816939,
    23014591149, 21770559195, 29234750919, 2545, 10689, 46319,
    1527, 1527, 3563, 46319, 46319, 1527,
    571607, 22905, 10689, 46319
  ]
def negativeCoefficients : Array ℕ := #[
    71255037003749300355869966336, 2199707279439053145812982824960, 45455610817510056968952217600, 40484507847254701802560421888, 1863119101937611147789977255936, 528406968643719036713973055488,
    2199707916958528333215086673920, 1863119101937611147789977255936, 45455610817510056968952217600, 45436268004396222902156918784, 39053139676830980859708309504, 45436268004396222902156918784,
    528406968643719036713973055488, 39053139676830980859708309504, 71254399484274112953766117376, 40484507847254701802560421888, 134905578380143236280083283968, 10474175547427869232317591453696,
    1371106822325496649404519546880, 96800775660487130908452297113600, 1406513444147694888011348049920, 44812506014093586994928025600, 1371106822325496649404519546880, 780028998269053885169658757120,
    1406513444147694888011348049920, 21961352607549162825541495029760, 860620838880006197519906242560, 10474181058429554741193555836928, 1371106822325496649404519546880, 44812506014093586994928025600,
    860620838880006197519906242560, 44812506014093586994928025600, 1380062546932412448862623498240, 780028998269053885169658757120, 134910340869120595300217520128, 3341939292387938527984406757376,
    67410746032679764730616741888, 117242565267688808538760611364864, 1668057396510778008121431293952, 53068034110833006277294030848, 117242070285591367539640787533824, 54502305303017682122626301952,
    54502305303017682122626301952, 922236376574746568548650319872, 50199491726463654586629488640, 1668057396510778008121431293952, 922236376574746568548650319872, 3342445892593578422521546407936,
    53068034110833006277294030848, 50199491726463654586629488640, 67410746032679764730616741888, 24036845397806494137712640, 403819002683149101513572352, 874941172480156386612740096,
    28844214477367792965255168, 461507431637884687444082688, 33651583556929091792797696, 874941172480156386612740096, 874941172480156386612740096, 461507431637884687444082688,
    10797350952694677166660517888, 865326434321033788957655040, 403819002683149101513572352, 874941172480156386612740096
  ]
def negativeScales : Array ℕ := #[
    23, 28, 10, 11, 16, 13,
    27, 16, 10, 11, 10, 11,
    13, 10, 22, 11, 46, 53,
    38, 58, 38, 33, 38, 37,
    38, 42, 32, 53, 38, 33,
    32, 33, 37, 37, 48, 50,
    34, 54, 39, 34, 56, 33,
    33, 38, 34, 39, 38, 51,
    34, 34, 34, 11, 13, 15,
    10, 10, 11, 15, 15, 10,
    19, 14, 13, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    23846978660062989, 28795154400683565, 10198445041452363, 11031356596255710, 16555562749717075, 13737564244911302,
    27795154818805591, 16555562749717075, 10198445041452363, 11197830998012197, 10979425212320825, 11197830998012197,
    13737564244911302, 10979425212320825, 22846965752198966, 11031356596255710, 46767864757392416, 53046607631213489,
    38113183821848655, 58254789549308256, 38149966189328593, 33177888064278595, 38113183821848655, 37299442510171613,
    38149966189328593, 42114737854690530, 32441292525536912, 53046608390289244, 38113183821848655, 33177888064278595,
    32441292525536912, 33177888064278595, 37122576500656453, 37299442510171613, 48767915687072905, 50398528373147942,
    34766965248760066, 54531195476053705, 39396011778231276, 34421829762387018, 56531189385179430, 33460303910201706,
    33460303910201706, 38541051324087011, 34341659413703020, 39396011778231276, 38541051324087011, 51398747052827692,
    34421829762387018, 34341659413703020, 34766965248760066, 11313449940963058, 13383839268854459, 15499316486274657,
    10576484346799762, 10576484346799762, 11798876768764696, 15499316486274657, 15499316486274657, 10576484346799762,
    19124664058476297, 14483374942405524, 13383839268854459, 15499316486274657
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
noncomputable def negativeCeiling : ℝ := 263724094983 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 71255037003749300355869966336, coefficient := (-71255037003749300355869966336) }, { argument := 2199707279439053145812982824960, coefficient := (-2199707279439053145812982824960) }, { argument := 45455610817510056968952217600, coefficient := (-45455610817510056968952217600) }, { argument := 40484507847254701802560421888, coefficient := (-40484507847254701802560421888) }, { argument := 1863119101937611147789977255936, coefficient := (-1863119101937611147789977255936) }, { argument := 528406968643719036713973055488, coefficient := (-528406968643719036713973055488) }, { argument := 2199707916958528333215086673920, coefficient := (-2199707916958528333215086673920) }, { argument := 1863119101937611147789977255936, coefficient := (-1863119101937611147789977255936) }, { argument := 45455610817510056968952217600, coefficient := (-45455610817510056968952217600) }, { argument := 45436268004396222902156918784, coefficient := (-45436268004396222902156918784) }, { argument := 39053139676830980859708309504, coefficient := (-39053139676830980859708309504) }, { argument := 45436268004396222902156918784, coefficient := (-45436268004396222902156918784) }, { argument := 528406968643719036713973055488, coefficient := (-528406968643719036713973055488) }, { argument := 39053139676830980859708309504, coefficient := (-39053139676830980859708309504) }, { argument := 71254399484274112953766117376, coefficient := (-71254399484274112953766117376) }, { argument := 40484507847254701802560421888, coefficient := (-40484507847254701802560421888) }, { argument := 134905578380143236280083283968, coefficient := (-134905578380143236280083283968) }, { argument := 10474175547427869232317591453696, coefficient := (-10474175547427869232317591453696) }, { argument := 1371106822325496649404519546880, coefficient := (-1371106822325496649404519546880) }, { argument := 96800775660487130908452297113600, coefficient := (-96800775660487130908452297113600) }, { argument := 1406513444147694888011348049920, coefficient := (-1406513444147694888011348049920) }, { argument := 44812506014093586994928025600, coefficient := (-44812506014093586994928025600) }, { argument := 1371106822325496649404519546880, coefficient := (-1371106822325496649404519546880) }, { argument := 780028998269053885169658757120, coefficient := (-780028998269053885169658757120) }, { argument := 1406513444147694888011348049920, coefficient := (-1406513444147694888011348049920) }, { argument := 21961352607549162825541495029760, coefficient := (-21961352607549162825541495029760) }, { argument := 860620838880006197519906242560, coefficient := (-860620838880006197519906242560) }, { argument := 10474181058429554741193555836928, coefficient := (-10474181058429554741193555836928) }, { argument := 1371106822325496649404519546880, coefficient := (-1371106822325496649404519546880) }, { argument := 44812506014093586994928025600, coefficient := (-44812506014093586994928025600) }, { argument := 860620838880006197519906242560, coefficient := (-860620838880006197519906242560) }, { argument := 44812506014093586994928025600, coefficient := (-44812506014093586994928025600) }, { argument := 1380062546932412448862623498240, coefficient := (-1380062546932412448862623498240) }, { argument := 780028998269053885169658757120, coefficient := (-780028998269053885169658757120) }, { argument := 134910340869120595300217520128, coefficient := (-134910340869120595300217520128) }, { argument := 3341939292387938527984406757376, coefficient := (-3341939292387938527984406757376) }, { argument := 67410746032679764730616741888, coefficient := (-67410746032679764730616741888) }, { argument := 117242565267688808538760611364864, coefficient := (-117242565267688808538760611364864) }, { argument := 1668057396510778008121431293952, coefficient := (-1668057396510778008121431293952) }, { argument := 53068034110833006277294030848, coefficient := (-53068034110833006277294030848) }, { argument := 117242070285591367539640787533824, coefficient := (-117242070285591367539640787533824) }, { argument := 54502305303017682122626301952, coefficient := (-54502305303017682122626301952) }, { argument := 54502305303017682122626301952, coefficient := (-54502305303017682122626301952) }, { argument := 922236376574746568548650319872, coefficient := (-922236376574746568548650319872) }, { argument := 50199491726463654586629488640, coefficient := (-50199491726463654586629488640) }, { argument := 1668057396510778008121431293952, coefficient := (-1668057396510778008121431293952) }, { argument := 922236376574746568548650319872, coefficient := (-922236376574746568548650319872) }, { argument := 3342445892593578422521546407936, coefficient := (-3342445892593578422521546407936) }, { argument := 53068034110833006277294030848, coefficient := (-53068034110833006277294030848) }, { argument := 50199491726463654586629488640, coefficient := (-50199491726463654586629488640) }, { argument := 67410746032679764730616741888, coefficient := (-67410746032679764730616741888) }, { argument := 24036845397806494137712640, coefficient := (-24036845397806494137712640) }, { argument := 403819002683149101513572352, coefficient := (-403819002683149101513572352) }, { argument := 874941172480156386612740096, coefficient := (-874941172480156386612740096) }, { argument := 28844214477367792965255168, coefficient := (-28844214477367792965255168) }, { argument := 461507431637884687444082688, coefficient := (-461507431637884687444082688) }, { argument := 33651583556929091792797696, coefficient := (-33651583556929091792797696) }, { argument := 874941172480156386612740096, coefficient := (-874941172480156386612740096) }, { argument := 874941172480156386612740096, coefficient := (-874941172480156386612740096) }, { argument := 461507431637884687444082688, coefficient := (-461507431637884687444082688) }, { argument := 10797350952694677166660517888, coefficient := (-10797350952694677166660517888) }, { argument := 865326434321033788957655040, coefficient := (-865326434321033788957655040) }, { argument := 403819002683149101513572352, coefficient := (-403819002683149101513572352) }, { argument := 874941172480156386612740096, coefficient := (-874941172480156386612740096) }] }

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


end Parent3

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-50759556507551317574550119254065152)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3563, 22905, 3563, 46319, 46319, 1527,
    35455995, 1309342725, 10474739235, 283650525, 185341332699831, 35455995,
    11569851, 5063501226299563, 116818173, 1482730634033565, 234009567, 104875101,
    35455995, 11569851, 11569851, 427259205, 3418072803, 92559645,
    57210589119, 104043622465, 57210589119, 3772884381863, 2545, 3772875345753,
    1285, 119819926339449, 9302892284480845, 297311257417, 343903691737326919, 304988840973,
    9717158645, 297311257417, 169141746343, 304988840973, 4762106971939, 5831790867,
    9302897179233613, 297311257417, 9717158645, 5831790867, 9717158645, 149626609853,
    169141746343, 479296625242733, 10136689486296601, 53166545465, 355112061522506747, 1315589199485,
    41854514515, 710221116088246233, 21492858805, 21492858805, 727363590085, 39592108325,
    1315589199485, 727363590085, 20276456775683071, 41854514515
  ]
def negativeCoefficients : Array ℕ := #[
    33651583556929091792797696, 865326434321033788957655040, 33651583556929091792797696, 874941172480156386612740096, 874941172480156386612740096, 28844214477367792965255168,
    5232381325149803948393103360, 193224881222787721371372748800, 193224833906889172306372853760, 5232428641048353013392998400, 3338812627533240067851974344704, 5232381325149803948393103360,
    213426080367952529473929216, 11401991117976380733701041946624, 4309829880978654304860635136, 3338812565462191304233577349120, 4316714593248588257424310272, 3869208295702881340785426432,
    5232381325149803948393103360, 213426080367952529473929216, 213426080367952529473929216, 7881541207771604424358625280, 7881539277781005712496787456, 213428010358551241335767040,
    65959318486521587978043654144, 239908259514189090049941831680, 65959318486521587978043654144, 135932485570161367496349712384, 24036845397806494137712640, 135932160009988336465848827904,
    24272963721949976398397440, 134905243903475698803645874176, 10474125556463948952618957537280, 1371106168951044930649056083968, 96800283622472714784960742948864, 1406512773691558157000839790592,
    44812484661987321676122030080, 1371106168951044930649056083968, 780028626742404868622434435072, 1406512773691558157000839790592, 21961342140746671566262796025856, 860620428919565903398831128576,
    10474131067465634461494921920512, 1371106168951044930649056083968, 44812484661987321676122030080, 860620428919565903398831128576, 44812484661987321676122030080, 1380061889287539477043398836224,
    780028626742404868622434435072, 134910006427694287857907662848, 11412897748313949195720693121024, 245187414369024546799207055360, 399820636986882509060006507184128, 6067084317259054211222932029440,
    193019879396891664501503426560, 399818944220710439581148245917696, 198236632894104952731273789440, 198236632894104952731273789440, 3354372498708144331742343331840, 182586372402465088041962700800,
    6067084317259054211222932029440, 3354372498708144331742343331840, 11414630397420030919422249009152, 193019879396891664501503426560
  ]
def negativeScales : Array ℕ := #[
    11, 14, 11, 15, 15, 10,
    25, 30, 33, 28, 47, 25,
    23, 52, 26, 50, 27, 26,
    25, 23, 23, 28, 31, 26,
    35, 36, 35, 41, 11, 41,
    10, 46, 53, 38, 58, 38,
    33, 38, 37, 38, 42, 32,
    53, 38, 33, 32, 33, 37,
    37, 48, 53, 35, 58, 40,
    35, 59, 34, 34, 39, 35,
    40, 39, 54, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    11798876768764696, 14483374942405524, 11798876768764696, 15499316486274657, 15499316486274657, 10576484346799762,
    25079526247262615, 30286195631132324, 33286195277852663, 28079539293349914, 47397177978981594, 25079526247262615,
    23463866949318620, 52169056724248974, 26799689486506241, 50397177952160803, 27801992272406483, 26644096959170915,
    25079526247262615, 23463866949318620, 23463866949318620, 28670536333223874, 31670535979944212, 26463879995405919,
    35735563149460048, 36598397579045289, 35735563149460048, 41778805029229366, 11313449940963058, 41778801573950727,
    10327552644081241, 46767861180457815, 53046600745527115, 38113183134360057, 58254782216075618, 38149965501625266,
    33177887376868139, 38113183134360057, 37299441823017952, 38149965501625266, 42114737167100475, 32441291838302757,
    53046601504606493, 38113183134360057, 33177887376868139, 32441291838302757, 33177887376868139, 37122575813164988,
    37299441823017952, 48767912110641435, 53170436081631925, 35629799678191648, 58301051975987512, 40258846207974595,
    35284664192130326, 59301045867872258, 34323138339944962, 34323138339944962, 39403885753829332, 35204493843446343,
    40258846207974595, 39403885753829332, 54170655087760121, 35284664192130326
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
noncomputable def negativeCeiling : ℝ := 699616581457 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 33651583556929091792797696, coefficient := (-33651583556929091792797696) }, { argument := 865326434321033788957655040, coefficient := (-865326434321033788957655040) }, { argument := 33651583556929091792797696, coefficient := (-33651583556929091792797696) }, { argument := 874941172480156386612740096, coefficient := (-874941172480156386612740096) }, { argument := 874941172480156386612740096, coefficient := (-874941172480156386612740096) }, { argument := 28844214477367792965255168, coefficient := (-28844214477367792965255168) }, { argument := 5232381325149803948393103360, coefficient := (-5232381325149803948393103360) }, { argument := 193224881222787721371372748800, coefficient := (-193224881222787721371372748800) }, { argument := 193224833906889172306372853760, coefficient := (-193224833906889172306372853760) }, { argument := 5232428641048353013392998400, coefficient := (-5232428641048353013392998400) }, { argument := 3338812627533240067851974344704, coefficient := (-3338812627533240067851974344704) }, { argument := 5232381325149803948393103360, coefficient := (-5232381325149803948393103360) }, { argument := 213426080367952529473929216, coefficient := (-213426080367952529473929216) }, { argument := 11401991117976380733701041946624, coefficient := (-11401991117976380733701041946624) }, { argument := 4309829880978654304860635136, coefficient := (-4309829880978654304860635136) }, { argument := 3338812565462191304233577349120, coefficient := (-3338812565462191304233577349120) }, { argument := 4316714593248588257424310272, coefficient := (-4316714593248588257424310272) }, { argument := 3869208295702881340785426432, coefficient := (-3869208295702881340785426432) }, { argument := 5232381325149803948393103360, coefficient := (-5232381325149803948393103360) }, { argument := 213426080367952529473929216, coefficient := (-213426080367952529473929216) }, { argument := 213426080367952529473929216, coefficient := (-213426080367952529473929216) }, { argument := 7881541207771604424358625280, coefficient := (-7881541207771604424358625280) }, { argument := 7881539277781005712496787456, coefficient := (-7881539277781005712496787456) }, { argument := 213428010358551241335767040, coefficient := (-213428010358551241335767040) }, { argument := 65959318486521587978043654144, coefficient := (-65959318486521587978043654144) }, { argument := 239908259514189090049941831680, coefficient := (-239908259514189090049941831680) }, { argument := 65959318486521587978043654144, coefficient := (-65959318486521587978043654144) }, { argument := 135932485570161367496349712384, coefficient := (-135932485570161367496349712384) }, { argument := 24036845397806494137712640, coefficient := (-24036845397806494137712640) }, { argument := 135932160009988336465848827904, coefficient := (-135932160009988336465848827904) }, { argument := 24272963721949976398397440, coefficient := (-24272963721949976398397440) }, { argument := 134905243903475698803645874176, coefficient := (-134905243903475698803645874176) }, { argument := 10474125556463948952618957537280, coefficient := (-10474125556463948952618957537280) }, { argument := 1371106168951044930649056083968, coefficient := (-1371106168951044930649056083968) }, { argument := 96800283622472714784960742948864, coefficient := (-96800283622472714784960742948864) }, { argument := 1406512773691558157000839790592, coefficient := (-1406512773691558157000839790592) }, { argument := 44812484661987321676122030080, coefficient := (-44812484661987321676122030080) }, { argument := 1371106168951044930649056083968, coefficient := (-1371106168951044930649056083968) }, { argument := 780028626742404868622434435072, coefficient := (-780028626742404868622434435072) }, { argument := 1406512773691558157000839790592, coefficient := (-1406512773691558157000839790592) }, { argument := 21961342140746671566262796025856, coefficient := (-21961342140746671566262796025856) }, { argument := 860620428919565903398831128576, coefficient := (-860620428919565903398831128576) }, { argument := 10474131067465634461494921920512, coefficient := (-10474131067465634461494921920512) }, { argument := 1371106168951044930649056083968, coefficient := (-1371106168951044930649056083968) }, { argument := 44812484661987321676122030080, coefficient := (-44812484661987321676122030080) }, { argument := 860620428919565903398831128576, coefficient := (-860620428919565903398831128576) }, { argument := 44812484661987321676122030080, coefficient := (-44812484661987321676122030080) }, { argument := 1380061889287539477043398836224, coefficient := (-1380061889287539477043398836224) }, { argument := 780028626742404868622434435072, coefficient := (-780028626742404868622434435072) }, { argument := 134910006427694287857907662848, coefficient := (-134910006427694287857907662848) }, { argument := 11412897748313949195720693121024, coefficient := (-11412897748313949195720693121024) }, { argument := 245187414369024546799207055360, coefficient := (-245187414369024546799207055360) }, { argument := 399820636986882509060006507184128, coefficient := (-399820636986882509060006507184128) }, { argument := 6067084317259054211222932029440, coefficient := (-6067084317259054211222932029440) }, { argument := 193019879396891664501503426560, coefficient := (-193019879396891664501503426560) }, { argument := 399818944220710439581148245917696, coefficient := (-399818944220710439581148245917696) }, { argument := 198236632894104952731273789440, coefficient := (-198236632894104952731273789440) }, { argument := 198236632894104952731273789440, coefficient := (-198236632894104952731273789440) }, { argument := 3354372498708144331742343331840, coefficient := (-3354372498708144331742343331840) }, { argument := 182586372402465088041962700800, coefficient := (-182586372402465088041962700800) }, { argument := 6067084317259054211222932029440, coefficient := (-6067084317259054211222932029440) }, { argument := 3354372498708144331742343331840, coefficient := (-3354372498708144331742343331840) }, { argument := 11414630397420030919422249009152, coefficient := (-11414630397420030919422249009152) }, { argument := 193019879396891664501503426560, coefficient := (-193019879396891664501503426560) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10
