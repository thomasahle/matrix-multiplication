import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 1, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3223386566066401525023604972978176)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    17489072391, 11681053307, 281732269, 10857528213, 65015139, 34915897685,
    43487181351, 8706079515, 7711098999, 360929182179, 98254325955, 21743592063,
    360929182179, 8706079515, 8706079515, 3731176935, 8706079515, 98254325955,
    3731176935, 17457947455, 7711098999, 48191013825, 1287806274675, 153498263625,
    79342055625, 157511290125, 5016283125, 153498263625, 87283326375, 157511290125,
    2458981987875, 3009769875, 643903138725, 153498263625, 5016283125, 3009769875,
    5016283125, 77250760125, 87283326375, 48191013825, 47027375, 3937561425,
    1968781425, 23512975, 1089448905, 114226752795, 1231250225625, 57113419965,
    1089448905, 5292843687, 1168834023, 10905212367, 28922424867, 920145933,
    10905216813, 472507371, 472507371, 15990644187, 870408315, 28922424867,
    15990644187, 5292839241, 920145933, 870408315
  ]
def negativeCoefficients : Array ℕ := #[
    20163527655209786757523439616, 13467337554099225603847749632, 649630382943561902968537088, 12517877763643250514893733888, 599658815024826371970957312, 80510578587377850328935301120,
    100274613108611472803235889152, 80299410349285188691946373120, 71122334880795452841438216192, 3328984126194651679771833925632, 906236202513361415237680496640, 100274619507325823371236605952,
    3328984126194651679771833925632, 80299410349285188691946373120, 80299410349285188691946373120, 68828066013673018878811176960, 80299410349285188691946373120, 906236202513361415237680496640,
    68828066013673018878811176960, 80510572188663499760934584320, 71122334880795452841438216192, 55560456167648363810075443200, 1484739547840439454660349132800, 1415771592424587592816656384000,
    91475162149775146525655040000, 1452785228827844784785719296000, 46267045504071489961328640000, 1415771592424587592816656384000, 805046591770843925327118336000, 1452785228827844784785719296000,
    22680105706095844379043299328000, 888327273678172607257509888000, 1484739551039796629944349491200, 1415771592424587592816656384000, 46267045504071489961328640000, 888327273678172607257509888000,
    46267045504071489961328640000, 1425025001525401890808922112000, 805046591770843925327118336000, 55560456167648363810075443200, 216875487770841681231872000, 18158796970371521774302003200,
    18158803542024098033329766400, 216868916118265422204108800, 1256049070744881893505761280, 131694479698765763191945297920, 1419534862675094816119848960000, 131694580158581067109556551680,
    1256049070744881893505761280, 24408933229059565735586562048, 21561182086925343748855431168, 100582830801750680924414017536, 533524569512642016594018435072, 16973696536515696142715977728,
    100582871808862756780747259904, 17432445091556660903329923072, 17432445091556660903329923072, 294975320891340341074766856192, 16056199426433766621488087040, 533524569512642016594018435072,
    294975320891340341074766856192, 24408912725503527807419940864, 16973696536515696142715977728, 16056199426433766621488087040
  ]
def negativeScales : Array ℕ := #[
    34, 33, 28, 33, 25, 35,
    35, 33, 32, 38, 36, 34,
    38, 33, 33, 31, 33, 36,
    31, 34, 32, 35, 40, 37,
    36, 37, 32, 37, 36, 37,
    41, 31, 39, 37, 32, 31,
    32, 36, 36, 35, 25, 31,
    30, 24, 30, 36, 40, 35,
    30, 32, 30, 33, 34, 29,
    33, 28, 28, 33, 29, 34,
    33, 32, 29, 29
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34025734720557793, 33443451320032554, 28069749575421104, 33337976650475221, 25954272369203013, 35023165013649317,
    35339871151519794, 33019376050699751, 32844289345694277, 38392924837821534, 36515801876819706, 34339871243580914,
    38392924837821534, 33019376050699751, 33019376050699751, 31796983629970729, 33019376050699751, 36515801876819706,
    31796983629970729, 34023164898988685, 32844289345694277, 35488045101163877, 40228052723105329, 37159431379657612,
    36207366724748242, 37196664285856588, 32223971631852323, 37159431379657612, 36344987032813690, 37196664285856588,
    41161198305831800, 31487006037686291, 39228052726214087, 37159431379657612, 32223971631852323, 31487006037686291,
    32223971631852323, 36168830077659862, 36344987032813690, 35488045101163877, 25486997469506163, 31874655286106166,
    30874655808216158, 24486953753020149, 30020951389832750, 36733109624603961, 40163261127589374, 35733110725127103,
    30020951389832750, 32301395901626176, 30122422932533754, 33344298814022808, 34751469462561547, 29777287446888720,
    33344299402202169, 28815761595187559, 28815761595187559, 33896509012286151, 29697117097868714, 34751469462561547,
    33896509012286151, 32301394689758751, 29777287446888720, 29697117097868714
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
noncomputable def negativeCeiling : ℝ := 4784739011 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 20163527655209786757523439616, coefficient := (-20163527655209786757523439616) }, { argument := 13467337554099225603847749632, coefficient := (-13467337554099225603847749632) }, { argument := 649630382943561902968537088, coefficient := (-649630382943561902968537088) }, { argument := 12517877763643250514893733888, coefficient := (-12517877763643250514893733888) }, { argument := 599658815024826371970957312, coefficient := (-599658815024826371970957312) }, { argument := 80510578587377850328935301120, coefficient := (-80510578587377850328935301120) }, { argument := 100274613108611472803235889152, coefficient := (-100274613108611472803235889152) }, { argument := 80299410349285188691946373120, coefficient := (-80299410349285188691946373120) }, { argument := 71122334880795452841438216192, coefficient := (-71122334880795452841438216192) }, { argument := 3328984126194651679771833925632, coefficient := (-3328984126194651679771833925632) }, { argument := 906236202513361415237680496640, coefficient := (-906236202513361415237680496640) }, { argument := 100274619507325823371236605952, coefficient := (-100274619507325823371236605952) }, { argument := 3328984126194651679771833925632, coefficient := (-3328984126194651679771833925632) }, { argument := 80299410349285188691946373120, coefficient := (-80299410349285188691946373120) }, { argument := 80299410349285188691946373120, coefficient := (-80299410349285188691946373120) }, { argument := 68828066013673018878811176960, coefficient := (-68828066013673018878811176960) }, { argument := 80299410349285188691946373120, coefficient := (-80299410349285188691946373120) }, { argument := 906236202513361415237680496640, coefficient := (-906236202513361415237680496640) }, { argument := 68828066013673018878811176960, coefficient := (-68828066013673018878811176960) }, { argument := 80510572188663499760934584320, coefficient := (-80510572188663499760934584320) }, { argument := 71122334880795452841438216192, coefficient := (-71122334880795452841438216192) }, { argument := 55560456167648363810075443200, coefficient := (-55560456167648363810075443200) }, { argument := 1484739547840439454660349132800, coefficient := (-1484739547840439454660349132800) }, { argument := 1415771592424587592816656384000, coefficient := (-1415771592424587592816656384000) }, { argument := 91475162149775146525655040000, coefficient := (-91475162149775146525655040000) }, { argument := 1452785228827844784785719296000, coefficient := (-1452785228827844784785719296000) }, { argument := 46267045504071489961328640000, coefficient := (-46267045504071489961328640000) }, { argument := 1415771592424587592816656384000, coefficient := (-1415771592424587592816656384000) }, { argument := 805046591770843925327118336000, coefficient := (-805046591770843925327118336000) }, { argument := 1452785228827844784785719296000, coefficient := (-1452785228827844784785719296000) }, { argument := 22680105706095844379043299328000, coefficient := (-22680105706095844379043299328000) }, { argument := 888327273678172607257509888000, coefficient := (-888327273678172607257509888000) }, { argument := 1484739551039796629944349491200, coefficient := (-1484739551039796629944349491200) }, { argument := 1415771592424587592816656384000, coefficient := (-1415771592424587592816656384000) }, { argument := 46267045504071489961328640000, coefficient := (-46267045504071489961328640000) }, { argument := 888327273678172607257509888000, coefficient := (-888327273678172607257509888000) }, { argument := 46267045504071489961328640000, coefficient := (-46267045504071489961328640000) }, { argument := 1425025001525401890808922112000, coefficient := (-1425025001525401890808922112000) }, { argument := 805046591770843925327118336000, coefficient := (-805046591770843925327118336000) }, { argument := 55560456167648363810075443200, coefficient := (-55560456167648363810075443200) }, { argument := 216875487770841681231872000, coefficient := (-216875487770841681231872000) }, { argument := 18158796970371521774302003200, coefficient := (-18158796970371521774302003200) }, { argument := 18158803542024098033329766400, coefficient := (-18158803542024098033329766400) }, { argument := 216868916118265422204108800, coefficient := (-216868916118265422204108800) }, { argument := 1256049070744881893505761280, coefficient := (-1256049070744881893505761280) }, { argument := 131694479698765763191945297920, coefficient := (-131694479698765763191945297920) }, { argument := 1419534862675094816119848960000, coefficient := (-1419534862675094816119848960000) }, { argument := 131694580158581067109556551680, coefficient := (-131694580158581067109556551680) }, { argument := 1256049070744881893505761280, coefficient := (-1256049070744881893505761280) }, { argument := 24408933229059565735586562048, coefficient := (-24408933229059565735586562048) }, { argument := 21561182086925343748855431168, coefficient := (-21561182086925343748855431168) }, { argument := 100582830801750680924414017536, coefficient := (-100582830801750680924414017536) }, { argument := 533524569512642016594018435072, coefficient := (-533524569512642016594018435072) }, { argument := 16973696536515696142715977728, coefficient := (-16973696536515696142715977728) }, { argument := 100582871808862756780747259904, coefficient := (-100582871808862756780747259904) }, { argument := 17432445091556660903329923072, coefficient := (-17432445091556660903329923072) }, { argument := 17432445091556660903329923072, coefficient := (-17432445091556660903329923072) }, { argument := 294975320891340341074766856192, coefficient := (-294975320891340341074766856192) }, { argument := 16056199426433766621488087040, coefficient := (-16056199426433766621488087040) }, { argument := 533524569512642016594018435072, coefficient := (-533524569512642016594018435072) }, { argument := 294975320891340341074766856192, coefficient := (-294975320891340341074766856192) }, { argument := 24408912725503527807419940864, coefficient := (-24408912725503527807419940864) }, { argument := 16973696536515696142715977728, coefficient := (-16973696536515696142715977728) }, { argument := 16056199426433766621488087040, coefficient := (-16056199426433766621488087040) }] }

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
def constantNumerator : ℤ := (-2495238905495674424339694627061760)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1168834023, 34695825, 3637794675, 39211790625, 1818898725, 34695825,
    2014570285, 35252468615, 35252485905, 2014552995, 48374375, 1323162125,
    386994875, 47027375, 3937561425, 1968781425, 23512975, 1591505375,
    133255368225, 66627708225, 795728575, 1061692245, 111316517055, 1199880793125,
    55658300985, 1061692245, 86629375, 7253402625, 3626702625, 43313375,
    603707355, 63297627345, 682285156875, 31648837815, 603707355, 1784333681,
    31223615059, 31223630373, 1784318367, 2878570375, 241020207225, 120510147225,
    1439241575, 1089448905, 114226752795, 1231250225625, 57113419965, 1089448905,
    1591505375, 133255368225, 66627708225, 795728575, 17007893415, 1783246949685,
    19221619764375, 891624154995, 17007893415, 83518328101, 1461466627439, 1461467344233,
    83517611307, 20817495, 2182676805, 23527074375
  ]
def negativeCoefficients : Array ℕ := #[
    21561182086925343748855431168, 40001562762575856481075200, 4194091710151775897832652800, 45208116645703656564326400000, 4194094909508951181833011200, 40001562762575856481075200,
    2322641404118444525391708160, 81286658313422901871095316480, 81286698181448531175863746560, 2322621470105629873007493120, 446174857675326745477120000, 1525502067993792934313984000,
    446174713560138669621248000, 216875487770841681231872000, 18158796970371521774302003200, 18158803542024098033329766400, 216868916118265422204108800, 3669761543069768448212992000,
    307265959261812855286215475200, 307266070461091974616606310400, 3669650343790649117822156800, 1224047820534821208320901120, 128339206330644342473679175680, 1383368369358531890868387840000,
    128339304230973906164090142720, 1224047820534821208320901120, 199753738736301548503040000, 16725207735868506897383424000, 16725213788706406083330048000, 199747685898402362556416000,
    696027192068819902770708480, 72977195756640900622288158720, 786621229635243624219279360000, 72977251425455750563894394880, 696027192068819902770708480, 2057196672219193722489798656,
    71996754506174570228684423168, 71996789817854413327193604096, 2057179016379272173235208192, 6637531375723391454543872000, 555754759909002100618769203200, 555754961036158579283224166400,
    6637330248566912790088908800, 1256049070744881893505761280, 131694479698765763191945297920, 1419534862675094816119848960000, 131694580158581067109556551680, 1256049070744881893505761280,
    3669761543069768448212992000, 307265959261812855286215475200, 307266070461091974616606310400, 3669650343790649117822156800, 19608766066214684847023063040, 2055943756316400545117566402560,
    22161018779723932447832801280000, 2055945324641287869334542090240, 19608766066214684847023063040, 96290076496453228752667672576, 3369912606079332303284551548928, 3369914258893766249605094178816,
    96289250089236255592396357632, 768030005041456444436643840, 80526560834914097238386933760, 867995839597510206035066880000
  ]
def negativeScales : Array ℕ := #[
    30, 25, 31, 35, 30, 25,
    30, 35, 35, 30, 25, 30,
    28, 25, 31, 30, 24, 30,
    36, 35, 29, 29, 36, 40,
    35, 29, 26, 32, 31, 25,
    29, 35, 39, 34, 29, 30,
    34, 34, 30, 31, 37, 36,
    30, 30, 36, 40, 35, 30,
    30, 36, 35, 29, 33, 40,
    44, 39, 33, 36, 40, 40,
    36, 24, 31, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30122422932533754, 25048258735828486, 31760416970726828, 35190568473585109, 30760418071249973, 25048258735828486,
    30907824998598603, 35037005237134468, 35037005944721543, 30907812616649604, 25527739685878029, 30301342697616007,
    28527739219885163, 25486997469506163, 31874655286106166, 30874655808216158, 24486953753020149, 30567744883392607,
    36955402708654109, 35955403230764174, 29567701166906591, 29983718501853114, 36695876718315895, 40126028221390399,
    35695877818839035, 29983718501853114, 26368352973007371, 32756010787110957, 31756011309220926, 25368309256521358,
    29169274136789852, 35881432374525255, 39311583874546475, 34881433475048456, 29169274136789852, 30732738287171960,
    34861918532747236, 34861919240334340, 30732725905224023, 31422705337535638, 37810363152179750, 36810363674289724,
    30422661621049624, 30020951389832750, 36733109624603961, 40163261127589374, 35733110725127103, 30020951389832750,
    30567744883392607, 36955402708654109, 35955403230764174, 29567701166906591, 33985485428557157, 40697643644492884,
    44127795147564586, 39697644745016024, 33985485428557157, 36281373780698345, 40410554024256256, 40410554731843331,
    36281361398750450, 24311293141662280, 31023451376278724, 34453602879418956
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
noncomputable def negativeCeiling : ℝ := 5196610493 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 21561182086925343748855431168, coefficient := (-21561182086925343748855431168) }, { argument := 40001562762575856481075200, coefficient := (-40001562762575856481075200) }, { argument := 4194091710151775897832652800, coefficient := (-4194091710151775897832652800) }, { argument := 45208116645703656564326400000, coefficient := (-45208116645703656564326400000) }, { argument := 4194094909508951181833011200, coefficient := (-4194094909508951181833011200) }, { argument := 40001562762575856481075200, coefficient := (-40001562762575856481075200) }, { argument := 2322641404118444525391708160, coefficient := (-2322641404118444525391708160) }, { argument := 81286658313422901871095316480, coefficient := (-81286658313422901871095316480) }, { argument := 81286698181448531175863746560, coefficient := (-81286698181448531175863746560) }, { argument := 2322621470105629873007493120, coefficient := (-2322621470105629873007493120) }, { argument := 446174857675326745477120000, coefficient := (-446174857675326745477120000) }, { argument := 1525502067993792934313984000, coefficient := (-1525502067993792934313984000) }, { argument := 446174713560138669621248000, coefficient := (-446174713560138669621248000) }, { argument := 216875487770841681231872000, coefficient := (-216875487770841681231872000) }, { argument := 18158796970371521774302003200, coefficient := (-18158796970371521774302003200) }, { argument := 18158803542024098033329766400, coefficient := (-18158803542024098033329766400) }, { argument := 216868916118265422204108800, coefficient := (-216868916118265422204108800) }, { argument := 3669761543069768448212992000, coefficient := (-3669761543069768448212992000) }, { argument := 307265959261812855286215475200, coefficient := (-307265959261812855286215475200) }, { argument := 307266070461091974616606310400, coefficient := (-307266070461091974616606310400) }, { argument := 3669650343790649117822156800, coefficient := (-3669650343790649117822156800) }, { argument := 1224047820534821208320901120, coefficient := (-1224047820534821208320901120) }, { argument := 128339206330644342473679175680, coefficient := (-128339206330644342473679175680) }, { argument := 1383368369358531890868387840000, coefficient := (-1383368369358531890868387840000) }, { argument := 128339304230973906164090142720, coefficient := (-128339304230973906164090142720) }, { argument := 1224047820534821208320901120, coefficient := (-1224047820534821208320901120) }, { argument := 199753738736301548503040000, coefficient := (-199753738736301548503040000) }, { argument := 16725207735868506897383424000, coefficient := (-16725207735868506897383424000) }, { argument := 16725213788706406083330048000, coefficient := (-16725213788706406083330048000) }, { argument := 199747685898402362556416000, coefficient := (-199747685898402362556416000) }, { argument := 696027192068819902770708480, coefficient := (-696027192068819902770708480) }, { argument := 72977195756640900622288158720, coefficient := (-72977195756640900622288158720) }, { argument := 786621229635243624219279360000, coefficient := (-786621229635243624219279360000) }, { argument := 72977251425455750563894394880, coefficient := (-72977251425455750563894394880) }, { argument := 696027192068819902770708480, coefficient := (-696027192068819902770708480) }, { argument := 2057196672219193722489798656, coefficient := (-2057196672219193722489798656) }, { argument := 71996754506174570228684423168, coefficient := (-71996754506174570228684423168) }, { argument := 71996789817854413327193604096, coefficient := (-71996789817854413327193604096) }, { argument := 2057179016379272173235208192, coefficient := (-2057179016379272173235208192) }, { argument := 6637531375723391454543872000, coefficient := (-6637531375723391454543872000) }, { argument := 555754759909002100618769203200, coefficient := (-555754759909002100618769203200) }, { argument := 555754961036158579283224166400, coefficient := (-555754961036158579283224166400) }, { argument := 6637330248566912790088908800, coefficient := (-6637330248566912790088908800) }, { argument := 1256049070744881893505761280, coefficient := (-1256049070744881893505761280) }, { argument := 131694479698765763191945297920, coefficient := (-131694479698765763191945297920) }, { argument := 1419534862675094816119848960000, coefficient := (-1419534862675094816119848960000) }, { argument := 131694580158581067109556551680, coefficient := (-131694580158581067109556551680) }, { argument := 1256049070744881893505761280, coefficient := (-1256049070744881893505761280) }, { argument := 3669761543069768448212992000, coefficient := (-3669761543069768448212992000) }, { argument := 307265959261812855286215475200, coefficient := (-307265959261812855286215475200) }, { argument := 307266070461091974616606310400, coefficient := (-307266070461091974616606310400) }, { argument := 3669650343790649117822156800, coefficient := (-3669650343790649117822156800) }, { argument := 19608766066214684847023063040, coefficient := (-19608766066214684847023063040) }, { argument := 2055943756316400545117566402560, coefficient := (-2055943756316400545117566402560) }, { argument := 22161018779723932447832801280000, coefficient := (-22161018779723932447832801280000) }, { argument := 2055945324641287869334542090240, coefficient := (-2055945324641287869334542090240) }, { argument := 19608766066214684847023063040, coefficient := (-19608766066214684847023063040) }, { argument := 96290076496453228752667672576, coefficient := (-96290076496453228752667672576) }, { argument := 3369912606079332303284551548928, coefficient := (-3369912606079332303284551548928) }, { argument := 3369914258893766249605094178816, coefficient := (-3369914258893766249605094178816) }, { argument := 96289250089236255592396357632, coefficient := (-96289250089236255592396357632) }, { argument := 768030005041456444436643840, coefficient := (-768030005041456444436643840) }, { argument := 80526560834914097238386933760, coefficient := (-80526560834914097238386933760) }, { argument := 867995839597510206035066880000, coefficient := (-867995839597510206035066880000) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1
