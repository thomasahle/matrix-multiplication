import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 23, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk23

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
def constantNumerator : ℤ := (-377345176231022385176069307105280)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    738299, 123, 12318211, 1287, 57, 24636419,
    57, 111, 2097, 111, 1287, 2097,
    184575, 111, 111, 123, 20670654499, 2055208715,
    1702887221, 325125067985, 11450448555, 20670652087, 45860514469, 45860514469,
    32824619191, 1702887221, 19150989347, 1807524459, 19150989445, 1807524459,
    1807524459, 6501611727, 903762531, 2055208715, 2055209205, 1581103,
    1702887221, 1702887627, 123, 20670654597, 2055209205, 1702887627,
    325125075279, 11450451285, 20670652185, 45860525403, 45860525403, 32824627017,
    1702887627, 302922648785, 6501611727, 302922656079, 6501611727, 53362643,
    11450448555, 11450451285, 1287, 57, 19150987447, 903762531,
    19150987545, 903762531, 53362637, 57
  ]
def negativeCoefficients : Array ℕ := #[
    13946073807744704766506172416, 2379166013001590215821754368, 465368854042529401899579342848, 24894200477504443965549576192, 2205080694977083614664065024, 465368797374131607463836778496,
    2205080694977083614664065024, 2147052255635581414278168576, 81123758199420076139483234304, 2147052255635581414278168576, 24894200477504443965549576192, 81123758199420076139483234304,
    13946092697210636245087027200, 2147052255635581414278168576, 2147052255635581414278168576, 2379166013001590215821754368, 95326568344781482682635780096, 37911909183662472859945533440,
    1963295297011092344532893696, 374843682566669613768491663360, 52805873505815587197781278720, 95326557221394806235776155648, 52873573343643555899316895744, 52873573343643555899316895744,
    37844209345834504158409916416, 1963295297011092344532893696, 88318349810611751442540658688, 33342941102143313407842975744, 88318350262556981248424673280, 33342941102143313407842975744,
    33342941102143313407842975744, 119933567594597773178497400832, 33342952225529989854702600192, 37911909183662472859945533440, 37911918222567068977625825280, 14933095626329289312620773376,
    1963295297011092344532893696, 1963295765097223214912765952, 2379166013001590215821754368, 95326568796726712488519794688, 37911918222567068977625825280, 1963295765097223214912765952,
    374843690976079068370833506304, 52805886095718417504550256640, 95326557673340036041660170240, 52873585949687287270581731328, 52873585949687287270581731328, 37844218368598199211594350592,
    1963295765097223214912765952, 349246036016693666017087324160, 119933567594597773178497400832, 349246044426103120619429167104, 119933567594597773178497400832, 503995913481076986150236717056,
    52805873505815587197781278720, 52805886095718417504550256640, 24894200477504443965549576192, 2205080694977083614664065024, 88318341048408316430503641088, 33342952225529989854702600192,
    88318341500353546236387655680, 33342952225529989854702600192, 503995856812679191714494152704, 2205080694977083614664065024
  ]
def negativeScales : Array ℕ := #[
    19, 6, 23, 10, 5, 24,
    5, 6, 11, 6, 10, 11,
    17, 6, 6, 6, 34, 30,
    30, 38, 33, 34, 35, 35,
    34, 30, 34, 30, 34, 30,
    30, 32, 29, 30, 30, 20,
    30, 30, 6, 34, 30, 30,
    38, 33, 34, 35, 35, 34,
    30, 38, 32, 38, 32, 25,
    33, 33, 10, 5, 34, 29,
    34, 29, 25, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19493845678875949, 6942514514520450, 23554289409788090, 10329796338220703, 5832890015409720, 24554289234109763,
    5832890015409720, 6794415866926375, 11034111146096593, 6794415866926375, 10329796338220703, 11034111146096593,
    17493847632954262, 6794415866926375, 6794415866926375, 6942514514520450, 34266865018697098, 30936637775323595,
    30665335745233840, 38242203839602800, 33414685063824566, 34266864850353099, 35416533488216936, 35416533488216936,
    34934059230861994, 30665335745233840, 34156699873093929, 30751368023739724, 34156699880476530, 30751368023739724,
    30751368023739724, 32598150255566273, 29751368505030566, 30936637775323595, 30936638119288945, 20592499923583526,
    30665335745233840, 30665336089199142, 6942514514520450, 34266865025536945, 30936638119288945, 30665336089199142,
    38242203871968860, 33414685407789868, 34266864857192947, 35416533832182237, 35416533832182237, 34934059574827343,
    30665336089199142, 38140158492703930, 32598150255566273, 38140158527442229, 32598150255566273, 25669326787825646,
    33414685063824566, 33414685407789868, 10329796338220703, 5832890015409720, 34156699729961861, 29751368505030566,
    34156699737344463, 29751368505030566, 25669326625611590, 5832890015409720
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
noncomputable def negativeCeiling : ℝ := 518424989 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 13946073807744704766506172416, coefficient := (-13946073807744704766506172416) }, { argument := 2379166013001590215821754368, coefficient := (-2379166013001590215821754368) }, { argument := 465368854042529401899579342848, coefficient := (-465368854042529401899579342848) }, { argument := 24894200477504443965549576192, coefficient := (-24894200477504443965549576192) }, { argument := 2205080694977083614664065024, coefficient := (-2205080694977083614664065024) }, { argument := 465368797374131607463836778496, coefficient := (-465368797374131607463836778496) }, { argument := 2205080694977083614664065024, coefficient := (-2205080694977083614664065024) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 81123758199420076139483234304, coefficient := (-81123758199420076139483234304) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 24894200477504443965549576192, coefficient := (-24894200477504443965549576192) }, { argument := 81123758199420076139483234304, coefficient := (-81123758199420076139483234304) }, { argument := 13946092697210636245087027200, coefficient := (-13946092697210636245087027200) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 2379166013001590215821754368, coefficient := (-2379166013001590215821754368) }, { argument := 95326568344781482682635780096, coefficient := (-95326568344781482682635780096) }, { argument := 37911909183662472859945533440, coefficient := (-37911909183662472859945533440) }, { argument := 1963295297011092344532893696, coefficient := (-1963295297011092344532893696) }, { argument := 374843682566669613768491663360, coefficient := (-374843682566669613768491663360) }, { argument := 52805873505815587197781278720, coefficient := (-52805873505815587197781278720) }, { argument := 95326557221394806235776155648, coefficient := (-95326557221394806235776155648) }, { argument := 52873573343643555899316895744, coefficient := (-52873573343643555899316895744) }, { argument := 52873573343643555899316895744, coefficient := (-52873573343643555899316895744) }, { argument := 37844209345834504158409916416, coefficient := (-37844209345834504158409916416) }, { argument := 1963295297011092344532893696, coefficient := (-1963295297011092344532893696) }, { argument := 88318349810611751442540658688, coefficient := (-88318349810611751442540658688) }, { argument := 33342941102143313407842975744, coefficient := (-33342941102143313407842975744) }, { argument := 88318350262556981248424673280, coefficient := (-88318350262556981248424673280) }, { argument := 33342941102143313407842975744, coefficient := (-33342941102143313407842975744) }, { argument := 33342941102143313407842975744, coefficient := (-33342941102143313407842975744) }, { argument := 119933567594597773178497400832, coefficient := (-119933567594597773178497400832) }, { argument := 33342952225529989854702600192, coefficient := (-33342952225529989854702600192) }, { argument := 37911909183662472859945533440, coefficient := (-37911909183662472859945533440) }, { argument := 37911918222567068977625825280, coefficient := (-37911918222567068977625825280) }, { argument := 14933095626329289312620773376, coefficient := (-14933095626329289312620773376) }, { argument := 1963295297011092344532893696, coefficient := (-1963295297011092344532893696) }, { argument := 1963295765097223214912765952, coefficient := (-1963295765097223214912765952) }, { argument := 2379166013001590215821754368, coefficient := (-2379166013001590215821754368) }, { argument := 95326568796726712488519794688, coefficient := (-95326568796726712488519794688) }, { argument := 37911918222567068977625825280, coefficient := (-37911918222567068977625825280) }, { argument := 1963295765097223214912765952, coefficient := (-1963295765097223214912765952) }, { argument := 374843690976079068370833506304, coefficient := (-374843690976079068370833506304) }, { argument := 52805886095718417504550256640, coefficient := (-52805886095718417504550256640) }, { argument := 95326557673340036041660170240, coefficient := (-95326557673340036041660170240) }, { argument := 52873585949687287270581731328, coefficient := (-52873585949687287270581731328) }, { argument := 52873585949687287270581731328, coefficient := (-52873585949687287270581731328) }, { argument := 37844218368598199211594350592, coefficient := (-37844218368598199211594350592) }, { argument := 1963295765097223214912765952, coefficient := (-1963295765097223214912765952) }, { argument := 349246036016693666017087324160, coefficient := (-349246036016693666017087324160) }, { argument := 119933567594597773178497400832, coefficient := (-119933567594597773178497400832) }, { argument := 349246044426103120619429167104, coefficient := (-349246044426103120619429167104) }, { argument := 119933567594597773178497400832, coefficient := (-119933567594597773178497400832) }, { argument := 503995913481076986150236717056, coefficient := (-503995913481076986150236717056) }, { argument := 52805873505815587197781278720, coefficient := (-52805873505815587197781278720) }, { argument := 52805886095718417504550256640, coefficient := (-52805886095718417504550256640) }, { argument := 24894200477504443965549576192, coefficient := (-24894200477504443965549576192) }, { argument := 2205080694977083614664065024, coefficient := (-2205080694977083614664065024) }, { argument := 88318341048408316430503641088, coefficient := (-88318341048408316430503641088) }, { argument := 33342952225529989854702600192, coefficient := (-33342952225529989854702600192) }, { argument := 88318341500353546236387655680, coefficient := (-88318341500353546236387655680) }, { argument := 33342952225529989854702600192, coefficient := (-33342952225529989854702600192) }, { argument := 503995856812679191714494152704, coefficient := (-503995856812679191714494152704) }, { argument := 2205080694977083614664065024, coefficient := (-2205080694977083614664065024) }] }

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
def constantNumerator : ℤ := 701169510237006879736355197288448
def positiveArguments : Array ℕ := #[
    5, 27, 123, 3, 1287, 57,
    3, 57, 111, 2097, 111, 1287,
    2097, 27, 111, 111, 123, 49,
    245, 203, 3647, 1365, 49, 5467,
    5467, 3913, 203, 549, 603, 549,
    603, 17, 7, 130023417, 130023431, 52206793,
    378375387, 104413587
  ]
def positiveCoefficients : Array ℕ := #[
    6338253001141147007483516026880, 4178047632588158427784544256, 4758332026003180431643508736, 3713820117856140824697372672, 49788400955008887931099152384, 4410161389954167229328130048,
    3713820117856140824697372672, 4410161389954167229328130048, 4294104511271162828556337152, 162247516398840152278966468608, 4294104511271162828556337152, 49788400955008887931099152384,
    162247516398840152278966468608, 4178047632588158427784544256, 4294104511271162828556337152, 4294104511271162828556337152, 4758332026003180431643508736, 7582382740622954183757135872,
    151647654812459083675142717440, 7853182124216631118891319296, 141086478852305683204909563904, 211223519203068009404663070720, 7582382740622954183757135872, 211494318586661686339797254144,
    211494318586661686339797254144, 151376855428865406740008534016, 7853182124216631118891319296, 339814540783836885459809599488, 373238921844542152882085953536, 339814540783836885459809599488,
    373238921844542152882085953536, 1346878762742493739090247155712, 1109194275199700726309615304704, 1228036452857966472524898238464, 1228036585084227992874964221952, 493079218882627227309735673856,
    1786827245511630878284921700352, 493079223604993710179380887552
  ]
def positiveScales : Array ℕ := #[
    2, 4, 6, 1, 10, 5,
    1, 5, 6, 11, 6, 10,
    11, 4, 6, 6, 6, 5,
    7, 7, 11, 10, 5, 12,
    12, 11, 7, 9, 9, 9,
    9, 4, 2, 26, 26, 25,
    28, 26
  ]
def negativeArguments : Array ℕ := #[
    1807524459, 6501611727, 903762531, 45860514469, 45860525403, 111,
    45860514469, 45860525403, 2097, 111, 32824619191, 32824627017,
    1287, 2097, 1581105, 1702887221, 1702887627, 111,
    111, 123, 3, 7, 9, 17,
    7, 31
  ]
def negativeCoefficients : Array ℕ := #[
    33342941102143313407842975744, 119933567594597773178497400832, 33342952225529989854702600192, 52873573343643555899316895744, 52873585949687287270581731328, 2147052255635581414278168576,
    52873573343643555899316895744, 52873585949687287270581731328, 81123758199420076139483234304, 2147052255635581414278168576, 37844209345834504158409916416, 37844218368598199211594350592,
    24894200477504443965549576192, 81123758199420076139483234304, 14933114515795220791201628160, 1963295297011092344532893696, 1963295765097223214912765952, 2147052255635581414278168576,
    2147052255635581414278168576, 2379166013001590215821754368, 475368975085586025561263702016, 1109194275199700726309615304704, 1426106925256758076683791106048, 1346878762742493739090247155712,
    1109194275199700726309615304704, 2456073037942194465399862460416
  ]
def negativeScales : Array ℕ := #[
    30, 32, 29, 35, 35, 6,
    35, 35, 11, 6, 34, 34,
    10, 11, 20, 30, 30, 6,
    6, 6, 1, 2, 3, 4,
    2, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 4754887502147955, 6942514504772358, 1584962500720924, 10329796338220701, 5832890014087662,
    1584962500720924, 5832890014087662, 6794415866314396, 11034111146096592, 6794415866314396, 10329796338220701,
    11034111146096592, 4754887502147955, 6794415866314396, 6794415866314396, 6942514504772358, 5614709844114682,
    7936637938489789, 7665335917183229, 11832494484259625, 10414685235807213, 5614709844114682, 12416533660199582,
    12416533660199582, 11934059394410200, 7665335917183229, 9100662339005198, 9236014191900084, 9100662339005198,
    9236014191900084, 4087462841250339, 2807354922011143, 26954196232026743, 26954196387365910, 25637734202611020,
    28495243004731970, 26637734216428140
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    30751368023739724, 32598150255566273, 29751368505030566, 35416533488216936, 35416533832182237, 6794415866926375,
    35416533488216936, 35416533832182237, 11034111146096593, 6794415866926375, 34934059230861994, 34934059574827343,
    10329796338220703, 11034111146096593, 20592501748504646, 30665335745233840, 30665336089199142, 6794415866926375,
    6794415866926375, 6942514514520450, 1584962500724866, 2807354922807594, 3169925001442313, 4087462841250340,
    2807354922807594, 4954196321574415
  ]

abbrev PositiveTerm := Fin 38
abbrev NegativeTerm := Fin 26
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
noncomputable def positiveFloor : ℝ := 1182888271 / 500000000000
noncomputable def negativeCeiling : ℝ := 14380297 / 25000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 33342941102143313407842975744, coefficient := (-33342941102143313407842975744) }, { argument := 119933567594597773178497400832, coefficient := (-119933567594597773178497400832) }, { argument := 33342952225529989854702600192, coefficient := (-33342952225529989854702600192) }, { argument := 52873573343643555899316895744, coefficient := (-52873573343643555899316895744) }, { argument := 52873585949687287270581731328, coefficient := (-52873585949687287270581731328) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 52873573343643555899316895744, coefficient := (-52873573343643555899316895744) }, { argument := 52873585949687287270581731328, coefficient := (-52873585949687287270581731328) }, { argument := 81123758199420076139483234304, coefficient := (-81123758199420076139483234304) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 37844209345834504158409916416, coefficient := (-37844209345834504158409916416) }, { argument := 37844218368598199211594350592, coefficient := (-37844218368598199211594350592) }, { argument := 24894200477504443965549576192, coefficient := (-24894200477504443965549576192) }, { argument := 81123758199420076139483234304, coefficient := (-81123758199420076139483234304) }, { argument := 14933114515795220791201628160, coefficient := (-14933114515795220791201628160) }, { argument := 1963295297011092344532893696, coefficient := (-1963295297011092344532893696) }, { argument := 1963295765097223214912765952, coefficient := (-1963295765097223214912765952) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 2379166013001590215821754368, coefficient := (-2379166013001590215821754368) }, { argument := 6338253001141147007483516026880, coefficient := 6338253001141147007483516026880 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4758332026003180431643508736, coefficient := 4758332026003180431643508736 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 49788400955008887931099152384, coefficient := 49788400955008887931099152384 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 162247516398840152278966468608, coefficient := 162247516398840152278966468608 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 49788400955008887931099152384, coefficient := 49788400955008887931099152384 }, { argument := 162247516398840152278966468608, coefficient := 162247516398840152278966468608 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4758332026003180431643508736, coefficient := 4758332026003180431643508736 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 7582382740622954183757135872, coefficient := 7582382740622954183757135872 }, { argument := 151647654812459083675142717440, coefficient := 151647654812459083675142717440 }, { argument := 7853182124216631118891319296, coefficient := 7853182124216631118891319296 }, { argument := 141086478852305683204909563904, coefficient := 141086478852305683204909563904 }, { argument := 211223519203068009404663070720, coefficient := 211223519203068009404663070720 }, { argument := 7582382740622954183757135872, coefficient := 7582382740622954183757135872 }, { argument := 211494318586661686339797254144, coefficient := 211494318586661686339797254144 }, { argument := 211494318586661686339797254144, coefficient := 211494318586661686339797254144 }, { argument := 151376855428865406740008534016, coefficient := 151376855428865406740008534016 }, { argument := 7853182124216631118891319296, coefficient := 7853182124216631118891319296 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 339814540783836885459809599488, coefficient := 339814540783836885459809599488 }, { argument := 373238921844542152882085953536, coefficient := 373238921844542152882085953536 }, { argument := 339814540783836885459809599488, coefficient := 339814540783836885459809599488 }, { argument := 373238921844542152882085953536, coefficient := 373238921844542152882085953536 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 1346878762742493739090247155712, coefficient := 1346878762742493739090247155712 }, { argument := 1346878762742493739090247155712, coefficient := (-1346878762742493739090247155712) }, { argument := 1109194275199700726309615304704, coefficient := 1109194275199700726309615304704 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 1228036452857966472524898238464, coefficient := 1228036452857966472524898238464 }, { argument := 1228036585084227992874964221952, coefficient := 1228036585084227992874964221952 }, { argument := 2456073037942194465399862460416, coefficient := (-2456073037942194465399862460416) }, { argument := 493079218882627227309735673856, coefficient := 493079218882627227309735673856 }, { argument := 1786827245511630878284921700352, coefficient := 1786827245511630878284921700352 }, { argument := 493079223604993710179380887552, coefficient := 493079223604993710179380887552 }] }

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

namespace Parent3

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-311762819493630168430595444572160)
def positiveArguments : Array ℕ := #[
    2615333, 102242271, 102242259, 2615337
  ]
def positiveCoefficients : Array ℕ := #[
    24701121801485835651342401536, 965650947405750247225118687232, 965650834068954658353633558528, 24701159580417698608504111104
  ]
def positiveScales : Array ℕ := #[
    21, 26, 26, 21
  ]
def negativeArguments : Array ℕ := #[
    35, 25
  ]
def negativeCoefficients : Array ℕ := #[
    2772985687999251815774038261760, 1980704062856608439838598758400
  ]
def negativeScales : Array ℕ := #[
    5, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    21318563220141511, 26607416545919040, 26607416376592387, 21318565426658138
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    5129283016944967, 4643856189792934
  ]

abbrev PositiveTerm := Fin 4
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 315612591 / 500000000000
noncomputable def negativeCeiling : ℝ := 70481613 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2772985687999251815774038261760, coefficient := (-2772985687999251815774038261760) }, { argument := 24701121801485835651342401536, coefficient := 24701121801485835651342401536 }, { argument := 965650947405750247225118687232, coefficient := 965650947405750247225118687232 }, { argument := 965650834068954658353633558528, coefficient := 965650834068954658353633558528 }, { argument := 24701159580417698608504111104, coefficient := 24701159580417698608504111104 }, { argument := 1980704062856608439838598758400, coefficient := (-1980704062856608439838598758400) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk23
