import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 16, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16

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
def constantNumerator : ℤ := (-115430391925765329402810727818854400)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2398649, 179, 5565743459, 947, 147, 173927225,
    75, 75, 3471, 141, 947, 3471,
    153585981, 147, 141, 179, 17141478791535337, 95,
    31, 117562464305060805, 313, 34282957444656745, 627, 281,
    95, 31, 273442490300799789, 273442337347036371, 95, 95,
    616753137, 31, 31, 179, 17141469935871255, 95,
    31, 117562402126259259, 313, 34282939733332375, 627, 281,
    95, 31, 937638486930820183, 937637949179229097, 11180469071, 313,
    313, 947, 147, 68360622306760223, 68360584068327905, 22360650997,
    75, 627, 627, 75, 281, 281,
    3471, 141, 95, 95
  ]
def negativeCoefficients : Array ℕ := #[
    2899788708292810655279794356224, 3462363547376297956358488064, 105133921452130253591116676857856, 73270576075203445020591915008, 2843393527733607818908925952, 105132556518211510880342691020800,
    2901421967075110019294822400, 2901421967075110019294822400, 67138904318118045846482190336, 2727336649050603418137133056, 73270576075203445020591915008, 67138904318118045846482190336,
    2901157155652216621069819183104, 2843393527733607818908925952, 2727336649050603418137133056, 3462363547376297956358488064, 77198357498137803796867975217152, 7350268983256945382213550080,
    299813603264428035327131648, 264727135218514539192743771504640, 6054300504630062906928529408, 77198357186457344263224830197760, 6063971911186979940326178816, 5435330484987372769478967296,
    7350268983256945382213550080, 299813603264428035327131648, 76967218589121399776785238851584, 76967175536464403888047575269376, 7350268983256945382213550080, 7350268983256945382213550080,
    2912534342373510447624043364352, 299813603264428035327131648, 299813603264428035327131648, 3462363547376297956358488064, 77198317615772343983382441492480, 7350268983256945382213550080,
    299813603264428035327131648, 264726995204300802737933471711232, 6054300504630062906928529408, 77198317304100427778232418304000, 6063971911186979940326178816, 5435330484987372769478967296,
    7350268983256945382213550080, 299813603264428035327131648, 263921771271867341238549555970048, 263921619908250764188490905157632, 105596544807302239272942627192832, 6054300504630062906928529408,
    6054300504630062906928529408, 73270576075203445020591915008, 2843393527733607818908925952, 76967218286885139250850564145152, 76967175234237754606667662622720, 105595188803378515668667740454912,
    2901421967075110019294822400, 6063971911186979940326178816, 6063971911186979940326178816, 2901421967075110019294822400, 5435330484987372769478967296, 5435330484987372769478967296,
    67138904318118045846482190336, 2727336649050603418137133056, 7350268983256945382213550080, 7350268983256945382213550080
  ]
def negativeScales : Array ℕ := #[
    21, 7, 32, 9, 7, 27,
    6, 6, 11, 7, 9, 11,
    27, 7, 7, 7, 53, 6,
    4, 56, 8, 54, 9, 8,
    6, 4, 57, 57, 6, 6,
    29, 4, 4, 7, 53, 6,
    4, 56, 8, 54, 9, 8,
    6, 4, 59, 59, 33, 8,
    8, 9, 7, 55, 55, 34,
    6, 9, 9, 6, 8, 8,
    11, 7, 6, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    21193790629411598, 7483815777264413, 32373927266256561, 9887220618935413, 7199672344836365, 27373908535896736,
    6228818690495881, 6228818690495881, 11761135650114939, 7139551352398794, 9887220618935413, 11761135650114939,
    27194471295048568, 7199672344836365, 7139551352398794, 7483815777264413, 53928341101192192, 6569855608333349,
    4954196321574415, 56706205118878681, 8290018846932619, 54928341095367458, 9292321632802040, 8134426320220927,
    6569855608333349, 4954196321574415, 57924015060888306, 57924014253896960, 6569855608333349, 6569855608333349,
    29200117907642674, 4954196321574415, 4954196321574415, 7483815777264413, 53928340355863991, 6569855608333349,
    4954196321574415, 56706204355836897, 8290018846932619, 54928340350039413, 9292321632802040, 8134426320220927,
    6569855608333349, 4954196321574415, 59701809401953128, 59701808574542790, 33380261665874897, 8290018846932619,
    8290018846932619, 9887220618935413, 7199672344836365, 55924015055223105, 55924014248231936, 34380243139580304,
    6228818690495881, 9292321632802040, 9292321632802040, 6228818690495881, 8134426320220927, 8134426320220927,
    11761135650114939, 7139551352398794, 6569855608333349, 6569855608333349
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
noncomputable def negativeCeiling : ℝ := 1318500086869 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2899788708292810655279794356224, coefficient := (-2899788708292810655279794356224) }, { argument := 3462363547376297956358488064, coefficient := (-3462363547376297956358488064) }, { argument := 105133921452130253591116676857856, coefficient := (-105133921452130253591116676857856) }, { argument := 73270576075203445020591915008, coefficient := (-73270576075203445020591915008) }, { argument := 2843393527733607818908925952, coefficient := (-2843393527733607818908925952) }, { argument := 105132556518211510880342691020800, coefficient := (-105132556518211510880342691020800) }, { argument := 2901421967075110019294822400, coefficient := (-2901421967075110019294822400) }, { argument := 2901421967075110019294822400, coefficient := (-2901421967075110019294822400) }, { argument := 67138904318118045846482190336, coefficient := (-67138904318118045846482190336) }, { argument := 2727336649050603418137133056, coefficient := (-2727336649050603418137133056) }, { argument := 73270576075203445020591915008, coefficient := (-73270576075203445020591915008) }, { argument := 67138904318118045846482190336, coefficient := (-67138904318118045846482190336) }, { argument := 2901157155652216621069819183104, coefficient := (-2901157155652216621069819183104) }, { argument := 2843393527733607818908925952, coefficient := (-2843393527733607818908925952) }, { argument := 2727336649050603418137133056, coefficient := (-2727336649050603418137133056) }, { argument := 3462363547376297956358488064, coefficient := (-3462363547376297956358488064) }, { argument := 77198357498137803796867975217152, coefficient := (-77198357498137803796867975217152) }, { argument := 7350268983256945382213550080, coefficient := (-7350268983256945382213550080) }, { argument := 299813603264428035327131648, coefficient := (-299813603264428035327131648) }, { argument := 264727135218514539192743771504640, coefficient := (-264727135218514539192743771504640) }, { argument := 6054300504630062906928529408, coefficient := (-6054300504630062906928529408) }, { argument := 77198357186457344263224830197760, coefficient := (-77198357186457344263224830197760) }, { argument := 6063971911186979940326178816, coefficient := (-6063971911186979940326178816) }, { argument := 5435330484987372769478967296, coefficient := (-5435330484987372769478967296) }, { argument := 7350268983256945382213550080, coefficient := (-7350268983256945382213550080) }, { argument := 299813603264428035327131648, coefficient := (-299813603264428035327131648) }, { argument := 76967218589121399776785238851584, coefficient := (-76967218589121399776785238851584) }, { argument := 76967175536464403888047575269376, coefficient := (-76967175536464403888047575269376) }, { argument := 7350268983256945382213550080, coefficient := (-7350268983256945382213550080) }, { argument := 7350268983256945382213550080, coefficient := (-7350268983256945382213550080) }, { argument := 2912534342373510447624043364352, coefficient := (-2912534342373510447624043364352) }, { argument := 299813603264428035327131648, coefficient := (-299813603264428035327131648) }, { argument := 299813603264428035327131648, coefficient := (-299813603264428035327131648) }, { argument := 3462363547376297956358488064, coefficient := (-3462363547376297956358488064) }, { argument := 77198317615772343983382441492480, coefficient := (-77198317615772343983382441492480) }, { argument := 7350268983256945382213550080, coefficient := (-7350268983256945382213550080) }, { argument := 299813603264428035327131648, coefficient := (-299813603264428035327131648) }, { argument := 264726995204300802737933471711232, coefficient := (-264726995204300802737933471711232) }, { argument := 6054300504630062906928529408, coefficient := (-6054300504630062906928529408) }, { argument := 77198317304100427778232418304000, coefficient := (-77198317304100427778232418304000) }, { argument := 6063971911186979940326178816, coefficient := (-6063971911186979940326178816) }, { argument := 5435330484987372769478967296, coefficient := (-5435330484987372769478967296) }, { argument := 7350268983256945382213550080, coefficient := (-7350268983256945382213550080) }, { argument := 299813603264428035327131648, coefficient := (-299813603264428035327131648) }, { argument := 263921771271867341238549555970048, coefficient := (-263921771271867341238549555970048) }, { argument := 263921619908250764188490905157632, coefficient := (-263921619908250764188490905157632) }, { argument := 105596544807302239272942627192832, coefficient := (-105596544807302239272942627192832) }, { argument := 6054300504630062906928529408, coefficient := (-6054300504630062906928529408) }, { argument := 6054300504630062906928529408, coefficient := (-6054300504630062906928529408) }, { argument := 73270576075203445020591915008, coefficient := (-73270576075203445020591915008) }, { argument := 2843393527733607818908925952, coefficient := (-2843393527733607818908925952) }, { argument := 76967218286885139250850564145152, coefficient := (-76967218286885139250850564145152) }, { argument := 76967175234237754606667662622720, coefficient := (-76967175234237754606667662622720) }, { argument := 105595188803378515668667740454912, coefficient := (-105595188803378515668667740454912) }, { argument := 2901421967075110019294822400, coefficient := (-2901421967075110019294822400) }, { argument := 6063971911186979940326178816, coefficient := (-6063971911186979940326178816) }, { argument := 6063971911186979940326178816, coefficient := (-6063971911186979940326178816) }, { argument := 2901421967075110019294822400, coefficient := (-2901421967075110019294822400) }, { argument := 5435330484987372769478967296, coefficient := (-5435330484987372769478967296) }, { argument := 5435330484987372769478967296, coefficient := (-5435330484987372769478967296) }, { argument := 67138904318118045846482190336, coefficient := (-67138904318118045846482190336) }, { argument := 2727336649050603418137133056, coefficient := (-2727336649050603418137133056) }, { argument := 7350268983256945382213550080, coefficient := (-7350268983256945382213550080) }, { argument := 7350268983256945382213550080, coefficient := (-7350268983256945382213550080) }] }

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
def constantNumerator : ℤ := 111354936375199112441201636986060800
def positiveArguments : Array ℕ := #[
    6651, 1, 19, 29, 299, 9,
    29, 9, 9, 771, 9, 299,
    771, 1, 9, 9, 19, 2737,
    177251335453, 177251238627, 65291643577, 95, 31, 111945729481,
    313, 65291643317, 627, 281, 95, 31,
    1230545137, 141, 22311837205, 3489, 111, 44623098229,
    57, 57, 1929, 105, 3489, 1929,
    76945175, 111, 105, 141
  ]
def positiveCoefficients : Array ℕ := #[
    2107786035529488437338643254738944, 1237940039285380274899124224, 1470053796651389076442710016, 1121883160602375874127331328, 11567002242072771943588691968, 1392682544196052809261514752,
    1121883160602375874127331328, 1392682544196052809261514752, 1392682544196052809261514752, 59653235643064261996701548544, 1392682544196052809261514752, 11567002242072771943588691968,
    59653235643064261996701548544, 1237940039285380274899124224, 1392682544196052809261514752, 1392682544196052809261514752, 1470053796651389076442710016, 433694961603082983987059584139264,
    837045765587131261843925565964288, 837045308339274191507658104635392, 308331069239495951445083230830592, 29401075933027781528854200320, 1199254413057712141308526592, 1057297521602933447357717704343552,
    24217202018520251627714117632, 308331068011680665898975475269632, 24255887644747919761304715264, 21741321939949491077915869184, 29401075933027781528854200320, 1199254413057712141308526592,
    5811085110627035722628938596352, 5454673298101206836274266112, 210729344376271890488185176719360, 134974149908334118097595138048, 4294104511271162828556337152, 210726623438429424173136304144384,
    4410161389954167229328130048, 4410161389954167229328130048, 74624572993171829696262832128, 4061990753905154027012751360, 134974149908334118097595138048, 74624572993171829696262832128,
    5813813047016629650492017868800, 4294104511271162828556337152, 4061990753905154027012751360, 5454673298101206836274266112
  ]
def positiveScales : Array ℕ := #[
    12, 0, 4, 4, 8, 3,
    4, 3, 3, 9, 3, 8,
    9, 0, 3, 3, 4, 11,
    37, 37, 35, 6, 4, 36,
    8, 35, 9, 8, 6, 4,
    30, 7, 34, 11, 6, 35,
    5, 5, 10, 6, 11, 10,
    26, 6, 6, 7
  ]
def negativeArguments : Array ℕ := #[
    947, 3471, 154260255, 31, 31, 147,
    141, 179, 1, 2737, 10565, 10565,
    171
  ]
def negativeCoefficients : Array ℕ := #[
    73270576075203445020591915008, 67138904318118045846482190336, 2913893831403698409697097809920, 299813603264428035327131648, 299813603264428035327131648, 2843393527733607818908925952,
    2727336649050603418137133056, 3462363547376297956358488064, 158456325028528675187087900672, 433694961603082983987059584139264, 1674091073926405453351583670599680, 1674091073926405453351583670599680,
    433536505278054455311872496238592
  ]
def negativeScales : Array ℕ := #[
    9, 11, 27, 4, 4, 7,
    7, 7, 0, 11, 13, 13,
    7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    12699355555584036, 0, 4247927513443585, 4857980995002857, 8224001674198104, 3169925001442312,
    4857980995002857, 3169925001442312, 3169925001442312, 9590587049914763, 3169925001442312, 8224001674198104,
    9590587049914763, 0, 3169925001442312, 3169925001442312, 4247927513443585, 11418379719364955,
    37367005540868442, 37367004752776054, 35926179307116450, 6569855608330797, 4954196309696329, 36704008536894319,
    8290018846932618, 35926179301371446, 9292321632802038, 8134426320220925, 6569855608330797, 4954196309696329,
    30196650431515571, 7139551352398793, 34377090261981205, 11768597882173550, 6794415866314396, 35377071633778822,
    5832890014087662, 5832890014087662, 10913637427705176, 6714245517659862, 11768597882173550, 10913637427705176,
    26197327526543845, 6794415866314396, 6714245517659862, 7139551352398793
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    9887220618935413, 11761135650114939, 27200791159954070, 4954196321574415, 4954196321574415, 7199672344836365,
    7139551352398794, 7483815777264413, 0, 11418379719364971, 13367005146822305, 13367005146822305,
    7417852514885912
  ]

abbrev PositiveTerm := Fin 46
abbrev NegativeTerm := Fin 13
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
noncomputable def positiveFloor : ℝ := 409912828603 / 200000000000
noncomputable def negativeCeiling : ℝ := 638012619613 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 73270576075203445020591915008, coefficient := (-73270576075203445020591915008) }, { argument := 67138904318118045846482190336, coefficient := (-67138904318118045846482190336) }, { argument := 2913893831403698409697097809920, coefficient := (-2913893831403698409697097809920) }, { argument := 299813603264428035327131648, coefficient := (-299813603264428035327131648) }, { argument := 299813603264428035327131648, coefficient := (-299813603264428035327131648) }, { argument := 2843393527733607818908925952, coefficient := (-2843393527733607818908925952) }, { argument := 2727336649050603418137133056, coefficient := (-2727336649050603418137133056) }, { argument := 3462363547376297956358488064, coefficient := (-3462363547376297956358488064) }, { argument := 2107786035529488437338643254738944, coefficient := 2107786035529488437338643254738944 }, { argument := 1237940039285380274899124224, coefficient := 1237940039285380274899124224 }, { argument := 1470053796651389076442710016, coefficient := 1470053796651389076442710016 }, { argument := 1121883160602375874127331328, coefficient := 1121883160602375874127331328 }, { argument := 11567002242072771943588691968, coefficient := 11567002242072771943588691968 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 1121883160602375874127331328, coefficient := 1121883160602375874127331328 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 59653235643064261996701548544, coefficient := 59653235643064261996701548544 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 11567002242072771943588691968, coefficient := 11567002242072771943588691968 }, { argument := 59653235643064261996701548544, coefficient := 59653235643064261996701548544 }, { argument := 1237940039285380274899124224, coefficient := 1237940039285380274899124224 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 1470053796651389076442710016, coefficient := 1470053796651389076442710016 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 433694961603082983987059584139264, coefficient := 433694961603082983987059584139264 }, { argument := 433694961603082983987059584139264, coefficient := (-433694961603082983987059584139264) }, { argument := 837045765587131261843925565964288, coefficient := 837045765587131261843925565964288 }, { argument := 837045308339274191507658104635392, coefficient := 837045308339274191507658104635392 }, { argument := 1674091073926405453351583670599680, coefficient := (-1674091073926405453351583670599680) }, { argument := 308331069239495951445083230830592, coefficient := 308331069239495951445083230830592 }, { argument := 29401075933027781528854200320, coefficient := 29401075933027781528854200320 }, { argument := 1199254413057712141308526592, coefficient := 1199254413057712141308526592 }, { argument := 1057297521602933447357717704343552, coefficient := 1057297521602933447357717704343552 }, { argument := 24217202018520251627714117632, coefficient := 24217202018520251627714117632 }, { argument := 308331068011680665898975475269632, coefficient := 308331068011680665898975475269632 }, { argument := 24255887644747919761304715264, coefficient := 24255887644747919761304715264 }, { argument := 21741321939949491077915869184, coefficient := 21741321939949491077915869184 }, { argument := 29401075933027781528854200320, coefficient := 29401075933027781528854200320 }, { argument := 1199254413057712141308526592, coefficient := 1199254413057712141308526592 }, { argument := 1674091073926405453351583670599680, coefficient := (-1674091073926405453351583670599680) }, { argument := 5811085110627035722628938596352, coefficient := 5811085110627035722628938596352 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 210729344376271890488185176719360, coefficient := 210729344376271890488185176719360 }, { argument := 134974149908334118097595138048, coefficient := 134974149908334118097595138048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 210726623438429424173136304144384, coefficient := 210726623438429424173136304144384 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 134974149908334118097595138048, coefficient := 134974149908334118097595138048 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }, { argument := 5813813047016629650492017868800, coefficient := 5813813047016629650492017868800 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 433536505278054455311872496238592, coefficient := (-433536505278054455311872496238592) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16
