import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 9, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9

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
def constantNumerator : ℤ := (-1103659649601816464986021459656704)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    12582915, 3963918015, 3827014977, 3963918015, 3827014977, 8254574688331,
    478184275, 44165262972853, 989535325, 83399207, 1977071503, 219173247,
    8261595445323, 478184275, 82542181, 245680680913, 12501775118383, 21836185,
    192196459, 3669381975, 142219203, 6250887534427, 3669381975, 21836185,
    171451203, 165000003, 171451203, 142219203, 165000003, 122840365221,
    192196459, 12582909, 6966438209, 6717465279, 6966438209, 6717465279,
    309356199544757, 17403444397, 1651446933121099, 36099122083, 3037162969, 72125794417,
    7982657153, 309615466760117, 17403444397, 3005514139, 30759982975583, 1899243660219809,
    1792470155, 16629749633, 219889686597, 13509136137, 949621837019081, 219889686597,
    1792470155, 14000233737, 13891853577, 14000233737, 13509136137, 13891853577,
    15379984578615, 16629749633, 200655, 51597
  ]
def negativeCoefficients : Array ℕ := #[
    118842272105595403608187207680, 73121381151871779528234762240, 70595965846972445982386552832, 73121381151871779528234762240, 70595965846972445982386552832, 9293824872617354939066220544,
    17641885881994697000144076800, 99451330933630367598110572544, 18253704892170005113942835200, 769221913739663076549984256, 18235266015632642999450599424, 16172131180851719050371268608,
    9301729542260612440157847552, 17641885881994697000144076800, 761317244096405575458357248, 553223711505958264503271424, 28151494882309708658700713984, 201403258120587702677012480,
    221587430690388175942057984, 4230509387594243755317657600, 5246962480215891368629764096, 28151494770780315686684065792, 4230509387594243755317657600, 201403258120587702677012480,
    197669778929413956072112128, 190232051718894264860540928, 197669778929413956072112128, 5246962480215891368629764096, 190232051718894264860540928, 553223823035351236519919616,
    221587430690388175942057984, 118842215437197609172444643328, 257016205493469065491920191488, 247830725651485859422276681728, 257016205493469065491920191488, 247830725651485859422276681728,
    348304116248630107378043322368, 642073769584986902153714991104, 3718727896313164942581853847552, 665911266350697854469173936128, 28012883999645428314854653952, 665243035361694107212433063936,
    589016134118231645807540436992, 348596025182251277912278827008, 642073769584986902153714991104, 27720975066024257780619149312, 69265323933379199780031299584, 4276716520225854364774020677632,
    16532619104523745705056010240, 19172795968113521308423159808, 253515548318941273252977180672, 498399153952280590755544694784, 4276716551342019075611008434176, 253515548318941273252977180672,
    16532619104523745705056010240, 16141170544909579954591629312, 16016216727772849142237233152, 16141170544909579954591629312, 498399153952280590755544694784, 16016216727772849142237233152,
    69265292817214488943043543040, 19172795968113521308423159808, 1895132893240417320708341760, 1949279547333000672728580096
  ]
def negativeScales : Array ℕ := #[
    23, 31, 31, 31, 31, 42,
    28, 45, 29, 26, 30, 27,
    42, 28, 26, 37, 43, 24,
    27, 31, 27, 42, 31, 24,
    27, 27, 27, 27, 27, 36,
    27, 23, 32, 32, 32, 32,
    48, 34, 50, 35, 31, 36,
    32, 48, 34, 31, 44, 50,
    30, 33, 37, 33, 49, 37,
    30, 33, 33, 33, 33, 33,
    43, 33, 17, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    23584962844690126, 31884279981104318, 31833572402243709, 31884279981104318, 31833572402243709, 42908331026832070,
    28832991448420702, 45327977335280730, 29882175972608400, 26313530330104419, 30880717905753408, 27707496468177326,
    42909557559707903, 28832991448420702, 26298628223180592, 37837993461049971, 43507198190236654, 24380217489226421,
    27518006515449349, 31772889948298596, 27083541035606363, 42507198184521047, 31772889948298596, 24380217489226421,
    27353222786184027, 27297890809800809, 27353222786184027, 27083541035606363, 27297890809800809, 36837993751895947,
    27518006515449349, 23584962156759523, 32697774079501420, 32645269813311099, 32697774079501420, 32645269813311099,
    48136262274489884, 34018653813723379, 50552652034743928, 35071244700614788, 31500077177131380, 36069796253032500,
    32894221908050854, 48137470871161113, 34018653813723379, 31484964661008925, 44806119939093331, 50754346429013737,
    30739301952119320, 33953047408331085, 37677988983402296, 33653216371101918, 49754346439510373, 37677988983402296,
    30739301952119320, 33704731862438734, 33693520058545421, 33704731862438734, 33653216371101918, 33693520058545421,
    43806119290989132, 33953047408331085, 17614357580651952, 15654999565165109
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
noncomputable def negativeCeiling : ℝ := 10660240027 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 118842272105595403608187207680, coefficient := (-118842272105595403608187207680) }, { argument := 73121381151871779528234762240, coefficient := (-73121381151871779528234762240) }, { argument := 70595965846972445982386552832, coefficient := (-70595965846972445982386552832) }, { argument := 73121381151871779528234762240, coefficient := (-73121381151871779528234762240) }, { argument := 70595965846972445982386552832, coefficient := (-70595965846972445982386552832) }, { argument := 9293824872617354939066220544, coefficient := (-9293824872617354939066220544) }, { argument := 17641885881994697000144076800, coefficient := (-17641885881994697000144076800) }, { argument := 99451330933630367598110572544, coefficient := (-99451330933630367598110572544) }, { argument := 18253704892170005113942835200, coefficient := (-18253704892170005113942835200) }, { argument := 769221913739663076549984256, coefficient := (-769221913739663076549984256) }, { argument := 18235266015632642999450599424, coefficient := (-18235266015632642999450599424) }, { argument := 16172131180851719050371268608, coefficient := (-16172131180851719050371268608) }, { argument := 9301729542260612440157847552, coefficient := (-9301729542260612440157847552) }, { argument := 17641885881994697000144076800, coefficient := (-17641885881994697000144076800) }, { argument := 761317244096405575458357248, coefficient := (-761317244096405575458357248) }, { argument := 553223711505958264503271424, coefficient := (-553223711505958264503271424) }, { argument := 28151494882309708658700713984, coefficient := (-28151494882309708658700713984) }, { argument := 201403258120587702677012480, coefficient := (-201403258120587702677012480) }, { argument := 221587430690388175942057984, coefficient := (-221587430690388175942057984) }, { argument := 4230509387594243755317657600, coefficient := (-4230509387594243755317657600) }, { argument := 5246962480215891368629764096, coefficient := (-5246962480215891368629764096) }, { argument := 28151494770780315686684065792, coefficient := (-28151494770780315686684065792) }, { argument := 4230509387594243755317657600, coefficient := (-4230509387594243755317657600) }, { argument := 201403258120587702677012480, coefficient := (-201403258120587702677012480) }, { argument := 197669778929413956072112128, coefficient := (-197669778929413956072112128) }, { argument := 190232051718894264860540928, coefficient := (-190232051718894264860540928) }, { argument := 197669778929413956072112128, coefficient := (-197669778929413956072112128) }, { argument := 5246962480215891368629764096, coefficient := (-5246962480215891368629764096) }, { argument := 190232051718894264860540928, coefficient := (-190232051718894264860540928) }, { argument := 553223823035351236519919616, coefficient := (-553223823035351236519919616) }, { argument := 221587430690388175942057984, coefficient := (-221587430690388175942057984) }, { argument := 118842215437197609172444643328, coefficient := (-118842215437197609172444643328) }, { argument := 257016205493469065491920191488, coefficient := (-257016205493469065491920191488) }, { argument := 247830725651485859422276681728, coefficient := (-247830725651485859422276681728) }, { argument := 257016205493469065491920191488, coefficient := (-257016205493469065491920191488) }, { argument := 247830725651485859422276681728, coefficient := (-247830725651485859422276681728) }, { argument := 348304116248630107378043322368, coefficient := (-348304116248630107378043322368) }, { argument := 642073769584986902153714991104, coefficient := (-642073769584986902153714991104) }, { argument := 3718727896313164942581853847552, coefficient := (-3718727896313164942581853847552) }, { argument := 665911266350697854469173936128, coefficient := (-665911266350697854469173936128) }, { argument := 28012883999645428314854653952, coefficient := (-28012883999645428314854653952) }, { argument := 665243035361694107212433063936, coefficient := (-665243035361694107212433063936) }, { argument := 589016134118231645807540436992, coefficient := (-589016134118231645807540436992) }, { argument := 348596025182251277912278827008, coefficient := (-348596025182251277912278827008) }, { argument := 642073769584986902153714991104, coefficient := (-642073769584986902153714991104) }, { argument := 27720975066024257780619149312, coefficient := (-27720975066024257780619149312) }, { argument := 69265323933379199780031299584, coefficient := (-69265323933379199780031299584) }, { argument := 4276716520225854364774020677632, coefficient := (-4276716520225854364774020677632) }, { argument := 16532619104523745705056010240, coefficient := (-16532619104523745705056010240) }, { argument := 19172795968113521308423159808, coefficient := (-19172795968113521308423159808) }, { argument := 253515548318941273252977180672, coefficient := (-253515548318941273252977180672) }, { argument := 498399153952280590755544694784, coefficient := (-498399153952280590755544694784) }, { argument := 4276716551342019075611008434176, coefficient := (-4276716551342019075611008434176) }, { argument := 253515548318941273252977180672, coefficient := (-253515548318941273252977180672) }, { argument := 16532619104523745705056010240, coefficient := (-16532619104523745705056010240) }, { argument := 16141170544909579954591629312, coefficient := (-16141170544909579954591629312) }, { argument := 16016216727772849142237233152, coefficient := (-16016216727772849142237233152) }, { argument := 16141170544909579954591629312, coefficient := (-16141170544909579954591629312) }, { argument := 498399153952280590755544694784, coefficient := (-498399153952280590755544694784) }, { argument := 16016216727772849142237233152, coefficient := (-16016216727772849142237233152) }, { argument := 69265292817214488943043543040, coefficient := (-69265292817214488943043543040) }, { argument := 19172795968113521308423159808, coefficient := (-19172795968113521308423159808) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1949279547333000672728580096, coefficient := (-1949279547333000672728580096) }] }

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
def constantNumerator : ℤ := (-5956444579581975832500334445461504)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    200655, 177723, 8318583, 2264535, 51597, 8318583,
    200655, 200655, 85995, 200655, 2264535, 85995,
    200655, 177723, 121671870555, 30542109867655, 98735, 1251719514104875,
    3255, 7595, 98735, 98735, 3255, 1218455,
    48825, 30542115696775, 98735, 7595, 48825, 7595,
    98735, 98735, 991551413445, 3963918015, 3827014977, 3963918015,
    3827014977, 618669378430851, 69613793461, 3302685533160573, 288793020233, 24297308805,
    577006442261, 127722540493, 619187912734595, 69613793461, 24044118227, 1260928924276505,
    77787807102675175, 18305609385, 172057051803, 2033417320263, 142750029555, 38893903588537383,
    2033417320263, 18305609385, 142785107955, 142777366515, 142785107955, 142750029555,
    142777366515, 630464424938457, 172057051803, 6615
  ]
def negativeCoefficients : Array ℕ := #[
    1895132893240417320708341760, 1678546276870083912627388416, 78566795088338443781365825536, 21387928366570424047994142720, 1949279547333000672728580096, 78566795088338443781365825536,
    1895132893240417320708341760, 1895132893240417320708341760, 1624399622777500560607150080, 1895132893240417320708341760, 21387928366570424047994142720, 1624399622777500560607150080,
    1895132893240417320708341760, 1678546276870083912627388416, 547961390892969224338145280, 68774717309539903451105853440, 1865051418744537680697098240, 704655442161886670247428096000,
    983763385711404490917150720, 71732746874789910796042240, 1865051418744537680697098240, 1865051418744537680697098240, 983763385711404490917150720, 23015964211539734235415838720,
    1844556348208883420469657600, 68774730435551233400058675200, 1865051418744537680697098240, 71732746874789910796042240, 1844556348208883420469657600, 71732746874789910796042240,
    1865051418744537680697098240, 1865051418744537680697098240, 558193822013698827186339840, 73121381151871779528234762240, 70595965846972445982386552832, 73121381151871779528234762240,
    70595965846972445982386552832, 348279897770839617365461696512, 642073915987571243149571391488, 3718493334115971118300032663552, 665911366813971922900605730816, 28012889825357791093252423680,
    665243135579395895162606452736, 589016254229593995748858396672, 348571806632979654614072688640, 642073915987571243149571391488, 27720980963217753844641431552, 709839879189043535699047874560,
    43790642385196992526559058329600, 168839445719195349912995758080, 198368275042932973298125897728, 2344370556371240787299625074688, 5266546523431119183339596021760, 43790642427080238814573721812992,
    2344370556371240787299625074688, 168839445719195349912995758080, 164620021498929675300325294080, 164611096226277051670871408640, 164620021498929675300325294080, 5266546523431119183339596021760,
    164611096226277051670871408640, 709839837305797247684384391168, 198368275042932973298125897728, 999630537093846498835169280
  ]
def negativeScales : Array ℕ := #[
    17, 17, 22, 21, 15, 22,
    17, 17, 16, 17, 21, 16,
    17, 17, 36, 44, 16, 50,
    11, 12, 16, 16, 11, 20,
    15, 44, 16, 12, 15, 12,
    16, 16, 39, 31, 31, 31,
    31, 49, 36, 51, 38, 34,
    39, 36, 49, 36, 34, 50,
    56, 34, 37, 40, 37, 55,
    40, 34, 37, 37, 37, 37,
    37, 49, 37, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    17614357580651952, 17439270874085520, 22987906387263822, 21110783406763079, 15654999565165109, 22987906387263822,
    17614357580651952, 17614357580651952, 16391965159307136, 17614357580651952, 21110783406763079, 16391965159307136,
    17614357580651952, 17439270874085520, 36824204713260471, 44795864961963657, 16591273967534972, 50152832742015265,
    11668441828086828, 12890834253091783, 16591273967534972, 16591273967534972, 11668441828086828, 20216621539732443,
    15575332423664331, 44795865237309461, 16591273967534972, 12890834253091783, 15575332423664331, 12890834253091783,
    16591273967534972, 16591273967534972, 39850896625843064, 31884279981104318, 31833572402243709, 31884279981104318,
    31833572402243709, 49136161956718827, 36018654142679752, 51552561032551493, 38071244918268196, 34500077477162089,
    39069796470371973, 36894222202243239, 49137370637101676, 36018654142679752, 34484964967919157, 50163408379798336,
    56110393555015181, 34091566749944871, 37324096066278954, 40887043473414928, 37054700088045059, 55110393556395036,
    40887043473414928, 34091566749944871, 37055054562344917, 37054976341023150, 37055054562344917, 37054700088045059,
    37054976341023150, 49163408294673852, 37324096066278954, 12691525441225267
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
noncomputable def negativeCeiling : ℝ := 71947043603 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1678546276870083912627388416, coefficient := (-1678546276870083912627388416) }, { argument := 78566795088338443781365825536, coefficient := (-78566795088338443781365825536) }, { argument := 21387928366570424047994142720, coefficient := (-21387928366570424047994142720) }, { argument := 1949279547333000672728580096, coefficient := (-1949279547333000672728580096) }, { argument := 78566795088338443781365825536, coefficient := (-78566795088338443781365825536) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1624399622777500560607150080, coefficient := (-1624399622777500560607150080) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 21387928366570424047994142720, coefficient := (-21387928366570424047994142720) }, { argument := 1624399622777500560607150080, coefficient := (-1624399622777500560607150080) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1678546276870083912627388416, coefficient := (-1678546276870083912627388416) }, { argument := 547961390892969224338145280, coefficient := (-547961390892969224338145280) }, { argument := 68774717309539903451105853440, coefficient := (-68774717309539903451105853440) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 704655442161886670247428096000, coefficient := (-704655442161886670247428096000) }, { argument := 983763385711404490917150720, coefficient := (-983763385711404490917150720) }, { argument := 71732746874789910796042240, coefficient := (-71732746874789910796042240) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 983763385711404490917150720, coefficient := (-983763385711404490917150720) }, { argument := 23015964211539734235415838720, coefficient := (-23015964211539734235415838720) }, { argument := 1844556348208883420469657600, coefficient := (-1844556348208883420469657600) }, { argument := 68774730435551233400058675200, coefficient := (-68774730435551233400058675200) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 71732746874789910796042240, coefficient := (-71732746874789910796042240) }, { argument := 1844556348208883420469657600, coefficient := (-1844556348208883420469657600) }, { argument := 71732746874789910796042240, coefficient := (-71732746874789910796042240) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 558193822013698827186339840, coefficient := (-558193822013698827186339840) }, { argument := 73121381151871779528234762240, coefficient := (-73121381151871779528234762240) }, { argument := 70595965846972445982386552832, coefficient := (-70595965846972445982386552832) }, { argument := 73121381151871779528234762240, coefficient := (-73121381151871779528234762240) }, { argument := 70595965846972445982386552832, coefficient := (-70595965846972445982386552832) }, { argument := 348279897770839617365461696512, coefficient := (-348279897770839617365461696512) }, { argument := 642073915987571243149571391488, coefficient := (-642073915987571243149571391488) }, { argument := 3718493334115971118300032663552, coefficient := (-3718493334115971118300032663552) }, { argument := 665911366813971922900605730816, coefficient := (-665911366813971922900605730816) }, { argument := 28012889825357791093252423680, coefficient := (-28012889825357791093252423680) }, { argument := 665243135579395895162606452736, coefficient := (-665243135579395895162606452736) }, { argument := 589016254229593995748858396672, coefficient := (-589016254229593995748858396672) }, { argument := 348571806632979654614072688640, coefficient := (-348571806632979654614072688640) }, { argument := 642073915987571243149571391488, coefficient := (-642073915987571243149571391488) }, { argument := 27720980963217753844641431552, coefficient := (-27720980963217753844641431552) }, { argument := 709839879189043535699047874560, coefficient := (-709839879189043535699047874560) }, { argument := 43790642385196992526559058329600, coefficient := (-43790642385196992526559058329600) }, { argument := 168839445719195349912995758080, coefficient := (-168839445719195349912995758080) }, { argument := 198368275042932973298125897728, coefficient := (-198368275042932973298125897728) }, { argument := 2344370556371240787299625074688, coefficient := (-2344370556371240787299625074688) }, { argument := 5266546523431119183339596021760, coefficient := (-5266546523431119183339596021760) }, { argument := 43790642427080238814573721812992, coefficient := (-43790642427080238814573721812992) }, { argument := 2344370556371240787299625074688, coefficient := (-2344370556371240787299625074688) }, { argument := 168839445719195349912995758080, coefficient := (-168839445719195349912995758080) }, { argument := 164620021498929675300325294080, coefficient := (-164620021498929675300325294080) }, { argument := 164611096226277051670871408640, coefficient := (-164611096226277051670871408640) }, { argument := 164620021498929675300325294080, coefficient := (-164620021498929675300325294080) }, { argument := 5266546523431119183339596021760, coefficient := (-5266546523431119183339596021760) }, { argument := 164611096226277051670871408640, coefficient := (-164611096226277051670871408640) }, { argument := 709839837305797247684384391168, coefficient := (-709839837305797247684384391168) }, { argument := 198368275042932973298125897728, coefficient := (-198368275042932973298125897728) }, { argument := 999630537093846498835169280, coefficient := (-999630537093846498835169280) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9
