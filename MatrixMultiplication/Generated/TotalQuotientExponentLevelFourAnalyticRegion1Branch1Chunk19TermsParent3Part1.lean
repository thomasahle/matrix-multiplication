import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 19, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk19

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
def constantNumerator : ℤ := (-16811805575057580453017410548531200)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    17944006275, 1834036425, 132876551379, 493603275165, 8303036313, 2036800296958753,
    57082325, 2036800570672351, 57082325, 5884975469, 21861217315, 367733543,
    302853950727, 302853878521, 4652801, 869942007453911, 387363121, 61131650181778675,
    4053140949, 179509739, 3820727181577489, 179509739, 349571597, 6604068819,
    349571597, 4053140949, 6604068819, 1739889127731279, 349571597, 349571597,
    387363121, 123004096044172675, 1646145305, 1363948967, 445937571624638321, 9171380985,
    30751010620205251, 36732556663, 36732556663, 26291292157, 1363948967, 64823843173146883,
    1175369275, 64823856738098941, 1175369275, 5884975469, 21861217315, 367733543,
    95839857825, 95839834975, 61636863, 11500782939, 11500780197, 209,
    1393265, 57082325, 1175369275, 57082325, 1393265, 1836361395,
    287472077145, 71868045645, 7345551015, 11460215387
  ]
def negativeCoefficients : Array ℕ := #[
    662016982823926513449880780800, 16916000276918101267080806400, 1225569868342765499213238239232, 4552686645456794424300609208320, 1225311887205023645460766654464, 2293233264602888902001790287872,
    8423864323258500647590297600, 2293233572777003391761225089024, 8423864323258500647590297600, 108558636356701839091149307904, 403268280949552886068585431040, 108535784880631465099088887808,
    698333665096601475152665903104, 698333498600901151868680404992, 21972231493862368119929962496, 979467625150843708321210302464, 114329413706886175383749656576, 34414059622400244349037812121600,
    1196276060494004127795819577344, 105963846850284747916646023168, 34414051022473409739724672729088, 105963846850284747916646023168, 103175324564750938760944812032, 3898354155176265199670293168128,
    103175324564750938760944812032, 1196276060494004127795819577344, 3898354155176265199670293168128, 979470503414570677862607618048, 103175324564750938760944812032, 103175324564750938760944812032,
    114329413706886175383749656576, 34622575069348797513848376524800, 485856338391576837221337006080, 25160417523849514784676380672, 125520267587451563312634266648576, 676728471331124880415433687040,
    34622559992605633374446235418624, 677596071935395553339043217408, 677596071935395553339043217408, 484988737787306164297727475712, 25160417523849514784676380672, 18246289747456735830955679285248,
    86726944832106168973891993600, 18246293565651300437670857015296, 86726944832106168973891993600, 108558636356701839091149307904, 403268280949552886068585431040, 108535784880631465099088887808,
    441983332339621186805484748800, 441983226962595665739671142400, 291071855940428168895186075648, 26518999940377271208329084928, 26518993617755739944380268544, 16170591763165279840869810176,
    51402405763713876864532480, 8423864323258500647590297600, 86726944832106168973891993600, 8423864323258500647590297600, 51402405763713876864532480, 16937444340202627515191132160,
    662865479428937973559763927040, 662865722545495650005585756160, 16937687456760303961012961280, 105701830136788632799276957696
  ]
def negativeScales : Array ℕ := #[
    34, 30, 36, 38, 32, 50,
    25, 50, 25, 32, 34, 28,
    38, 38, 22, 49, 28, 55,
    31, 27, 51, 27, 28, 32,
    28, 31, 32, 50, 28, 28,
    28, 56, 30, 30, 58, 33,
    54, 35, 35, 34, 30, 55,
    30, 55, 30, 32, 34, 28,
    36, 36, 25, 33, 33, 7,
    20, 25, 30, 25, 20, 30,
    38, 36, 32, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34062782978919464, 30772375146306593, 36951295590226169, 38844561012435944, 32950991872451703, 50855225959915711,
    25766540762445095, 50855226153790996, 25766540762445095, 32454389255515829, 34347654686819237, 28454085537795791,
    38139831275217814, 38139830931252512, 22149668053764575, 49627912558882359, 28529111367446966, 55762769030091367,
    31916393206170467, 27419486876271785, 51762768669567978, 27419486876271785, 28381012728457137, 32620708008213550,
    28381012728457137, 31916393206170467, 32620708008213550, 50627916798380020, 28381012728457137, 28381012728457137,
    28529111367446966, 56771483971642736, 30616444541851014, 30345142520024764, 58629619369405833, 33094491838646802,
    54771483343406752, 35096340263039171, 35096340263039171, 34613865997748643, 30345142520024764, 55847374075250616,
    30130466944830274, 55847374377147058, 30130466944830274, 32454389255515829, 34347654686819237, 28454085537795791,
    36479906716815572, 36479906372850270, 25877290105049322, 33421013027761882, 33421012683796581, 7707359132166870,
    20410038254991501, 25766540762445095, 30130466944830274, 25766540762445095, 20410038254991501, 30774202862716993,
    38064630874180359, 36064631403311832, 32774223570713468, 33415915107701151
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
noncomputable def negativeCeiling : ℝ := 219474655379 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 662016982823926513449880780800, coefficient := (-662016982823926513449880780800) }, { argument := 16916000276918101267080806400, coefficient := (-16916000276918101267080806400) }, { argument := 1225569868342765499213238239232, coefficient := (-1225569868342765499213238239232) }, { argument := 4552686645456794424300609208320, coefficient := (-4552686645456794424300609208320) }, { argument := 1225311887205023645460766654464, coefficient := (-1225311887205023645460766654464) }, { argument := 2293233264602888902001790287872, coefficient := (-2293233264602888902001790287872) }, { argument := 8423864323258500647590297600, coefficient := (-8423864323258500647590297600) }, { argument := 2293233572777003391761225089024, coefficient := (-2293233572777003391761225089024) }, { argument := 8423864323258500647590297600, coefficient := (-8423864323258500647590297600) }, { argument := 108558636356701839091149307904, coefficient := (-108558636356701839091149307904) }, { argument := 403268280949552886068585431040, coefficient := (-403268280949552886068585431040) }, { argument := 108535784880631465099088887808, coefficient := (-108535784880631465099088887808) }, { argument := 698333665096601475152665903104, coefficient := (-698333665096601475152665903104) }, { argument := 698333498600901151868680404992, coefficient := (-698333498600901151868680404992) }, { argument := 21972231493862368119929962496, coefficient := (-21972231493862368119929962496) }, { argument := 979467625150843708321210302464, coefficient := (-979467625150843708321210302464) }, { argument := 114329413706886175383749656576, coefficient := (-114329413706886175383749656576) }, { argument := 34414059622400244349037812121600, coefficient := (-34414059622400244349037812121600) }, { argument := 1196276060494004127795819577344, coefficient := (-1196276060494004127795819577344) }, { argument := 105963846850284747916646023168, coefficient := (-105963846850284747916646023168) }, { argument := 34414051022473409739724672729088, coefficient := (-34414051022473409739724672729088) }, { argument := 105963846850284747916646023168, coefficient := (-105963846850284747916646023168) }, { argument := 103175324564750938760944812032, coefficient := (-103175324564750938760944812032) }, { argument := 3898354155176265199670293168128, coefficient := (-3898354155176265199670293168128) }, { argument := 103175324564750938760944812032, coefficient := (-103175324564750938760944812032) }, { argument := 1196276060494004127795819577344, coefficient := (-1196276060494004127795819577344) }, { argument := 3898354155176265199670293168128, coefficient := (-3898354155176265199670293168128) }, { argument := 979470503414570677862607618048, coefficient := (-979470503414570677862607618048) }, { argument := 103175324564750938760944812032, coefficient := (-103175324564750938760944812032) }, { argument := 103175324564750938760944812032, coefficient := (-103175324564750938760944812032) }, { argument := 114329413706886175383749656576, coefficient := (-114329413706886175383749656576) }, { argument := 34622575069348797513848376524800, coefficient := (-34622575069348797513848376524800) }, { argument := 485856338391576837221337006080, coefficient := (-485856338391576837221337006080) }, { argument := 25160417523849514784676380672, coefficient := (-25160417523849514784676380672) }, { argument := 125520267587451563312634266648576, coefficient := (-125520267587451563312634266648576) }, { argument := 676728471331124880415433687040, coefficient := (-676728471331124880415433687040) }, { argument := 34622559992605633374446235418624, coefficient := (-34622559992605633374446235418624) }, { argument := 677596071935395553339043217408, coefficient := (-677596071935395553339043217408) }, { argument := 677596071935395553339043217408, coefficient := (-677596071935395553339043217408) }, { argument := 484988737787306164297727475712, coefficient := (-484988737787306164297727475712) }, { argument := 25160417523849514784676380672, coefficient := (-25160417523849514784676380672) }, { argument := 18246289747456735830955679285248, coefficient := (-18246289747456735830955679285248) }, { argument := 86726944832106168973891993600, coefficient := (-86726944832106168973891993600) }, { argument := 18246293565651300437670857015296, coefficient := (-18246293565651300437670857015296) }, { argument := 86726944832106168973891993600, coefficient := (-86726944832106168973891993600) }, { argument := 108558636356701839091149307904, coefficient := (-108558636356701839091149307904) }, { argument := 403268280949552886068585431040, coefficient := (-403268280949552886068585431040) }, { argument := 108535784880631465099088887808, coefficient := (-108535784880631465099088887808) }, { argument := 441983332339621186805484748800, coefficient := (-441983332339621186805484748800) }, { argument := 441983226962595665739671142400, coefficient := (-441983226962595665739671142400) }, { argument := 291071855940428168895186075648, coefficient := (-291071855940428168895186075648) }, { argument := 26518999940377271208329084928, coefficient := (-26518999940377271208329084928) }, { argument := 26518993617755739944380268544, coefficient := (-26518993617755739944380268544) }, { argument := 16170591763165279840869810176, coefficient := (-16170591763165279840869810176) }, { argument := 51402405763713876864532480, coefficient := (-51402405763713876864532480) }, { argument := 8423864323258500647590297600, coefficient := (-8423864323258500647590297600) }, { argument := 86726944832106168973891993600, coefficient := (-86726944832106168973891993600) }, { argument := 8423864323258500647590297600, coefficient := (-8423864323258500647590297600) }, { argument := 51402405763713876864532480, coefficient := (-51402405763713876864532480) }, { argument := 16937444340202627515191132160, coefficient := (-16937444340202627515191132160) }, { argument := 662865479428937973559763927040, coefficient := (-662865479428937973559763927040) }, { argument := 662865722545495650005585756160, coefficient := (-662865722545495650005585756160) }, { argument := 16937687456760303961012961280, coefficient := (-16937687456760303961012961280) }, { argument := 105701830136788632799276957696, coefficient := (-105701830136788632799276957696) }] }

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
def constantNumerator : ℤ := (-5957549861094804222360177602461696)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    42571844245, 716112689, 1836361395, 287472077145, 71868045645, 7345551015,
    216505150149, 804262679115, 13528723503, 302853950727, 302853878521, 11460215387,
    42571844245, 716112689, 601874307141, 601874163643, 539, 1314373905,
    205757863155, 51439484655, 5257571085, 132876551379, 493603275165, 8303036313,
    95839857825, 95839834975, 216505150149, 804262679115, 13528723503, 9288799020399,
    9288796805777, 451, 594207118515, 594206976845, 12617, 438408536819079,
    168250635, 139407669, 6373457667426615, 937396395, 1753595881652397, 3754392741,
    3754392741, 2687202999, 139407669, 8147207420570265, 57082325, 8147208515425639,
    57082325, 61546757, 302853950727, 302853878521, 451, 407,
    68187555, 10674379305, 2668595805, 272754135, 11460215387, 42571844245,
    716112689, 11500782939, 11500780197, 11460215387
  ]
def negativeCoefficients : Array ℕ := #[
    392655957766669915382570024960, 105679580015351689701744443392, 16937444340202627515191132160, 662865479428937973559763927040, 662865722545495650005585756160, 16937687456760303961012961280,
    3993815095438662396037545590784, 14836027809670393019049537699840, 3992974401661126005487533293568, 698333665096601475152665903104, 698333498600901151868680404992, 105701830136788632799276957696,
    392655957766669915382570024960, 105679580015351689701744443392, 693913831773205263284611055616, 693913666331275195211283693568, 20851552536713124005332123648, 12122959521348615596660490240,
    474445330346704644327667138560, 474445504357147334639081226240, 12123133531791305908074577920, 1225569868342765499213238239232, 4552686645456794424300609208320, 1225311887205023645460766654464,
    441983332339621186805484748800, 441983226962595665739671142400, 3993815095438662396037545590784, 14836027809670393019049537699840, 3992974401661126005487533293568, 10709256142589021356296895463424,
    10709253589303692980872231780352, 279155478858853251989752512512, 685074165126412839548501360640, 685074001792023281896490270720, 488096546114488841512570322944, 987208261527224280070427246592,
    12414705616336475459829104640, 642904397988853193455435776, 3587937697010516741977937018880, 17291911394182947961904824320, 987186719896021441578075684864, 17314080511354977382368804864,
    17314080511354977382368804864, 12392536499164446039365124096, 642904397988853193455435776, 2293235018961899083861422243840, 8423864323258500647590297600, 2293235327136289982047986909184,
    8423864323258500647590297600, 290646342386122716643560783872, 698333665096601475152665903104, 698333498600901151868680404992, 279155478858853251989752512512, 15745049874660930371373236224,
    628919188048497052420669440, 24613442898129579043832463360, 24613451925504960115444285440, 628928215423878124032491520, 105701830136788632799276957696, 392655957766669915382570024960,
    105679580015351689701744443392, 26518999940377271208329084928, 26518993617755739944380268544, 105701830136788632799276957696
  ]
def negativeScales : Array ℕ := #[
    35, 29, 30, 38, 36, 32,
    37, 39, 33, 38, 38, 33,
    35, 29, 39, 39, 9, 30,
    37, 35, 32, 36, 38, 32,
    36, 36, 37, 39, 33, 43,
    43, 8, 39, 39, 13, 48,
    27, 27, 52, 29, 50, 31,
    31, 31, 27, 52, 25, 52,
    25, 25, 38, 38, 8, 8,
    26, 33, 31, 28, 33, 35,
    29, 33, 33, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35309180539004601, 29415611389981114, 30774202862716993, 38064630874180359, 36064631403311832, 32774223570713468,
    37655610387472184, 39548875818752372, 33655306669751960, 38139831275217814, 38139830931252512, 33415915107701151,
    35309180539004601, 29415611389981114, 39130671275932338, 39130670931967036, 9074141462752506, 30291728597039957,
    37582156608884994, 35582157138016467, 32291749305036267, 36951295590226169, 38844561012435944, 32950991872451703,
    36479906716815572, 36479906372850270, 37655610387472184, 39548875818752372, 33655306669751960, 43078629216492057,
    43078628872526756, 8816983624165144, 39112174932314948, 39112174588349647, 13623081294663700, 48639269219590424,
    27326036708865382, 27054734687047987, 52500997685319140, 29804084006371992, 50639237738549583, 31805932430791134,
    31805932430791134, 31323458164763605, 27054734687047987, 52855227063599408, 25766540762445095, 52855227257474719,
    25766540762445095, 25875179507725702, 38139831275217814, 38139830931252512, 8816983624165144, 8668884984300449,
    26023005119324339, 33313433131165952, 31313433660297425, 28023025827320649, 33415915107701151, 35309180539004601,
    29415611389981114, 33421013027761882, 33421012683796581, 33415915107701151
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
noncomputable def negativeCeiling : ℝ := 9332430983 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 392655957766669915382570024960, coefficient := (-392655957766669915382570024960) }, { argument := 105679580015351689701744443392, coefficient := (-105679580015351689701744443392) }, { argument := 16937444340202627515191132160, coefficient := (-16937444340202627515191132160) }, { argument := 662865479428937973559763927040, coefficient := (-662865479428937973559763927040) }, { argument := 662865722545495650005585756160, coefficient := (-662865722545495650005585756160) }, { argument := 16937687456760303961012961280, coefficient := (-16937687456760303961012961280) }, { argument := 3993815095438662396037545590784, coefficient := (-3993815095438662396037545590784) }, { argument := 14836027809670393019049537699840, coefficient := (-14836027809670393019049537699840) }, { argument := 3992974401661126005487533293568, coefficient := (-3992974401661126005487533293568) }, { argument := 698333665096601475152665903104, coefficient := (-698333665096601475152665903104) }, { argument := 698333498600901151868680404992, coefficient := (-698333498600901151868680404992) }, { argument := 105701830136788632799276957696, coefficient := (-105701830136788632799276957696) }, { argument := 392655957766669915382570024960, coefficient := (-392655957766669915382570024960) }, { argument := 105679580015351689701744443392, coefficient := (-105679580015351689701744443392) }, { argument := 693913831773205263284611055616, coefficient := (-693913831773205263284611055616) }, { argument := 693913666331275195211283693568, coefficient := (-693913666331275195211283693568) }, { argument := 20851552536713124005332123648, coefficient := (-20851552536713124005332123648) }, { argument := 12122959521348615596660490240, coefficient := (-12122959521348615596660490240) }, { argument := 474445330346704644327667138560, coefficient := (-474445330346704644327667138560) }, { argument := 474445504357147334639081226240, coefficient := (-474445504357147334639081226240) }, { argument := 12123133531791305908074577920, coefficient := (-12123133531791305908074577920) }, { argument := 1225569868342765499213238239232, coefficient := (-1225569868342765499213238239232) }, { argument := 4552686645456794424300609208320, coefficient := (-4552686645456794424300609208320) }, { argument := 1225311887205023645460766654464, coefficient := (-1225311887205023645460766654464) }, { argument := 441983332339621186805484748800, coefficient := (-441983332339621186805484748800) }, { argument := 441983226962595665739671142400, coefficient := (-441983226962595665739671142400) }, { argument := 3993815095438662396037545590784, coefficient := (-3993815095438662396037545590784) }, { argument := 14836027809670393019049537699840, coefficient := (-14836027809670393019049537699840) }, { argument := 3992974401661126005487533293568, coefficient := (-3992974401661126005487533293568) }, { argument := 10709256142589021356296895463424, coefficient := (-10709256142589021356296895463424) }, { argument := 10709253589303692980872231780352, coefficient := (-10709253589303692980872231780352) }, { argument := 279155478858853251989752512512, coefficient := (-279155478858853251989752512512) }, { argument := 685074165126412839548501360640, coefficient := (-685074165126412839548501360640) }, { argument := 685074001792023281896490270720, coefficient := (-685074001792023281896490270720) }, { argument := 488096546114488841512570322944, coefficient := (-488096546114488841512570322944) }, { argument := 987208261527224280070427246592, coefficient := (-987208261527224280070427246592) }, { argument := 12414705616336475459829104640, coefficient := (-12414705616336475459829104640) }, { argument := 642904397988853193455435776, coefficient := (-642904397988853193455435776) }, { argument := 3587937697010516741977937018880, coefficient := (-3587937697010516741977937018880) }, { argument := 17291911394182947961904824320, coefficient := (-17291911394182947961904824320) }, { argument := 987186719896021441578075684864, coefficient := (-987186719896021441578075684864) }, { argument := 17314080511354977382368804864, coefficient := (-17314080511354977382368804864) }, { argument := 17314080511354977382368804864, coefficient := (-17314080511354977382368804864) }, { argument := 12392536499164446039365124096, coefficient := (-12392536499164446039365124096) }, { argument := 642904397988853193455435776, coefficient := (-642904397988853193455435776) }, { argument := 2293235018961899083861422243840, coefficient := (-2293235018961899083861422243840) }, { argument := 8423864323258500647590297600, coefficient := (-8423864323258500647590297600) }, { argument := 2293235327136289982047986909184, coefficient := (-2293235327136289982047986909184) }, { argument := 8423864323258500647590297600, coefficient := (-8423864323258500647590297600) }, { argument := 290646342386122716643560783872, coefficient := (-290646342386122716643560783872) }, { argument := 698333665096601475152665903104, coefficient := (-698333665096601475152665903104) }, { argument := 698333498600901151868680404992, coefficient := (-698333498600901151868680404992) }, { argument := 279155478858853251989752512512, coefficient := (-279155478858853251989752512512) }, { argument := 15745049874660930371373236224, coefficient := (-15745049874660930371373236224) }, { argument := 628919188048497052420669440, coefficient := (-628919188048497052420669440) }, { argument := 24613442898129579043832463360, coefficient := (-24613442898129579043832463360) }, { argument := 24613451925504960115444285440, coefficient := (-24613451925504960115444285440) }, { argument := 628928215423878124032491520, coefficient := (-628928215423878124032491520) }, { argument := 105701830136788632799276957696, coefficient := (-105701830136788632799276957696) }, { argument := 392655957766669915382570024960, coefficient := (-392655957766669915382570024960) }, { argument := 105679580015351689701744443392, coefficient := (-105679580015351689701744443392) }, { argument := 26518999940377271208329084928, coefficient := (-26518999940377271208329084928) }, { argument := 26518993617755739944380268544, coefficient := (-26518993617755739944380268544) }, { argument := 105701830136788632799276957696, coefficient := (-105701830136788632799276957696) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk19
