import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 10, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-361234405056256975132810387914752)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    5985, 479753409, 124033, 15371600191, 3069157, 97643,
    122972771513, 50141, 50141, 1696877, 92365, 3069157,
    1696877, 3838057287, 97643, 92365, 124033, 67560782545,
    244177736541, 33780390121, 331455, 1392111, 6032481, 198873,
    198873, 464037, 6032481, 6032481, 198873, 74444793,
    2983095, 1392111, 6032481, 464037, 2983095, 464037,
    6032481, 6032481, 198873, 782932587, 4089, 27675706773,
    101181, 3219, 221405600019, 1653, 1653, 55941,
    3045, 101181, 55941, 6263514861, 3219, 3045,
    4089, 183255, 769671, 3335241, 109953, 109953,
    256557, 3335241, 3335241, 109953
  ]
def negativeCoefficients : Array ℕ := #[
    56526726799949653207941120, 17699776708625409327274917888, 2342917127879082819161423872, 567111949453523723398059917312, 57974736589859006780526297088, 1844424121947363070403674112,
    567111811033767880300011978752, 1894273422540535045279449088, 1894273422540535045279449088, 32053100281409579845123309568, 1744725520761019120652124160, 57974736589859006780526297088,
    32053100281409579845123309568, 17699915128381252425322856448, 1844424121947363070403674112, 1744725520761019120652124160, 2342917127879082819161423872, 77892279064197404263626833920,
    281517763404343998690430550016, 77892276409019179154058248192, 1565251982579558254305607680, 26296233307336578672334209024, 56975172165895920456724119552, 1878302379095469905166729216,
    30052838065527518482667667456, 2191352775611381556027850752, 56975172165895920456724119552, 56975172165895920456724119552, 30052838065527518482667667456, 703111190574737567834078969856,
    56349071372864097155001876480, 26296233307336578672334209024, 56975172165895920456724119552, 2191352775611381556027850752, 56349071372864097155001876480, 2191352775611381556027850752,
    56975172165895920456724119552, 56975172165895920456724119552, 1878302379095469905166729216, 28885114118712675866649821184, 1235824419101054673843388416, 1021053359801122097787448590336,
    30580080838606948631486398464, 972883053334872828344795136, 1021053110009148909667982770176, 999177189911491012894654464, 999177189911491012894654464, 16907129818765492665559547904,
    920294780181636459245076480, 30580080838606948631486398464, 16907129818765492665559547904, 28885363910685863986115641344, 972883053334872828344795136, 920294780181636459245076480,
    1235824419101054673843388416, 865397269818276833635860480, 14538674132947050805082456064, 31500460621385276744345321472, 1038476723781932200363032576, 16615627580510915205808521216,
    1211556177745587567090204672, 31500460621385276744345321472, 31500460621385276744345321472, 16615627580510915205808521216
  ]
def negativeScales : Array ℕ := #[
    12, 28, 16, 33, 21, 16,
    36, 15, 15, 20, 16, 21,
    20, 31, 16, 16, 16, 35,
    37, 34, 18, 20, 22, 17,
    17, 18, 22, 22, 17, 26,
    21, 20, 22, 18, 21, 18,
    22, 22, 17, 29, 11, 34,
    16, 11, 37, 10, 10, 15,
    11, 16, 15, 32, 11, 11,
    11, 17, 19, 21, 16, 16,
    17, 21, 21, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    12547135531832084, 28837717818330426, 16920364493267946, 33839548308387134, 21549411016800793, 16575229000958025,
    36839547956256439, 15613703148778080, 15613703148778080, 20694450562717709, 16495058652271465, 21549411016800793,
    20694450562717709, 31837729100773309, 16575229000958025, 16495058652271465, 16920364493267946, 35975467003524051,
    37829140710246807, 34975466954345704, 18338453490525323, 20408842818416730, 22524320035837256, 17601487896365009,
    17601487896365009, 18823880318738715, 22524320035837256, 22524320035837256, 17601487896365009, 26149667608038562,
    21508378491967993, 20408842818416730, 22524320035837256, 18823880318738715, 21508378491967993, 18823880318738715,
    22524320035837256, 22524320035837256, 17601487896365009, 29544312851306353, 11997532370288072, 34687901109471610,
    16626578877333553, 11652396861500322, 37687900756528561, 10690871009350625, 10690871009350625, 15771618423534793,
    11572226512796267, 16626578877333553, 15771618423534793, 32544325327354787, 11652396861500322, 11572226512796267,
    11997532370288072, 17483493036380206, 19553882364272945, 21669359581725990, 16746527442422252, 16746527442422252,
    17968919877847984, 21669359581725990, 21669359581725990, 16746527442422252
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
noncomputable def negativeCeiling : ℝ := 1038540283 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 56526726799949653207941120, coefficient := (-56526726799949653207941120) }, { argument := 17699776708625409327274917888, coefficient := (-17699776708625409327274917888) }, { argument := 2342917127879082819161423872, coefficient := (-2342917127879082819161423872) }, { argument := 567111949453523723398059917312, coefficient := (-567111949453523723398059917312) }, { argument := 57974736589859006780526297088, coefficient := (-57974736589859006780526297088) }, { argument := 1844424121947363070403674112, coefficient := (-1844424121947363070403674112) }, { argument := 567111811033767880300011978752, coefficient := (-567111811033767880300011978752) }, { argument := 1894273422540535045279449088, coefficient := (-1894273422540535045279449088) }, { argument := 1894273422540535045279449088, coefficient := (-1894273422540535045279449088) }, { argument := 32053100281409579845123309568, coefficient := (-32053100281409579845123309568) }, { argument := 1744725520761019120652124160, coefficient := (-1744725520761019120652124160) }, { argument := 57974736589859006780526297088, coefficient := (-57974736589859006780526297088) }, { argument := 32053100281409579845123309568, coefficient := (-32053100281409579845123309568) }, { argument := 17699915128381252425322856448, coefficient := (-17699915128381252425322856448) }, { argument := 1844424121947363070403674112, coefficient := (-1844424121947363070403674112) }, { argument := 1744725520761019120652124160, coefficient := (-1744725520761019120652124160) }, { argument := 2342917127879082819161423872, coefficient := (-2342917127879082819161423872) }, { argument := 77892279064197404263626833920, coefficient := (-77892279064197404263626833920) }, { argument := 281517763404343998690430550016, coefficient := (-281517763404343998690430550016) }, { argument := 77892276409019179154058248192, coefficient := (-77892276409019179154058248192) }, { argument := 1565251982579558254305607680, coefficient := (-1565251982579558254305607680) }, { argument := 26296233307336578672334209024, coefficient := (-26296233307336578672334209024) }, { argument := 56975172165895920456724119552, coefficient := (-56975172165895920456724119552) }, { argument := 1878302379095469905166729216, coefficient := (-1878302379095469905166729216) }, { argument := 30052838065527518482667667456, coefficient := (-30052838065527518482667667456) }, { argument := 2191352775611381556027850752, coefficient := (-2191352775611381556027850752) }, { argument := 56975172165895920456724119552, coefficient := (-56975172165895920456724119552) }, { argument := 56975172165895920456724119552, coefficient := (-56975172165895920456724119552) }, { argument := 30052838065527518482667667456, coefficient := (-30052838065527518482667667456) }, { argument := 703111190574737567834078969856, coefficient := (-703111190574737567834078969856) }, { argument := 56349071372864097155001876480, coefficient := (-56349071372864097155001876480) }, { argument := 26296233307336578672334209024, coefficient := (-26296233307336578672334209024) }, { argument := 56975172165895920456724119552, coefficient := (-56975172165895920456724119552) }, { argument := 2191352775611381556027850752, coefficient := (-2191352775611381556027850752) }, { argument := 56349071372864097155001876480, coefficient := (-56349071372864097155001876480) }, { argument := 2191352775611381556027850752, coefficient := (-2191352775611381556027850752) }, { argument := 56975172165895920456724119552, coefficient := (-56975172165895920456724119552) }, { argument := 56975172165895920456724119552, coefficient := (-56975172165895920456724119552) }, { argument := 1878302379095469905166729216, coefficient := (-1878302379095469905166729216) }, { argument := 28885114118712675866649821184, coefficient := (-28885114118712675866649821184) }, { argument := 1235824419101054673843388416, coefficient := (-1235824419101054673843388416) }, { argument := 1021053359801122097787448590336, coefficient := (-1021053359801122097787448590336) }, { argument := 30580080838606948631486398464, coefficient := (-30580080838606948631486398464) }, { argument := 972883053334872828344795136, coefficient := (-972883053334872828344795136) }, { argument := 1021053110009148909667982770176, coefficient := (-1021053110009148909667982770176) }, { argument := 999177189911491012894654464, coefficient := (-999177189911491012894654464) }, { argument := 999177189911491012894654464, coefficient := (-999177189911491012894654464) }, { argument := 16907129818765492665559547904, coefficient := (-16907129818765492665559547904) }, { argument := 920294780181636459245076480, coefficient := (-920294780181636459245076480) }, { argument := 30580080838606948631486398464, coefficient := (-30580080838606948631486398464) }, { argument := 16907129818765492665559547904, coefficient := (-16907129818765492665559547904) }, { argument := 28885363910685863986115641344, coefficient := (-28885363910685863986115641344) }, { argument := 972883053334872828344795136, coefficient := (-972883053334872828344795136) }, { argument := 920294780181636459245076480, coefficient := (-920294780181636459245076480) }, { argument := 1235824419101054673843388416, coefficient := (-1235824419101054673843388416) }, { argument := 865397269818276833635860480, coefficient := (-865397269818276833635860480) }, { argument := 14538674132947050805082456064, coefficient := (-14538674132947050805082456064) }, { argument := 31500460621385276744345321472, coefficient := (-31500460621385276744345321472) }, { argument := 1038476723781932200363032576, coefficient := (-1038476723781932200363032576) }, { argument := 16615627580510915205808521216, coefficient := (-16615627580510915205808521216) }, { argument := 1211556177745587567090204672, coefficient := (-1211556177745587567090204672) }, { argument := 31500460621385276744345321472, coefficient := (-31500460621385276744345321472) }, { argument := 31500460621385276744345321472, coefficient := (-31500460621385276744345321472) }, { argument := 16615627580510915205808521216, coefficient := (-16615627580510915205808521216) }] }

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

end TermShard6


end Parent1

namespace Parent1

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4897510568672427472847628744523776)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    41159073, 1649295, 769671, 3335241, 256557, 1649295,
    256557, 3335241, 3335241, 109953, 12489026277, 1530649,
    432263600923, 37875421, 1204979, 3458107961789, 618773, 618773,
    20940581, 1139845, 37875421, 20940581, 99913055811, 1204979,
    1139845, 1530649, 2912745324165, 10575915740465, 1456372648485, 16311285,
    61335, 529876395, 1517715, 48285, 4239010125, 24795,
    24795, 839115, 45675, 1517715, 839115, 130491315,
    48285, 45675, 61335, 959329330845, 1723993460947, 959329269693,
    80702618795, 80702587733, 11184252647767, 1338594575413315, 12778861671, 27584370294785445,
    12604401763, 423506171, 12778861671, 7706327721, 12604401763, 200960540013,
    262088445, 334648738260769, 12778861671, 423506171
  ]
def negativeCoefficients : Array ℕ := #[
    388736453602369953669228527616, 31154301713457966010890977280, 14538674132947050805082456064, 31500460621385276744345321472, 1211556177745587567090204672, 31154301713457966010890977280,
    1211556177745587567090204672, 31500460621385276744345321472, 31500460621385276744345321472, 1038476723781932200363032576, 460763742923305229996223627264, 28913142138551758306794274816,
    15947712037213401831903787483136, 715446474619908402357483864064, 22761409768647128879816769536, 15947708137594763079796712800256, 23376583005637591822514520064, 23376583005637591822514520064,
    395556391384867672154653589504, 21531063294666202994421268480, 715446474619908402357483864064, 395556391384867672154653589504, 460767642541943982103298310144, 22761409768647128879816769536,
    21531063294666202994421268480, 28913142138551758306794274816, 3358166721672870035987669975040, 12193200688092143944891986083840, 3358166690319169718204466462720, 19256966394133600232370339840,
    2317170785814477513456353280, 625567631952949215190560276480, 57337651572388028684036997120, 1824155725002886553146490880, 625567479213908284875472896000, 1873457231084045649177477120,
    1873457231084045649177477120, 31700868410185298747924152320, 1725552712840568361084518400, 57337651572388028684036997120, 31700868410185298747924152320, 19257119133174530547457720320,
    1824155725002886553146490880, 1725552712840568361084518400, 2317170785814477513456353280, 1106031415531297094291391774720, 3975258269854761445414922092544, 1106031345027841244573485498368,
    186087569373688415702053027840, 186087497749592863506291490816, 12592349014225236112974020608, 1507123507757893185161459138560, 29466048849784173491537313792, 15528619972605688625470730403840,
    29063771690534309292331237376, 976538743759209246377377792, 29466048849784173491537313792, 17769581902177548115107643392, 29063771690534309292331237376, 463383456316784871108432101376,
    19338713878366007058738708480, 1507123932931205916063824871424, 29466048849784173491537313792, 976538743759209246377377792
  ]
def negativeScales : Array ℕ := #[
    25, 20, 19, 21, 17, 20,
    17, 21, 21, 16, 33, 20,
    38, 25, 20, 41, 19, 19,
    24, 20, 25, 24, 36, 20,
    20, 20, 41, 43, 40, 23,
    15, 28, 20, 15, 31, 14,
    14, 19, 15, 20, 19, 26,
    15, 15, 15, 39, 40, 39,
    36, 36, 43, 50, 33, 54,
    33, 28, 33, 32, 33, 37,
    27, 48, 33, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    25294707153893291, 20653418037845600, 19553882364272945, 21669359581725990, 17968919877847984, 20653418037845600,
    17968919877847984, 21669359581725990, 21669359581725990, 16746527442422252, 33539941948630334, 20545712059206978,
    38653120401926824, 25174758589001392, 20200576573157124, 41653120049151382, 19239050720971759, 19239050720971759,
    24319798134856121, 20120406224473140, 25174758589001392, 24319798134856121, 36539954158654996, 20200576573157124,
    20120406224473140, 20545712059206978, 41405516703625972, 43265847821422704, 40405516690156174, 23959367118185431,
    15904422947861917, 28981080636006465, 20533469472931265, 15559287457087955, 31981080283756867, 14597761604906147,
    14597761604906147, 19678509018828490, 15479117108402347, 20533469472931265, 19678509018828490, 26959378561058800,
    15559287457087955, 15479117108402347, 15904422947861917, 39803235211534042, 40648891441009514, 39803235119570116,
    36231896438501327, 36231895883215728, 43346534089630264, 50249640496289583, 33573040276965031, 54614700564729108,
    33553208594716549, 28657807750656908, 33573040276965031, 32843396395183412, 33553208594716549, 37548121289861140,
    27965478521888712, 48249640903286979, 33573040276965031, 28657807750656908
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
noncomputable def negativeCeiling : ℝ := 42305315031 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 388736453602369953669228527616, coefficient := (-388736453602369953669228527616) }, { argument := 31154301713457966010890977280, coefficient := (-31154301713457966010890977280) }, { argument := 14538674132947050805082456064, coefficient := (-14538674132947050805082456064) }, { argument := 31500460621385276744345321472, coefficient := (-31500460621385276744345321472) }, { argument := 1211556177745587567090204672, coefficient := (-1211556177745587567090204672) }, { argument := 31154301713457966010890977280, coefficient := (-31154301713457966010890977280) }, { argument := 1211556177745587567090204672, coefficient := (-1211556177745587567090204672) }, { argument := 31500460621385276744345321472, coefficient := (-31500460621385276744345321472) }, { argument := 31500460621385276744345321472, coefficient := (-31500460621385276744345321472) }, { argument := 1038476723781932200363032576, coefficient := (-1038476723781932200363032576) }, { argument := 460763742923305229996223627264, coefficient := (-460763742923305229996223627264) }, { argument := 28913142138551758306794274816, coefficient := (-28913142138551758306794274816) }, { argument := 15947712037213401831903787483136, coefficient := (-15947712037213401831903787483136) }, { argument := 715446474619908402357483864064, coefficient := (-715446474619908402357483864064) }, { argument := 22761409768647128879816769536, coefficient := (-22761409768647128879816769536) }, { argument := 15947708137594763079796712800256, coefficient := (-15947708137594763079796712800256) }, { argument := 23376583005637591822514520064, coefficient := (-23376583005637591822514520064) }, { argument := 23376583005637591822514520064, coefficient := (-23376583005637591822514520064) }, { argument := 395556391384867672154653589504, coefficient := (-395556391384867672154653589504) }, { argument := 21531063294666202994421268480, coefficient := (-21531063294666202994421268480) }, { argument := 715446474619908402357483864064, coefficient := (-715446474619908402357483864064) }, { argument := 395556391384867672154653589504, coefficient := (-395556391384867672154653589504) }, { argument := 460767642541943982103298310144, coefficient := (-460767642541943982103298310144) }, { argument := 22761409768647128879816769536, coefficient := (-22761409768647128879816769536) }, { argument := 21531063294666202994421268480, coefficient := (-21531063294666202994421268480) }, { argument := 28913142138551758306794274816, coefficient := (-28913142138551758306794274816) }, { argument := 3358166721672870035987669975040, coefficient := (-3358166721672870035987669975040) }, { argument := 12193200688092143944891986083840, coefficient := (-12193200688092143944891986083840) }, { argument := 3358166690319169718204466462720, coefficient := (-3358166690319169718204466462720) }, { argument := 19256966394133600232370339840, coefficient := (-19256966394133600232370339840) }, { argument := 2317170785814477513456353280, coefficient := (-2317170785814477513456353280) }, { argument := 625567631952949215190560276480, coefficient := (-625567631952949215190560276480) }, { argument := 57337651572388028684036997120, coefficient := (-57337651572388028684036997120) }, { argument := 1824155725002886553146490880, coefficient := (-1824155725002886553146490880) }, { argument := 625567479213908284875472896000, coefficient := (-625567479213908284875472896000) }, { argument := 1873457231084045649177477120, coefficient := (-1873457231084045649177477120) }, { argument := 1873457231084045649177477120, coefficient := (-1873457231084045649177477120) }, { argument := 31700868410185298747924152320, coefficient := (-31700868410185298747924152320) }, { argument := 1725552712840568361084518400, coefficient := (-1725552712840568361084518400) }, { argument := 57337651572388028684036997120, coefficient := (-57337651572388028684036997120) }, { argument := 31700868410185298747924152320, coefficient := (-31700868410185298747924152320) }, { argument := 19257119133174530547457720320, coefficient := (-19257119133174530547457720320) }, { argument := 1824155725002886553146490880, coefficient := (-1824155725002886553146490880) }, { argument := 1725552712840568361084518400, coefficient := (-1725552712840568361084518400) }, { argument := 2317170785814477513456353280, coefficient := (-2317170785814477513456353280) }, { argument := 1106031415531297094291391774720, coefficient := (-1106031415531297094291391774720) }, { argument := 3975258269854761445414922092544, coefficient := (-3975258269854761445414922092544) }, { argument := 1106031345027841244573485498368, coefficient := (-1106031345027841244573485498368) }, { argument := 186087569373688415702053027840, coefficient := (-186087569373688415702053027840) }, { argument := 186087497749592863506291490816, coefficient := (-186087497749592863506291490816) }, { argument := 12592349014225236112974020608, coefficient := (-12592349014225236112974020608) }, { argument := 1507123507757893185161459138560, coefficient := (-1507123507757893185161459138560) }, { argument := 29466048849784173491537313792, coefficient := (-29466048849784173491537313792) }, { argument := 15528619972605688625470730403840, coefficient := (-15528619972605688625470730403840) }, { argument := 29063771690534309292331237376, coefficient := (-29063771690534309292331237376) }, { argument := 976538743759209246377377792, coefficient := (-976538743759209246377377792) }, { argument := 29466048849784173491537313792, coefficient := (-29466048849784173491537313792) }, { argument := 17769581902177548115107643392, coefficient := (-17769581902177548115107643392) }, { argument := 29063771690534309292331237376, coefficient := (-29063771690534309292331237376) }, { argument := 463383456316784871108432101376, coefficient := (-463383456316784871108432101376) }, { argument := 19338713878366007058738708480, coefficient := (-19338713878366007058738708480) }, { argument := 1507123932931205916063824871424, coefficient := (-1507123932931205916063824871424) }, { argument := 29466048849784173491537313792, coefficient := (-29466048849784173491537313792) }, { argument := 976538743759209246377377792, coefficient := (-976538743759209246377377792) }] }

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

end TermShard7


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10
