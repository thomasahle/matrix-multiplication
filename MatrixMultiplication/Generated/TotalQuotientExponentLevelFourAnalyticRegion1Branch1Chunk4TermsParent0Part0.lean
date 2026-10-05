import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 4, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1238680676399350533692929431568384)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    83397, 2139707, 111, 9, 1929, 3489,
    17117657, 1929, 57, 57, 111, 111,
    3489, 111, 667175, 9, 1700749627, 101357504495,
    39401277685, 589505242509, 1535114715, 2558524525, 78290850465, 2558524525,
    1535114715, 1254188722155, 80337670085, 101357520143, 78290850465, 2558524525,
    80337670085, 2558524525, 78290850465, 2558524525, 1700749627, 119849769629471,
    40270590535, 841586463834867, 454482378895, 40270590535, 1683172525442811, 40270590535,
    40270590535, 1669503624751, 10355294709, 454482378895, 1669503624751, 119849775380255,
    40270590535, 10355294709, 40270590535, 275525, 177504975, 1887840055,
    88752755, 275525, 1020932289, 159821223939, 39955320639, 4083787773,
    59746901347761, 2068042329, 53661777, 440785011130889
  ]
def negativeCoefficients : Array ℕ := #[
    3150649580575038415092842496, 80835844959692479610094616576, 2147052255635581414278168576, 2785365088392105618523029504, 37312286496585914848131416064, 67487074954167059048797569024,
    80835849682058962479739830272, 37312286496585914848131416064, 2205080694977083614664065024, 2205080694977083614664065024, 2147052255635581414278168576, 2147052255635581414278168576,
    67487074954167059048797569024, 2147052255635581414278168576, 3150644858208555545447628800, 2785365088392105618523029504, 7843323275681495104312311808, 233714493171141311155394314240,
    181706321408089537814714122240, 1359306542334200974577466605568, 113271473085562309287094517760, 5899555889873036942036172800, 180526410230114930426306887680, 188785788475937182145157529600,
    113271473085562309287094517760, 2891962297215762708986131906560, 185246054942013359979935825920, 233714529252972719331277275136, 180526410230114930426306887680, 5899555889873036942036172800,
    185246054942013359979935825920, 5899555889873036942036172800, 180526410230114930426306887680, 188785788475937182145157529600, 7843323275681495104312311808, 134938844460931346013989371904,
    46428829831018450727898972160, 3790168484926760429299571884032, 523982508092922515357716971520, 46428829831018450727898972160, 3790167579192250158708978352128, 46428829831018450727898972160,
    46428829831018450727898972160, 1924806630994507771605183102976, 47755367826190406462981799936, 523982508092922515357716971520, 1924806630994507771605183102976, 134938850935738515886041989120,
    46428829831018450727898972160, 47755367826190406462981799936, 46428829831018450727898972160, 40660313287270593671987200, 13097555382540848467437158400, 139298009386731055907099115520,
    13097594858573166205877616640, 40660313287270593671987200, 9416438325884738626243264512, 368522651943719421408001916928, 368522787105319092487100301312, 9416573487484409705341648896,
    134538061323159112423443529728, 9537161894165312198374588416, 494942533429736760793890816, 496279802969892908015588212736
  ]
def negativeScales : Array ℕ := #[
    16, 21, 6, 3, 10, 11,
    24, 10, 5, 5, 6, 6,
    11, 6, 19, 3, 30, 36,
    35, 39, 30, 31, 36, 31,
    30, 40, 36, 36, 36, 31,
    36, 31, 36, 31, 30, 46,
    35, 49, 38, 35, 50, 35,
    35, 40, 33, 38, 40, 46,
    35, 33, 35, 18, 27, 30,
    26, 18, 29, 37, 35, 31,
    45, 30, 25, 48
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    16347707866780927, 21028981824554590, 6794415866926375, 3169925001442313, 10913637433615165, 11768597882530236,
    24028981908835697, 10913637433615165, 5832890015409720, 5832890015409720, 6794415866926375, 6794415866926375,
    11768597882530236, 6794415866926375, 19347705704388811, 3169925001442313, 30663523626721344, 36560661953454727,
    35197523362309743, 39100713687005219, 30515699322336452, 31252664916502204, 36188124664307494, 31252664916502204,
    30515699322336452, 40189891590481682, 36225357570506469, 36560662176184069, 36188124664307494, 31252664916502204,
    36225357570506469, 31252664916502204, 36188124664307494, 31252664916502204, 30663523626721344, 46768220464654104,
    35229007577245428, 49580104828784466, 38725433403495124, 35229007577245428, 50580104484024372, 35229007577245428,
    35229007577245428, 40602556364373274, 33269649561742774, 38725433403495124, 40602556364373274, 46768220533879330,
    35229007577245428, 33269649561742774, 35229007577245428, 18071823703359091, 27403284219250004, 30814089394103419,
    26403288567526348, 18071823703359091, 29927240046985554, 37217668051766162, 35217668580897635, 31927260754984400,
    45763929126411896, 30945618578918231, 25677391494227422, 48647068494423606
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
noncomputable def negativeCeiling : ℝ := 2759183561 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3150649580575038415092842496, coefficient := (-3150649580575038415092842496) }, { argument := 80835844959692479610094616576, coefficient := (-80835844959692479610094616576) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 2785365088392105618523029504, coefficient := (-2785365088392105618523029504) }, { argument := 37312286496585914848131416064, coefficient := (-37312286496585914848131416064) }, { argument := 67487074954167059048797569024, coefficient := (-67487074954167059048797569024) }, { argument := 80835849682058962479739830272, coefficient := (-80835849682058962479739830272) }, { argument := 37312286496585914848131416064, coefficient := (-37312286496585914848131416064) }, { argument := 2205080694977083614664065024, coefficient := (-2205080694977083614664065024) }, { argument := 2205080694977083614664065024, coefficient := (-2205080694977083614664065024) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 67487074954167059048797569024, coefficient := (-67487074954167059048797569024) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 3150644858208555545447628800, coefficient := (-3150644858208555545447628800) }, { argument := 2785365088392105618523029504, coefficient := (-2785365088392105618523029504) }, { argument := 7843323275681495104312311808, coefficient := (-7843323275681495104312311808) }, { argument := 233714493171141311155394314240, coefficient := (-233714493171141311155394314240) }, { argument := 181706321408089537814714122240, coefficient := (-181706321408089537814714122240) }, { argument := 1359306542334200974577466605568, coefficient := (-1359306542334200974577466605568) }, { argument := 113271473085562309287094517760, coefficient := (-113271473085562309287094517760) }, { argument := 5899555889873036942036172800, coefficient := (-5899555889873036942036172800) }, { argument := 180526410230114930426306887680, coefficient := (-180526410230114930426306887680) }, { argument := 188785788475937182145157529600, coefficient := (-188785788475937182145157529600) }, { argument := 113271473085562309287094517760, coefficient := (-113271473085562309287094517760) }, { argument := 2891962297215762708986131906560, coefficient := (-2891962297215762708986131906560) }, { argument := 185246054942013359979935825920, coefficient := (-185246054942013359979935825920) }, { argument := 233714529252972719331277275136, coefficient := (-233714529252972719331277275136) }, { argument := 180526410230114930426306887680, coefficient := (-180526410230114930426306887680) }, { argument := 5899555889873036942036172800, coefficient := (-5899555889873036942036172800) }, { argument := 185246054942013359979935825920, coefficient := (-185246054942013359979935825920) }, { argument := 5899555889873036942036172800, coefficient := (-5899555889873036942036172800) }, { argument := 180526410230114930426306887680, coefficient := (-180526410230114930426306887680) }, { argument := 188785788475937182145157529600, coefficient := (-188785788475937182145157529600) }, { argument := 7843323275681495104312311808, coefficient := (-7843323275681495104312311808) }, { argument := 134938844460931346013989371904, coefficient := (-134938844460931346013989371904) }, { argument := 46428829831018450727898972160, coefficient := (-46428829831018450727898972160) }, { argument := 3790168484926760429299571884032, coefficient := (-3790168484926760429299571884032) }, { argument := 523982508092922515357716971520, coefficient := (-523982508092922515357716971520) }, { argument := 46428829831018450727898972160, coefficient := (-46428829831018450727898972160) }, { argument := 3790167579192250158708978352128, coefficient := (-3790167579192250158708978352128) }, { argument := 46428829831018450727898972160, coefficient := (-46428829831018450727898972160) }, { argument := 46428829831018450727898972160, coefficient := (-46428829831018450727898972160) }, { argument := 1924806630994507771605183102976, coefficient := (-1924806630994507771605183102976) }, { argument := 47755367826190406462981799936, coefficient := (-47755367826190406462981799936) }, { argument := 523982508092922515357716971520, coefficient := (-523982508092922515357716971520) }, { argument := 1924806630994507771605183102976, coefficient := (-1924806630994507771605183102976) }, { argument := 134938850935738515886041989120, coefficient := (-134938850935738515886041989120) }, { argument := 46428829831018450727898972160, coefficient := (-46428829831018450727898972160) }, { argument := 47755367826190406462981799936, coefficient := (-47755367826190406462981799936) }, { argument := 46428829831018450727898972160, coefficient := (-46428829831018450727898972160) }, { argument := 40660313287270593671987200, coefficient := (-40660313287270593671987200) }, { argument := 13097555382540848467437158400, coefficient := (-13097555382540848467437158400) }, { argument := 139298009386731055907099115520, coefficient := (-139298009386731055907099115520) }, { argument := 13097594858573166205877616640, coefficient := (-13097594858573166205877616640) }, { argument := 40660313287270593671987200, coefficient := (-40660313287270593671987200) }, { argument := 9416438325884738626243264512, coefficient := (-9416438325884738626243264512) }, { argument := 368522651943719421408001916928, coefficient := (-368522651943719421408001916928) }, { argument := 368522787105319092487100301312, coefficient := (-368522787105319092487100301312) }, { argument := 9416573487484409705341648896, coefficient := (-9416573487484409705341648896) }, { argument := 134538061323159112423443529728, coefficient := (-134538061323159112423443529728) }, { argument := 9537161894165312198374588416, coefficient := (-9537161894165312198374588416) }, { argument := 494942533429736760793890816, coefficient := (-494942533429736760793890816) }, { argument := 496279802969892908015588212736, coefficient := (-496279802969892908015588212736) }] }

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
def constantNumerator : ℤ := (-4360195728200752414082632289091584)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3331158003, 119521407361685, 3331158003, 3471504189, 2068042329, 103195725,
    26491257, 4147057707, 1036764807, 105966549, 315435435, 1130645145,
    78881775, 1646159181, 275525, 1646160243, 275525, 1700750725,
    101357536337, 39401305867, 589505244339, 1535115813, 2558526355, 78290906463,
    2558526355, 1535115813, 1254189619221, 80337727547, 101357551985, 78290906463,
    2558526355, 80337727547, 2558526355, 78290906463, 2558526355, 1700750725,
    883981267193415, 144345696845, 6277875953899259, 1629044292965, 144345696845, 12555749085569987,
    144345696845, 144345696845, 5984160174917, 37117464903, 1629044292965, 5984160174917,
    883981525499463, 144345696845, 37117464903, 144345696845, 418548712037277, 323740427979,
    8400450227, 3123529718309909, 521474102553, 837265977366705, 521474102553, 543444510839,
    323740427979, 16154711975, 1644495723, 257436582273
  ]
def negativeCoefficients : Array ℕ := #[
    15362254787607598690794995712, 134569141414220455858342461440, 15362254787607598690794995712, 16009487331323408301063929856, 9537161894165312198374588416, 475906282143977654609510400,
    488677438069866675214221312, 19124928044983443027161776128, 19124935059357877055218778112, 488684452444300703271223296, 46550053929793955821183303680, 166853773023977813398058434560,
    46563581296158088509574348800, 7591569279123579780017946624, 40660313287270593671987200, 7591574176734131349903900672, 40660313287270593671987200, 7843328339312743337584230400,
    233714566593794410537837133824, 181706451374624909135360032768, 1359306546553893681438526537728, 113271554103662281019445215232, 5899560109565743803096104960, 180526539352711760374740811776,
    188785923506103801699075358720, 113271554103662281019445215232, 2891964365709127612277710651392, 185246187440364355417217695744, 233714602675625818713720094720, 180526539352711760374740811776,
    5899560109565743803096104960, 185246187440364355417217695744, 5899560109565743803096104960, 180526539352711760374740811776, 188785923506103801699075358720, 7843328339312743337584230400,
    497637213191845331803287060480, 166419257990061204509000990720, 14136519903329449978696126431232, 1878160197316405022315868323840, 166419257990061204509000990720, 14136516725782609837200546725888,
    166419257990061204509000990720, 166419257990061204509000990720, 6899266952673680221216012500992, 171174093932634381780686733312, 1878160197316405022315868323840, 6899266952673680221216012500992,
    497637358605223021846468755456, 166419257990061204509000990720, 171174093932634381780686733312, 166419257990061204509000990720, 3769951647134963461821283958784, 373247301327613260144001941504,
    19370119430175538450586927104, 14067127275461176509318891044864, 601218706928909981908601929728, 3770710743678686775769489735680, 601218706928909981908601929728, 626548863106831839882446372864,
    373247301327613260144001941504, 18625114836707248510179737600, 15167795866245477188379869184, 593608343550063020112290512896
  ]
def negativeScales : Array ℕ := #[
    31, 46, 31, 31, 30, 26,
    24, 31, 29, 26, 28, 30,
    26, 30, 18, 30, 18, 30,
    36, 35, 39, 30, 31, 36,
    31, 30, 40, 36, 36, 36,
    31, 36, 31, 36, 31, 30,
    49, 37, 52, 40, 37, 53,
    37, 37, 42, 35, 40, 42,
    49, 37, 35, 37, 48, 38,
    32, 51, 38, 49, 38, 38,
    38, 33, 30, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31633376639335852, 46764262369768305, 31633376639335852, 31692913766360557, 30945618578918231, 26620807965828875,
    24659012964897186, 31949440987038129, 29949441516169694, 26659033672893510, 28232769496041627, 30074499061936313,
    26233188679858471, 30616456702838236, 18071823703359091, 30616457633575468, 18071823703359091, 30663524558121604,
    36560662406684989, 35197524394205649, 39100713691483775, 30515700354232357, 31252665948398110, 36188125696203399,
    31252665948398110, 30515700354232357, 40189892622377587, 36225358602402374, 36560662629414261, 36188125696203399,
    31252665948398110, 36225358602402374, 31252665948398110, 36188125696203399, 31252665948398110, 30663524558121604,
    49651009125648159, 37070737143140114, 52479197945944768, 40567162969261831, 37070737143140114, 53479197621661874,
    37070737143140114, 37070737143140114, 42444285930261930, 35111379127637460, 40567162969261831, 42444285930261930,
    49651009547214559, 37070737143140114, 35111379127637460, 37070737143140114, 48572388866434117, 38236046581081016,
    32967819520066896, 51472098679564012, 38923804657815280, 49572679330259763, 38923804657815280, 38983341796249142,
    38236046581081016, 33911235982995492, 30614998110015639, 37905426126661032
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
noncomputable def negativeCeiling : ℝ := 45926663331 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 15362254787607598690794995712, coefficient := (-15362254787607598690794995712) }, { argument := 134569141414220455858342461440, coefficient := (-134569141414220455858342461440) }, { argument := 15362254787607598690794995712, coefficient := (-15362254787607598690794995712) }, { argument := 16009487331323408301063929856, coefficient := (-16009487331323408301063929856) }, { argument := 9537161894165312198374588416, coefficient := (-9537161894165312198374588416) }, { argument := 475906282143977654609510400, coefficient := (-475906282143977654609510400) }, { argument := 488677438069866675214221312, coefficient := (-488677438069866675214221312) }, { argument := 19124928044983443027161776128, coefficient := (-19124928044983443027161776128) }, { argument := 19124935059357877055218778112, coefficient := (-19124935059357877055218778112) }, { argument := 488684452444300703271223296, coefficient := (-488684452444300703271223296) }, { argument := 46550053929793955821183303680, coefficient := (-46550053929793955821183303680) }, { argument := 166853773023977813398058434560, coefficient := (-166853773023977813398058434560) }, { argument := 46563581296158088509574348800, coefficient := (-46563581296158088509574348800) }, { argument := 7591569279123579780017946624, coefficient := (-7591569279123579780017946624) }, { argument := 40660313287270593671987200, coefficient := (-40660313287270593671987200) }, { argument := 7591574176734131349903900672, coefficient := (-7591574176734131349903900672) }, { argument := 40660313287270593671987200, coefficient := (-40660313287270593671987200) }, { argument := 7843328339312743337584230400, coefficient := (-7843328339312743337584230400) }, { argument := 233714566593794410537837133824, coefficient := (-233714566593794410537837133824) }, { argument := 181706451374624909135360032768, coefficient := (-181706451374624909135360032768) }, { argument := 1359306546553893681438526537728, coefficient := (-1359306546553893681438526537728) }, { argument := 113271554103662281019445215232, coefficient := (-113271554103662281019445215232) }, { argument := 5899560109565743803096104960, coefficient := (-5899560109565743803096104960) }, { argument := 180526539352711760374740811776, coefficient := (-180526539352711760374740811776) }, { argument := 188785923506103801699075358720, coefficient := (-188785923506103801699075358720) }, { argument := 113271554103662281019445215232, coefficient := (-113271554103662281019445215232) }, { argument := 2891964365709127612277710651392, coefficient := (-2891964365709127612277710651392) }, { argument := 185246187440364355417217695744, coefficient := (-185246187440364355417217695744) }, { argument := 233714602675625818713720094720, coefficient := (-233714602675625818713720094720) }, { argument := 180526539352711760374740811776, coefficient := (-180526539352711760374740811776) }, { argument := 5899560109565743803096104960, coefficient := (-5899560109565743803096104960) }, { argument := 185246187440364355417217695744, coefficient := (-185246187440364355417217695744) }, { argument := 5899560109565743803096104960, coefficient := (-5899560109565743803096104960) }, { argument := 180526539352711760374740811776, coefficient := (-180526539352711760374740811776) }, { argument := 188785923506103801699075358720, coefficient := (-188785923506103801699075358720) }, { argument := 7843328339312743337584230400, coefficient := (-7843328339312743337584230400) }, { argument := 497637213191845331803287060480, coefficient := (-497637213191845331803287060480) }, { argument := 166419257990061204509000990720, coefficient := (-166419257990061204509000990720) }, { argument := 14136519903329449978696126431232, coefficient := (-14136519903329449978696126431232) }, { argument := 1878160197316405022315868323840, coefficient := (-1878160197316405022315868323840) }, { argument := 166419257990061204509000990720, coefficient := (-166419257990061204509000990720) }, { argument := 14136516725782609837200546725888, coefficient := (-14136516725782609837200546725888) }, { argument := 166419257990061204509000990720, coefficient := (-166419257990061204509000990720) }, { argument := 166419257990061204509000990720, coefficient := (-166419257990061204509000990720) }, { argument := 6899266952673680221216012500992, coefficient := (-6899266952673680221216012500992) }, { argument := 171174093932634381780686733312, coefficient := (-171174093932634381780686733312) }, { argument := 1878160197316405022315868323840, coefficient := (-1878160197316405022315868323840) }, { argument := 6899266952673680221216012500992, coefficient := (-6899266952673680221216012500992) }, { argument := 497637358605223021846468755456, coefficient := (-497637358605223021846468755456) }, { argument := 166419257990061204509000990720, coefficient := (-166419257990061204509000990720) }, { argument := 171174093932634381780686733312, coefficient := (-171174093932634381780686733312) }, { argument := 166419257990061204509000990720, coefficient := (-166419257990061204509000990720) }, { argument := 3769951647134963461821283958784, coefficient := (-3769951647134963461821283958784) }, { argument := 373247301327613260144001941504, coefficient := (-373247301327613260144001941504) }, { argument := 19370119430175538450586927104, coefficient := (-19370119430175538450586927104) }, { argument := 14067127275461176509318891044864, coefficient := (-14067127275461176509318891044864) }, { argument := 601218706928909981908601929728, coefficient := (-601218706928909981908601929728) }, { argument := 3770710743678686775769489735680, coefficient := (-3770710743678686775769489735680) }, { argument := 601218706928909981908601929728, coefficient := (-601218706928909981908601929728) }, { argument := 626548863106831839882446372864, coefficient := (-626548863106831839882446372864) }, { argument := 373247301327613260144001941504, coefficient := (-373247301327613260144001941504) }, { argument := 18625114836707248510179737600, coefficient := (-18625114836707248510179737600) }, { argument := 15167795866245477188379869184, coefficient := (-15167795866245477188379869184) }, { argument := 593608343550063020112290512896, coefficient := (-593608343550063020112290512896) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4
