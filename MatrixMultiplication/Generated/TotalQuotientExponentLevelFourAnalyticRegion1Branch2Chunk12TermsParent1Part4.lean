import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 2,
parent chunk 12, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-69309194786319350883716662558720)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    14553, 1246707, 14553, 483483, 1246707, 2694649431,
    14553, 14553, 30723, 13661260605, 49601014639, 3415315029,
    355824279411, 17021341720717, 8380445, 78776183, 930229395, 65367471,
    8510670971975, 930229395, 8380445, 65367471, 65367471, 65367471,
    65367471, 65367471, 177912028089, 78776183, 2676605689, 333205422317,
    635147331, 13242877903751, 20938923, 48857487, 635147331, 635147331,
    20938923, 7838136843, 314083845, 333205422317, 635147331, 48857487,
    314083845, 48857487, 635147331, 635147331, 11152700781, 115732941897,
    741, 4272497062839, 11661, 351, 34179601490817, 351,
    351, 30069, 351, 11661, 30069, 926238547071,
    351, 351, 741, 78346885
  ]
def negativeCoefficients : Array ℕ := #[
    274898397700807787179671552, 11774814701517933550862598144, 274898397700807787179671552, 2283183914237264676853383168, 11774814701517933550862598144, 12426877105506016330329882624,
    274898397700807787179671552, 274898397700807787179671552, 290170530906408219800764416, 31500722263085689212984360960, 114372152855244245592417763328, 31500721135528457707488018432,
    400622523041188712980414464, 19164327057691739598679441408, 154591924138798843292549120, 181645510863088640868745216, 2144962947425833950684119040, 4823268033130523910727532544,
    19164327309029753502878924800, 2144962947425833950684119040, 154591924138798843292549120, 150727126035328872210235392, 150727126035328872210235392, 150727126035328872210235392,
    4823268033130523910727532544, 150727126035328872210235392, 400622271703174808780931072, 181645510863088640868745216, 385739532275140790539255808, 48019962105109438460984295424,
    2929100066014172244527284224, 477124959941167830341641043968, 1545019815040442502607798272, 112657694846698932481818624, 2929100066014172244527284224, 2929100066014172244527284224,
    1545019815040442502607798272, 36147026089383686050594947072, 2896912153200829692389621760, 48019962105109438460984295424, 2929100066014172244527284224, 112657694846698932481818624,
    2896912153200829692389621760, 112657694846698932481818624, 2929100066014172244527284224, 2929100066014172244527284224, 401818392651889917724459008, 4169718672014563715680567296,
    13997094255225628413394944, 153932929441146072262772785152, 110135031113485865673818112, 13260405083897963760058368, 153931240537715490759200735232, 13260405083897963760058368,
    13260405083897963760058368, 567987351093629447722500096, 13260405083897963760058368, 110135031113485865673818112, 567987351093629447722500096, 4171407575445145219252617216,
    13260405083897963760058368, 13260405083897963760058368, 13997094255225628413394944, 180655617070919220482539520
  ]
def negativeScales : Array ℕ := #[
    13, 20, 13, 18, 20, 31,
    13, 13, 14, 33, 35, 31,
    38, 43, 22, 26, 29, 25,
    42, 29, 22, 25, 25, 25,
    25, 25, 37, 26, 31, 38,
    29, 43, 24, 25, 29, 29,
    24, 32, 28, 38, 29, 25,
    28, 25, 29, 29, 33, 36,
    9, 41, 13, 8, 44, 8,
    8, 14, 8, 13, 14, 39,
    8, 8, 9, 26
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    13829028966070369, 20249691013388697, 13829028966070369, 18883105640887843, 20249691013388697, 31327450447165949,
    13829028966070369, 13829028966070369, 14907031481868981, 33669371564649698, 35529650581576838, 31669371513008937,
    38372373998971937, 43952410007475395, 22998595445260584, 26231256178899205, 29793011289018899, 25962069558846065,
    42952410026396183, 29793011289018899, 22998595445260584, 25962069558846065, 25962069558846065, 25962069558846065,
    25962069558846065, 25962069558846065, 37372373093870004, 26231256178899205, 31317757474315525, 38277620921914012,
    29242516042399155, 43590281912051735, 24319683902921615, 25542076324259107, 29242516042399155, 29242516042399155,
    24319683902921615, 32867863617027606, 28226574498530133, 38277620921914012, 29242516042399155, 25542076324259107,
    28226574498530133, 25542076324259107, 29242516042399155, 29242516042399155, 33376674069919037, 36752008611527698,
    9533329732306630, 41958216650725820, 13509403893060724, 8455327220304618, 44958200821841987, 8455327220304618,
    8455327220304618, 14875989271598903, 8455327220304618, 13509403893060724, 14875989271598903, 39752592842620096,
    8455327220304618, 8455327220304618, 9533329732306630, 26223372579823372
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
noncomputable def negativeCeiling : ℝ := 593786527 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 274898397700807787179671552, coefficient := (-274898397700807787179671552) }, { argument := 11774814701517933550862598144, coefficient := (-11774814701517933550862598144) }, { argument := 274898397700807787179671552, coefficient := (-274898397700807787179671552) }, { argument := 2283183914237264676853383168, coefficient := (-2283183914237264676853383168) }, { argument := 11774814701517933550862598144, coefficient := (-11774814701517933550862598144) }, { argument := 12426877105506016330329882624, coefficient := (-12426877105506016330329882624) }, { argument := 274898397700807787179671552, coefficient := (-274898397700807787179671552) }, { argument := 274898397700807787179671552, coefficient := (-274898397700807787179671552) }, { argument := 290170530906408219800764416, coefficient := (-290170530906408219800764416) }, { argument := 31500722263085689212984360960, coefficient := (-31500722263085689212984360960) }, { argument := 114372152855244245592417763328, coefficient := (-114372152855244245592417763328) }, { argument := 31500721135528457707488018432, coefficient := (-31500721135528457707488018432) }, { argument := 400622523041188712980414464, coefficient := (-400622523041188712980414464) }, { argument := 19164327057691739598679441408, coefficient := (-19164327057691739598679441408) }, { argument := 154591924138798843292549120, coefficient := (-154591924138798843292549120) }, { argument := 181645510863088640868745216, coefficient := (-181645510863088640868745216) }, { argument := 2144962947425833950684119040, coefficient := (-2144962947425833950684119040) }, { argument := 4823268033130523910727532544, coefficient := (-4823268033130523910727532544) }, { argument := 19164327309029753502878924800, coefficient := (-19164327309029753502878924800) }, { argument := 2144962947425833950684119040, coefficient := (-2144962947425833950684119040) }, { argument := 154591924138798843292549120, coefficient := (-154591924138798843292549120) }, { argument := 150727126035328872210235392, coefficient := (-150727126035328872210235392) }, { argument := 150727126035328872210235392, coefficient := (-150727126035328872210235392) }, { argument := 150727126035328872210235392, coefficient := (-150727126035328872210235392) }, { argument := 4823268033130523910727532544, coefficient := (-4823268033130523910727532544) }, { argument := 150727126035328872210235392, coefficient := (-150727126035328872210235392) }, { argument := 400622271703174808780931072, coefficient := (-400622271703174808780931072) }, { argument := 181645510863088640868745216, coefficient := (-181645510863088640868745216) }, { argument := 385739532275140790539255808, coefficient := (-385739532275140790539255808) }, { argument := 48019962105109438460984295424, coefficient := (-48019962105109438460984295424) }, { argument := 2929100066014172244527284224, coefficient := (-2929100066014172244527284224) }, { argument := 477124959941167830341641043968, coefficient := (-477124959941167830341641043968) }, { argument := 1545019815040442502607798272, coefficient := (-1545019815040442502607798272) }, { argument := 112657694846698932481818624, coefficient := (-112657694846698932481818624) }, { argument := 2929100066014172244527284224, coefficient := (-2929100066014172244527284224) }, { argument := 2929100066014172244527284224, coefficient := (-2929100066014172244527284224) }, { argument := 1545019815040442502607798272, coefficient := (-1545019815040442502607798272) }, { argument := 36147026089383686050594947072, coefficient := (-36147026089383686050594947072) }, { argument := 2896912153200829692389621760, coefficient := (-2896912153200829692389621760) }, { argument := 48019962105109438460984295424, coefficient := (-48019962105109438460984295424) }, { argument := 2929100066014172244527284224, coefficient := (-2929100066014172244527284224) }, { argument := 112657694846698932481818624, coefficient := (-112657694846698932481818624) }, { argument := 2896912153200829692389621760, coefficient := (-2896912153200829692389621760) }, { argument := 112657694846698932481818624, coefficient := (-112657694846698932481818624) }, { argument := 2929100066014172244527284224, coefficient := (-2929100066014172244527284224) }, { argument := 2929100066014172244527284224, coefficient := (-2929100066014172244527284224) }, { argument := 401818392651889917724459008, coefficient := (-401818392651889917724459008) }, { argument := 4169718672014563715680567296, coefficient := (-4169718672014563715680567296) }, { argument := 13997094255225628413394944, coefficient := (-13997094255225628413394944) }, { argument := 153932929441146072262772785152, coefficient := (-153932929441146072262772785152) }, { argument := 110135031113485865673818112, coefficient := (-110135031113485865673818112) }, { argument := 13260405083897963760058368, coefficient := (-13260405083897963760058368) }, { argument := 153931240537715490759200735232, coefficient := (-153931240537715490759200735232) }, { argument := 13260405083897963760058368, coefficient := (-13260405083897963760058368) }, { argument := 13260405083897963760058368, coefficient := (-13260405083897963760058368) }, { argument := 567987351093629447722500096, coefficient := (-567987351093629447722500096) }, { argument := 13260405083897963760058368, coefficient := (-13260405083897963760058368) }, { argument := 110135031113485865673818112, coefficient := (-110135031113485865673818112) }, { argument := 567987351093629447722500096, coefficient := (-567987351093629447722500096) }, { argument := 4171407575445145219252617216, coefficient := (-4171407575445145219252617216) }, { argument := 13260405083897963760058368, coefficient := (-13260405083897963760058368) }, { argument := 13260405083897963760058368, coefficient := (-13260405083897963760058368) }, { argument := 13997094255225628413394944, coefficient := (-13997094255225628413394944) }, { argument := 180655617070919220482539520, coefficient := (-180655617070919220482539520) }] }

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

end TermShard8


end Parent1

namespace Parent1

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 17858289069922089192020171852611584
def positiveArguments : Array ℕ := #[
    1175, 1, 1, 1, 1, 1,
    4619, 55279, 82695, 23989, 4619, 95807,
    48127, 4619, 55279, 4619, 8235
  ]
def positiveCoefficients : Array ℕ := #[
    186186181908521193344828283289600, 158456325028528675187087900672, 316912650057057350374175801344, 316912650057057350374175801344, 316912650057057350374175801344, 316912650057057350374175801344,
    89344453772799554527485231104, 2138502732239266756754646499328, 1599553930448508153637235589120, 1856058975151061713409693188096, 89344453772799554527485231104, 1853176895997100437457193664512,
    1861823133458984265314692235264, 89344453772799554527485231104, 2138502732239266756754646499328, 89344453772799554527485231104, 637152263969694160237142999040
  ]
def positiveScales : Array ℕ := #[
    10, 0, 0, 0, 0, 0,
    12, 15, 16, 14, 12, 16,
    15, 12, 15, 12, 13
  ]
def negativeArguments : Array ℕ := #[
    5785712455, 60303513325, 5785712455, 78346885, 1537442577, 28557,
    56862753519, 449397, 13527, 113716909113, 13527, 13527,
    1158813, 13527, 449397, 1158813, 3083483079, 13527,
    13527, 28557, 13799631043, 50096025745, 3449907627, 128767221,
    171, 4751608587, 2691, 81, 9502498749, 81,
    81, 6939, 81, 2691, 6939, 258252867,
    81, 81, 171, 13661260605, 49601014639, 3415315029,
    1, 1, 1, 1, 149
  ]
def negativeCoefficients : Array ℕ := #[
    26681889235364697709289144320, 278100869262952182013807820800, 26681889235364697709289144320, 180655617070919220482539520, 14180404872971745493008777216, 269713239302616916735033344,
    524466330745710100768308068352, 2122217330302169950099341312, 255517805655110763222663168, 524426679815200113469163569152, 255517805655110763222663168, 255517805655110763222663168,
    10944679342227244358037405696, 255517805655110763222663168, 2122217330302169950099341312, 10944679342227244358037405696, 14220055803481732792153276416, 255517805655110763222663168,
    255517805655110763222663168, 269713239302616916735033344, 31819782770229826080720551936, 115513570753497484425942794240, 31819781536603816151394287616, 593833992717449530687094784,
    12920394697131349304672256, 21912926885707416600626331648, 101663105643217722160447488, 12240373923598120393900032, 21911270310443522252548866048, 12240373923598120393900032,
    12240373923598120393900032, 524296016394119490205384704, 12240373923598120393900032, 101663105643217722160447488, 524296016394119490205384704, 595490567981343878764560384,
    12240373923598120393900032, 12240373923598120393900032, 12920394697131349304672256, 31500722263085689212984360960, 114372152855244245592417763328, 31500721135528457707488018432,
    39614081257132168796771975168, 39614081257132168796771975168, 158456325028528675187087900672, 1267650600228229401496703205376, 11804996214625386301438048600064
  ]
def negativeScales : Array ℕ := #[
    32, 35, 32, 26, 30, 14,
    35, 18, 13, 36, 13, 13,
    20, 13, 18, 20, 31, 13,
    13, 14, 33, 35, 31, 26,
    7, 32, 11, 6, 33, 6,
    6, 12, 6, 11, 12, 27,
    6, 6, 7, 33, 35, 31,
    0, 0, 0, 0, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10198445041452361, 0, 0, 0, 0, 0,
    12173364830849036, 15754443897067599, 16335512481699629, 14550085398576695, 12173364830849036, 16547843447790030,
    15554558875155990, 12173364830849036, 15754443897067599, 12173364830849036, 13007552934613717
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    32429847478316023, 35811523006688579, 32429847478316023, 26223372579823372, 30517885381235758, 14801556808026795,
    35726764910703915, 18777630968521050, 13723554295483443, 36726655835325515, 13723554295483443, 13723554295483443,
    20144216343831399, 13723554295483443, 18777630968521050, 20144216343831399, 31521913783354549, 13723554295483443,
    13723554295483443, 14801556808026795, 33683910643495253, 35543977103883911, 31683910587563188, 26940190155480371,
    7417852514885912, 32145768853245414, 11393926675640423, 6339850002884626, 33145659784143314, 6339850002884626,
    6339850002884626, 12760512051639823, 6339850002884626, 11393926675640423, 12760512051639823, 27944209133839362,
    6339850002884626, 6339850002884626, 7417852514885912, 33669371564649698, 35529650581576838, 31669371513008937,
    0, 0, 0, 0, 7219168520462162
  ]

abbrev PositiveTerm := Fin 17
abbrev NegativeTerm := Fin 47
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
noncomputable def positiveFloor : ℝ := 25176610107 / 1000000000000
noncomputable def negativeCeiling : ℝ := 903578121 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 26681889235364697709289144320, coefficient := (-26681889235364697709289144320) }, { argument := 278100869262952182013807820800, coefficient := (-278100869262952182013807820800) }, { argument := 26681889235364697709289144320, coefficient := (-26681889235364697709289144320) }, { argument := 180655617070919220482539520, coefficient := (-180655617070919220482539520) }, { argument := 14180404872971745493008777216, coefficient := (-14180404872971745493008777216) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 524466330745710100768308068352, coefficient := (-524466330745710100768308068352) }, { argument := 2122217330302169950099341312, coefficient := (-2122217330302169950099341312) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 524426679815200113469163569152, coefficient := (-524426679815200113469163569152) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 10944679342227244358037405696, coefficient := (-10944679342227244358037405696) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 2122217330302169950099341312, coefficient := (-2122217330302169950099341312) }, { argument := 10944679342227244358037405696, coefficient := (-10944679342227244358037405696) }, { argument := 14220055803481732792153276416, coefficient := (-14220055803481732792153276416) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 31819782770229826080720551936, coefficient := (-31819782770229826080720551936) }, { argument := 115513570753497484425942794240, coefficient := (-115513570753497484425942794240) }, { argument := 31819781536603816151394287616, coefficient := (-31819781536603816151394287616) }, { argument := 593833992717449530687094784, coefficient := (-593833992717449530687094784) }, { argument := 12920394697131349304672256, coefficient := (-12920394697131349304672256) }, { argument := 21912926885707416600626331648, coefficient := (-21912926885707416600626331648) }, { argument := 101663105643217722160447488, coefficient := (-101663105643217722160447488) }, { argument := 12240373923598120393900032, coefficient := (-12240373923598120393900032) }, { argument := 21911270310443522252548866048, coefficient := (-21911270310443522252548866048) }, { argument := 12240373923598120393900032, coefficient := (-12240373923598120393900032) }, { argument := 12240373923598120393900032, coefficient := (-12240373923598120393900032) }, { argument := 524296016394119490205384704, coefficient := (-524296016394119490205384704) }, { argument := 12240373923598120393900032, coefficient := (-12240373923598120393900032) }, { argument := 101663105643217722160447488, coefficient := (-101663105643217722160447488) }, { argument := 524296016394119490205384704, coefficient := (-524296016394119490205384704) }, { argument := 595490567981343878764560384, coefficient := (-595490567981343878764560384) }, { argument := 12240373923598120393900032, coefficient := (-12240373923598120393900032) }, { argument := 12240373923598120393900032, coefficient := (-12240373923598120393900032) }, { argument := 12920394697131349304672256, coefficient := (-12920394697131349304672256) }, { argument := 31500722263085689212984360960, coefficient := (-31500722263085689212984360960) }, { argument := 114372152855244245592417763328, coefficient := (-114372152855244245592417763328) }, { argument := 31500721135528457707488018432, coefficient := (-31500721135528457707488018432) }, { argument := 39614081257132168796771975168, coefficient := (-39614081257132168796771975168) }, { argument := 39614081257132168796771975168, coefficient := (-39614081257132168796771975168) }, { argument := 186186181908521193344828283289600, coefficient := 186186181908521193344828283289600 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 89344453772799554527485231104, coefficient := 89344453772799554527485231104 }, { argument := 2138502732239266756754646499328, coefficient := 2138502732239266756754646499328 }, { argument := 1599553930448508153637235589120, coefficient := 1599553930448508153637235589120 }, { argument := 1856058975151061713409693188096, coefficient := 1856058975151061713409693188096 }, { argument := 89344453772799554527485231104, coefficient := 89344453772799554527485231104 }, { argument := 1853176895997100437457193664512, coefficient := 1853176895997100437457193664512 }, { argument := 1861823133458984265314692235264, coefficient := 1861823133458984265314692235264 }, { argument := 89344453772799554527485231104, coefficient := 89344453772799554527485231104 }, { argument := 2138502732239266756754646499328, coefficient := 2138502732239266756754646499328 }, { argument := 89344453772799554527485231104, coefficient := 89344453772799554527485231104 }, { argument := 11804996214625386301438048600064, coefficient := (-11804996214625386301438048600064) }, { argument := 637152263969694160237142999040, coefficient := 637152263969694160237142999040 }] }

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

end TermShard9


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12
