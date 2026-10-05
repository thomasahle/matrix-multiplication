import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 7, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7

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
def constantNumerator : ℤ := (-1099748322059652785262804615561216)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3, 2043286079, 1918989249, 2043286079, 1918989249, 2143440678063,
    6746988339, 11936190373585, 2283466437, 635437521, 18261439605, 6779673135,
    2147950260399, 6746988339, 617821965, 959404374551, 57087309440489, 32703755,
    32947495, 976203347, 643156787, 28543657204455, 976203347, 32703755,
    32359691, 14826903, 32359691, 643156787, 14826903, 479699703065,
    32947495, 3, 3494243777, 3280899135, 3494243777, 3280899135,
    77767138315857, 61872684651, 434542272814255, 168982876539, 11686378869, 337855652829,
    3898382607, 77936574909009, 61872684651, 11355448023, 115025942327479, 7313422249930569,
    3390910215, 3109545939, 130454758639, 45577418575, 3656711625529987, 130454758639,
    3390910215, 3381735175, 1474874115, 3381735175, 45577418575, 1474874115,
    57512470599037, 3109545939, 48195, 37485
  ]
def negativeCoefficients : Array ℕ := #[
    118842243771396506390315925504, 75383950737372953412609507328, 70798207113006186199429152768, 75383950737372953412609507328, 70798207113006186199429152768, 9653198639015290079960629248,
    15557495894729462653258825728, 107511645037401414882893496320, 21061260482122207600727556096, 732609582794964922055786496, 21054006425683665321700884480, 15632861903093638360486379520,
    9673507992343296250849787904, 15557495894729462653258825728, 712300229466958751166627840, 540096647965688421953830912, 32137298190471307362008301568, 150819449683574779302379520,
    151943502033706270830100480, 4501943326501919748352114688, 2966037162264581597139304448, 32137300987443677889476689920, 4501943326501919748352114688, 150819449683574779302379520,
    149232734545330578510577664, 136754042523358185991962624, 149232734545330578510577664, 2966037162264581597139304448, 136754042523358185991962624, 540093850993317894485442560,
    151943502033706270830100480, 118842243771396506390315925504, 257829682741884920158673174528, 242087626700000176552689008640, 257829682741884920158673174528, 242087626700000176552689008640,
    350232055140963407062810755072, 570674789455167093451687723008, 3914008835846014464382950440960, 779295969088547769117893984256, 26946955018106285306085900288, 779042095199078432119568990208,
    575299730021837135916665143296, 350995129718745680597131198464, 570674789455167093451687723008, 26183880440324011771765456896, 64753848875496823472361832448, 4117090714948800626776004886528,
    15637813228258107879441039360, 14340249530543963223260921856, 601616386452795795363548102656, 210188743998340221744499916800, 4117091278534552540231801765888, 601616386452795795363548102656,
    15637813228258107879441039360, 15595500824571595858326323200, 13603312670171934853347409920, 15595500824571595858326323200, 210188743998340221744499916800, 13603312670171934853347409920,
    64753285289744910016564953088, 14340249530543963223260921856, 1820755621135220408592629760, 1416143260882949206683156480
  ]
def negativeScales : Array ℕ := #[
    1, 30, 30, 30, 30, 40,
    32, 43, 31, 29, 34, 32,
    40, 32, 29, 39, 45, 24,
    24, 29, 29, 44, 29, 24,
    24, 23, 24, 29, 23, 38,
    24, 1, 31, 31, 31, 31,
    46, 35, 48, 37, 33, 38,
    31, 46, 35, 33, 46, 52,
    31, 31, 36, 35, 51, 36,
    31, 31, 30, 31, 35, 30,
    45, 31, 15, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 30928244070068921, 30837699484313517, 30928244070068921, 30837699484313517, 40963065641254351,
    32651596522399151, 43440407684365254, 31088578438741062, 29243175039207650, 34088081450730675, 32658568573114447,
    40966097737839378, 32651596522399151, 29202615922122173, 39803348062195668, 45698235302448406, 24962952970649516,
    24973665460885164, 29862606459446343, 29260595235772551, 44698235428008993, 29862606459446343, 24962952970649516,
    24947694505895662, 23821713948563613, 24947694505895662, 29260595235772551, 23821713948563613, 38803340590961235,
    24973665460885164, 1584962500724866, 31702333115895135, 31611444095618663, 31702333115895135, 31611444095618663,
    46144225884838232, 35848583584295367, 48626489859474232, 37298086105748439, 33444108915780560, 38297616037522574,
    31860228547027016, 46147365764088528, 35848583584295367, 33402665576786264, 46708952603998122, 52699468083684048,
    31659025438998862, 31534056785025287, 36924758621277146, 35407600164075565, 51699468281173580, 36924758621277146,
    31659025438998862, 31655116540170739, 30457944675297656, 31655116540170739, 35407600164075565, 30457944675297656,
    45708940047433168, 31534056785025287, 15556595861081553, 15194025781695223
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
noncomputable def negativeCeiling : ℝ := 2153107047 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 118842243771396506390315925504, coefficient := (-118842243771396506390315925504) }, { argument := 75383950737372953412609507328, coefficient := (-75383950737372953412609507328) }, { argument := 70798207113006186199429152768, coefficient := (-70798207113006186199429152768) }, { argument := 75383950737372953412609507328, coefficient := (-75383950737372953412609507328) }, { argument := 70798207113006186199429152768, coefficient := (-70798207113006186199429152768) }, { argument := 9653198639015290079960629248, coefficient := (-9653198639015290079960629248) }, { argument := 15557495894729462653258825728, coefficient := (-15557495894729462653258825728) }, { argument := 107511645037401414882893496320, coefficient := (-107511645037401414882893496320) }, { argument := 21061260482122207600727556096, coefficient := (-21061260482122207600727556096) }, { argument := 732609582794964922055786496, coefficient := (-732609582794964922055786496) }, { argument := 21054006425683665321700884480, coefficient := (-21054006425683665321700884480) }, { argument := 15632861903093638360486379520, coefficient := (-15632861903093638360486379520) }, { argument := 9673507992343296250849787904, coefficient := (-9673507992343296250849787904) }, { argument := 15557495894729462653258825728, coefficient := (-15557495894729462653258825728) }, { argument := 712300229466958751166627840, coefficient := (-712300229466958751166627840) }, { argument := 540096647965688421953830912, coefficient := (-540096647965688421953830912) }, { argument := 32137298190471307362008301568, coefficient := (-32137298190471307362008301568) }, { argument := 150819449683574779302379520, coefficient := (-150819449683574779302379520) }, { argument := 151943502033706270830100480, coefficient := (-151943502033706270830100480) }, { argument := 4501943326501919748352114688, coefficient := (-4501943326501919748352114688) }, { argument := 2966037162264581597139304448, coefficient := (-2966037162264581597139304448) }, { argument := 32137300987443677889476689920, coefficient := (-32137300987443677889476689920) }, { argument := 4501943326501919748352114688, coefficient := (-4501943326501919748352114688) }, { argument := 150819449683574779302379520, coefficient := (-150819449683574779302379520) }, { argument := 149232734545330578510577664, coefficient := (-149232734545330578510577664) }, { argument := 136754042523358185991962624, coefficient := (-136754042523358185991962624) }, { argument := 149232734545330578510577664, coefficient := (-149232734545330578510577664) }, { argument := 2966037162264581597139304448, coefficient := (-2966037162264581597139304448) }, { argument := 136754042523358185991962624, coefficient := (-136754042523358185991962624) }, { argument := 540093850993317894485442560, coefficient := (-540093850993317894485442560) }, { argument := 151943502033706270830100480, coefficient := (-151943502033706270830100480) }, { argument := 118842243771396506390315925504, coefficient := (-118842243771396506390315925504) }, { argument := 257829682741884920158673174528, coefficient := (-257829682741884920158673174528) }, { argument := 242087626700000176552689008640, coefficient := (-242087626700000176552689008640) }, { argument := 257829682741884920158673174528, coefficient := (-257829682741884920158673174528) }, { argument := 242087626700000176552689008640, coefficient := (-242087626700000176552689008640) }, { argument := 350232055140963407062810755072, coefficient := (-350232055140963407062810755072) }, { argument := 570674789455167093451687723008, coefficient := (-570674789455167093451687723008) }, { argument := 3914008835846014464382950440960, coefficient := (-3914008835846014464382950440960) }, { argument := 779295969088547769117893984256, coefficient := (-779295969088547769117893984256) }, { argument := 26946955018106285306085900288, coefficient := (-26946955018106285306085900288) }, { argument := 779042095199078432119568990208, coefficient := (-779042095199078432119568990208) }, { argument := 575299730021837135916665143296, coefficient := (-575299730021837135916665143296) }, { argument := 350995129718745680597131198464, coefficient := (-350995129718745680597131198464) }, { argument := 570674789455167093451687723008, coefficient := (-570674789455167093451687723008) }, { argument := 26183880440324011771765456896, coefficient := (-26183880440324011771765456896) }, { argument := 64753848875496823472361832448, coefficient := (-64753848875496823472361832448) }, { argument := 4117090714948800626776004886528, coefficient := (-4117090714948800626776004886528) }, { argument := 15637813228258107879441039360, coefficient := (-15637813228258107879441039360) }, { argument := 14340249530543963223260921856, coefficient := (-14340249530543963223260921856) }, { argument := 601616386452795795363548102656, coefficient := (-601616386452795795363548102656) }, { argument := 210188743998340221744499916800, coefficient := (-210188743998340221744499916800) }, { argument := 4117091278534552540231801765888, coefficient := (-4117091278534552540231801765888) }, { argument := 601616386452795795363548102656, coefficient := (-601616386452795795363548102656) }, { argument := 15637813228258107879441039360, coefficient := (-15637813228258107879441039360) }, { argument := 15595500824571595858326323200, coefficient := (-15595500824571595858326323200) }, { argument := 13603312670171934853347409920, coefficient := (-13603312670171934853347409920) }, { argument := 15595500824571595858326323200, coefficient := (-15595500824571595858326323200) }, { argument := 210188743998340221744499916800, coefficient := (-210188743998340221744499916800) }, { argument := 13603312670171934853347409920, coefficient := (-13603312670171934853347409920) }, { argument := 64753285289744910016564953088, coefficient := (-64753285289744910016564953088) }, { argument := 14340249530543963223260921856, coefficient := (-14340249530543963223260921856) }, { argument := 1820755621135220408592629760, coefficient := (-1820755621135220408592629760) }, { argument := 1416143260882949206683156480, coefficient := (-1416143260882949206683156480) }] }

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
def constantNumerator : ℤ := (-5817114527971768895863865464586240)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    5355, 50337, 594405, 41769, 37485, 594405,
    5355, 41769, 41769, 41769, 41769, 41769,
    48195, 50337, 240812418357, 115357549839927, 392445, 1167098151137325,
    402705, 12825, 392445, 223155, 402705, 6286815,
    7695, 28839393584637, 392445, 12825, 7695, 12825,
    197505, 223155, 240808027957, 2043286079, 1918989249, 2043286079,
    1918989249, 622134761455833, 247478239143, 3476296156827431, 337945589451, 5842877409,
    84458872287, 249483031101, 623490151682265, 247478239143, 11354849001, 1164226396651405,
    77153649332717683, 120742117685, 106956289561, 5004357885421, 1363574614285, 38576829767167889,
    5004357885421, 120742117685, 120740970805, 51749325225, 120740970805, 1363574614285,
    51749325225, 582108097516655, 106956289561, 49455
  ]
def negativeCoefficients : Array ℕ := #[
    1618449441009084807637893120, 1901678093185674648974524416, 22455985994001051705975767040, 50495622559483445998302265344, 1416143260882949206683156480, 22455985994001051705975767040,
    1618449441009084807637893120, 1577988204983857687446945792, 1577988204983857687446945792, 1577988204983857687446945792, 50495622559483445998302265344, 1577988204983857687446945792,
    1820755621135220408592629760, 1901678093185674648974524416, 542261358789386595295297536, 64940527309183582211590324224, 1853269114369777915888926720, 657017849820856461547693670400,
    1901720594484020475781447680, 60564350142803199865651200, 1853269114369777915888926720, 1053819692484775677662330880, 1901720594484020475781447680, 29688644440002128574142218240,
    1162835522741821437420503040, 64940541100681133047966334976, 1853269114369777915888926720, 60564350142803199865651200, 1162835522741821437420503040, 60564350142803199865651200,
    1865381984398338555862056960, 1053819692484775677662330880, 542251472487484591582478336, 75383950737372953412609507328, 70798207113006186199429152768, 75383950737372953412609507328,
    70798207113006186199429152768, 350230734983340239544328912896, 570645967660401304243468763136, 3913961519129376393972043218944, 779249474930189426629753700352, 26945516054470542491161460736,
    778995600916204567133889232896, 575268703181683437781911601152, 350993751848177835469103431680, 570645967660401304243468763136, 26182499189632946566386941952, 655401195766770353759961743360,
    43433643298137659314784851460096, 139206183990807187232978370560, 123312206287833720628273217536, 5769631822850718442773488336896, 1572094495945163215869218652160, 43433649041138090717048509300736,
    5769631822850718442773488336896, 139206183990807187232978370560, 139204861728191983732318535680, 119325819801592119845663539200, 139204861728191983732318535680, 1572094495945163215869218652160,
    119325819801592119845663539200, 655395452766338951496303902720, 123312206287833720628273217536, 1868357075282546432346685440
  ]
def negativeScales : Array ℕ := #[
    12, 15, 19, 15, 15, 19,
    12, 15, 15, 15, 15, 15,
    15, 15, 37, 46, 18, 50,
    18, 13, 18, 17, 18, 22,
    12, 44, 18, 13, 12, 13,
    17, 17, 37, 30, 30, 30,
    30, 49, 37, 51, 38, 32,
    36, 37, 49, 37, 33, 50,
    56, 36, 36, 42, 40, 55,
    42, 36, 36, 35, 36, 40,
    35, 49, 36, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    12386670859637623, 15619331616437464, 19181086725987725, 15350144983612506, 15194025781695223, 19181086725987725,
    12386670859637623, 15350144983612506, 15350144983612506, 15350144983612506, 15350144983612506, 15350144983612506,
    15556595861081553, 15619331616437464, 37809118836303946, 46713105756124206, 18582130953190490, 50051847317864393,
    18619363859395622, 13646671205401350, 18582130953190490, 17767686606672550, 18619363859395622, 22583897879364855,
    12909705616407956, 44713106062511048, 18582130953190490, 13646671205401350, 12909705616407956, 13646671205401350,
    17591529651193783, 17767686606672550, 37809092533399012, 30928244070068921, 30837699484313517, 30928244070068921,
    30837699484313517, 49144220446762483, 37848510719482443, 51626472418531211, 38298000029475243, 32444031874009772,
    36297529932967442, 37860150738060742, 49147360100616962, 37848510719482443, 33402589469805535, 50048293056785704,
    56098583915430611, 36813138054385503, 36638230366407442, 42186322105821828, 40310530784786183, 55098584106190516,
    42186322105821828, 36813138054385503, 36813124350749967, 35590820999878504, 36813124350749967, 40310530784786183,
    35590820999878504, 49048280415010564, 36638230366407442, 15593828767283669
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
noncomputable def negativeCeiling : ℝ := 71730234397 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1618449441009084807637893120, coefficient := (-1618449441009084807637893120) }, { argument := 1901678093185674648974524416, coefficient := (-1901678093185674648974524416) }, { argument := 22455985994001051705975767040, coefficient := (-22455985994001051705975767040) }, { argument := 50495622559483445998302265344, coefficient := (-50495622559483445998302265344) }, { argument := 1416143260882949206683156480, coefficient := (-1416143260882949206683156480) }, { argument := 22455985994001051705975767040, coefficient := (-22455985994001051705975767040) }, { argument := 1618449441009084807637893120, coefficient := (-1618449441009084807637893120) }, { argument := 1577988204983857687446945792, coefficient := (-1577988204983857687446945792) }, { argument := 1577988204983857687446945792, coefficient := (-1577988204983857687446945792) }, { argument := 1577988204983857687446945792, coefficient := (-1577988204983857687446945792) }, { argument := 50495622559483445998302265344, coefficient := (-50495622559483445998302265344) }, { argument := 1577988204983857687446945792, coefficient := (-1577988204983857687446945792) }, { argument := 1820755621135220408592629760, coefficient := (-1820755621135220408592629760) }, { argument := 1901678093185674648974524416, coefficient := (-1901678093185674648974524416) }, { argument := 542261358789386595295297536, coefficient := (-542261358789386595295297536) }, { argument := 64940527309183582211590324224, coefficient := (-64940527309183582211590324224) }, { argument := 1853269114369777915888926720, coefficient := (-1853269114369777915888926720) }, { argument := 657017849820856461547693670400, coefficient := (-657017849820856461547693670400) }, { argument := 1901720594484020475781447680, coefficient := (-1901720594484020475781447680) }, { argument := 60564350142803199865651200, coefficient := (-60564350142803199865651200) }, { argument := 1853269114369777915888926720, coefficient := (-1853269114369777915888926720) }, { argument := 1053819692484775677662330880, coefficient := (-1053819692484775677662330880) }, { argument := 1901720594484020475781447680, coefficient := (-1901720594484020475781447680) }, { argument := 29688644440002128574142218240, coefficient := (-29688644440002128574142218240) }, { argument := 1162835522741821437420503040, coefficient := (-1162835522741821437420503040) }, { argument := 64940541100681133047966334976, coefficient := (-64940541100681133047966334976) }, { argument := 1853269114369777915888926720, coefficient := (-1853269114369777915888926720) }, { argument := 60564350142803199865651200, coefficient := (-60564350142803199865651200) }, { argument := 1162835522741821437420503040, coefficient := (-1162835522741821437420503040) }, { argument := 60564350142803199865651200, coefficient := (-60564350142803199865651200) }, { argument := 1865381984398338555862056960, coefficient := (-1865381984398338555862056960) }, { argument := 1053819692484775677662330880, coefficient := (-1053819692484775677662330880) }, { argument := 542251472487484591582478336, coefficient := (-542251472487484591582478336) }, { argument := 75383950737372953412609507328, coefficient := (-75383950737372953412609507328) }, { argument := 70798207113006186199429152768, coefficient := (-70798207113006186199429152768) }, { argument := 75383950737372953412609507328, coefficient := (-75383950737372953412609507328) }, { argument := 70798207113006186199429152768, coefficient := (-70798207113006186199429152768) }, { argument := 350230734983340239544328912896, coefficient := (-350230734983340239544328912896) }, { argument := 570645967660401304243468763136, coefficient := (-570645967660401304243468763136) }, { argument := 3913961519129376393972043218944, coefficient := (-3913961519129376393972043218944) }, { argument := 779249474930189426629753700352, coefficient := (-779249474930189426629753700352) }, { argument := 26945516054470542491161460736, coefficient := (-26945516054470542491161460736) }, { argument := 778995600916204567133889232896, coefficient := (-778995600916204567133889232896) }, { argument := 575268703181683437781911601152, coefficient := (-575268703181683437781911601152) }, { argument := 350993751848177835469103431680, coefficient := (-350993751848177835469103431680) }, { argument := 570645967660401304243468763136, coefficient := (-570645967660401304243468763136) }, { argument := 26182499189632946566386941952, coefficient := (-26182499189632946566386941952) }, { argument := 655401195766770353759961743360, coefficient := (-655401195766770353759961743360) }, { argument := 43433643298137659314784851460096, coefficient := (-43433643298137659314784851460096) }, { argument := 139206183990807187232978370560, coefficient := (-139206183990807187232978370560) }, { argument := 123312206287833720628273217536, coefficient := (-123312206287833720628273217536) }, { argument := 5769631822850718442773488336896, coefficient := (-5769631822850718442773488336896) }, { argument := 1572094495945163215869218652160, coefficient := (-1572094495945163215869218652160) }, { argument := 43433649041138090717048509300736, coefficient := (-43433649041138090717048509300736) }, { argument := 5769631822850718442773488336896, coefficient := (-5769631822850718442773488336896) }, { argument := 139206183990807187232978370560, coefficient := (-139206183990807187232978370560) }, { argument := 139204861728191983732318535680, coefficient := (-139204861728191983732318535680) }, { argument := 119325819801592119845663539200, coefficient := (-119325819801592119845663539200) }, { argument := 139204861728191983732318535680, coefficient := (-139204861728191983732318535680) }, { argument := 1572094495945163215869218652160, coefficient := (-1572094495945163215869218652160) }, { argument := 119325819801592119845663539200, coefficient := (-119325819801592119845663539200) }, { argument := 655395452766338951496303902720, coefficient := (-655395452766338951496303902720) }, { argument := 123312206287833720628273217536, coefficient := (-123312206287833720628273217536) }, { argument := 1868357075282546432346685440, coefficient := (-1868357075282546432346685440) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7
