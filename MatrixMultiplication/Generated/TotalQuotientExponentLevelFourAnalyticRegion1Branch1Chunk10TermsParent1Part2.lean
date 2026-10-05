import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 10, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-5843524457983805102087278468005888)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    8688467445, 13375, 2848889358965, 10247370304145, 1424445154685, 7098218960667,
    1296305, 7098217269477, 1296305, 36651, 454679462805, 82925,
    454679354475, 82925, 66291, 1352021502813703, 13131711, 340743,
    9844242577237215, 21152277, 2704234786787091, 21152277, 22043451, 13131711,
    655275, 227728932519749, 24075, 227729001758907, 24075, 467197557,
    443109191217, 42265, 443109085647, 42265, 36651, 1083,
    162507425, 3169332275, 6338662225, 20313525, 68718902525, 247179848825,
    34359462725, 14482368189, 1605, 14482364739, 1605, 17670574935,
    63560532555, 8835290415, 454679462805, 82925, 454679354475, 82925,
    1083, 14482368189, 1605, 14482364739, 1605, 2109,
    68718902525, 247179848825, 34359462725, 443109191217
  ]
def negativeCoefficients : Array ℕ := #[
    641095741402688478404652564480, 505293213667052037865472000, 3284545806196363575806488739840, 11814413589318376515102593515520, 3284546901938726161676888965120, 16367378568322094388869263785984,
    12243254567152670877480386560, 16367374668703455636762189103104, 12243254567152670877480386560, 708933443435132382114496905216, 1048419460741947031545037455360, 783204481183930658691481600,
    1048419210949973843425571635200, 783204481183930658691481600, 1282254424129174121927153811456, 3044481768134345419997623353344, 3875796993070664476174319616, 201139165309056439881302016,
    11083631800647573165603721052160, 6243050246323405653238874112, 3044697694524168931895131766784, 6243050246323405653238874112, 6506078385573710228468269056, 3875796993070664476174319616,
    193403043566400422962790400, 8204799485099379400931679404032, 454763892300346834078924800, 8204801979702948746906856062976, 454763892300346834078924800, 2206278084055380593295514140672,
    1021740230886053406191684419584, 798363277593942219827445760, 1021739987458206923502013906944, 798363277593942219827445760, 708933443435132382114496905216, 41896533204564588678617235456,
    187358304940784339438796800, 7307982670184082614045900800, 7307979989641584403126681600, 187359198454950409745203200, 79227500494054255791335014400, 284978963215811976587588403200,
    79227526924779748903301939200, 33394067445464435193626492928, 30317592820023122271928320, 33394059490306053406382358528, 30317592820023122271928320, 81491143365312948813944586240,
    293121219307692318775805214720, 81491170551202027443396280320, 1048419460741947031545037455360, 783204481183930658691481600, 1048419210949973843425571635200, 783204481183930658691481600,
    41896533204564588678617235456, 33394067445464435193626492928, 30317592820023122271928320, 33394059490306053406382358528, 30317592820023122271928320, 40793992857076046871285202944,
    79227500494054255791335014400, 284978963215811976587588403200, 79227526924779748903301939200, 1021740230886053406191684419584
  ]
def negativeScales : Array ℕ := #[
    33, 13, 41, 43, 40, 42,
    20, 42, 20, 15, 38, 16,
    38, 16, 16, 50, 23, 18,
    53, 24, 51, 24, 24, 23,
    19, 47, 14, 47, 14, 28,
    38, 15, 38, 15, 15, 10,
    27, 31, 32, 24, 35, 37,
    34, 33, 10, 33, 10, 34,
    35, 33, 38, 16, 38, 16,
    10, 33, 10, 33, 10, 11,
    35, 37, 34, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33016454577114956, 13707251271149006, 41373536732099500, 43220318964152373, 40373537213390339, 42690594216993010,
    20305973770739856, 42690593873262881, 20305973770739856, 15161564941492690, 38726058885058147, 16339519486562748,
    38726058541327705, 16339519486562748, 16016525395637961, 50264039520016334, 23646551569067652, 18378324493994027,
    53128201631763283, 24334309639130713, 51264141837884887, 24334309639130713, 24393846766108081, 23646551569067652,
    19321740965627657, 47694310923215639, 14555248177619742, 47694311361855446, 14555248177619742, 28799457490049077,
    38688871296132785, 15367175829465614, 38688870952413140, 15367175829465614, 15161564941492690, 10080817527608328,
    27275930395799732, 31561531774789074, 32561531245613479, 24275937276014532, 35999987968649564, 37846770178658948,
    34999988449940585, 33753578483524610, 10648357582030099, 33753578139844733, 10648357582030099, 34040629929475065,
    35887412165007083, 33040630410765905, 38726058885058147, 16339519486562748, 38726058541327705, 16339519486562748,
    10080817527608328, 33753578483524610, 10648357582030099, 33753578139844733, 10648357582030099, 11042343379793692,
    35999987968649564, 37846770178658948, 34999988449940585, 38688871296132785
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
noncomputable def negativeCeiling : ℝ := 5201543047 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 641095741402688478404652564480, coefficient := (-641095741402688478404652564480) }, { argument := 505293213667052037865472000, coefficient := (-505293213667052037865472000) }, { argument := 3284545806196363575806488739840, coefficient := (-3284545806196363575806488739840) }, { argument := 11814413589318376515102593515520, coefficient := (-11814413589318376515102593515520) }, { argument := 3284546901938726161676888965120, coefficient := (-3284546901938726161676888965120) }, { argument := 16367378568322094388869263785984, coefficient := (-16367378568322094388869263785984) }, { argument := 12243254567152670877480386560, coefficient := (-12243254567152670877480386560) }, { argument := 16367374668703455636762189103104, coefficient := (-16367374668703455636762189103104) }, { argument := 12243254567152670877480386560, coefficient := (-12243254567152670877480386560) }, { argument := 708933443435132382114496905216, coefficient := (-708933443435132382114496905216) }, { argument := 1048419460741947031545037455360, coefficient := (-1048419460741947031545037455360) }, { argument := 783204481183930658691481600, coefficient := (-783204481183930658691481600) }, { argument := 1048419210949973843425571635200, coefficient := (-1048419210949973843425571635200) }, { argument := 783204481183930658691481600, coefficient := (-783204481183930658691481600) }, { argument := 1282254424129174121927153811456, coefficient := (-1282254424129174121927153811456) }, { argument := 3044481768134345419997623353344, coefficient := (-3044481768134345419997623353344) }, { argument := 3875796993070664476174319616, coefficient := (-3875796993070664476174319616) }, { argument := 201139165309056439881302016, coefficient := (-201139165309056439881302016) }, { argument := 11083631800647573165603721052160, coefficient := (-11083631800647573165603721052160) }, { argument := 6243050246323405653238874112, coefficient := (-6243050246323405653238874112) }, { argument := 3044697694524168931895131766784, coefficient := (-3044697694524168931895131766784) }, { argument := 6243050246323405653238874112, coefficient := (-6243050246323405653238874112) }, { argument := 6506078385573710228468269056, coefficient := (-6506078385573710228468269056) }, { argument := 3875796993070664476174319616, coefficient := (-3875796993070664476174319616) }, { argument := 193403043566400422962790400, coefficient := (-193403043566400422962790400) }, { argument := 8204799485099379400931679404032, coefficient := (-8204799485099379400931679404032) }, { argument := 454763892300346834078924800, coefficient := (-454763892300346834078924800) }, { argument := 8204801979702948746906856062976, coefficient := (-8204801979702948746906856062976) }, { argument := 454763892300346834078924800, coefficient := (-454763892300346834078924800) }, { argument := 2206278084055380593295514140672, coefficient := (-2206278084055380593295514140672) }, { argument := 1021740230886053406191684419584, coefficient := (-1021740230886053406191684419584) }, { argument := 798363277593942219827445760, coefficient := (-798363277593942219827445760) }, { argument := 1021739987458206923502013906944, coefficient := (-1021739987458206923502013906944) }, { argument := 798363277593942219827445760, coefficient := (-798363277593942219827445760) }, { argument := 708933443435132382114496905216, coefficient := (-708933443435132382114496905216) }, { argument := 41896533204564588678617235456, coefficient := (-41896533204564588678617235456) }, { argument := 187358304940784339438796800, coefficient := (-187358304940784339438796800) }, { argument := 7307982670184082614045900800, coefficient := (-7307982670184082614045900800) }, { argument := 7307979989641584403126681600, coefficient := (-7307979989641584403126681600) }, { argument := 187359198454950409745203200, coefficient := (-187359198454950409745203200) }, { argument := 79227500494054255791335014400, coefficient := (-79227500494054255791335014400) }, { argument := 284978963215811976587588403200, coefficient := (-284978963215811976587588403200) }, { argument := 79227526924779748903301939200, coefficient := (-79227526924779748903301939200) }, { argument := 33394067445464435193626492928, coefficient := (-33394067445464435193626492928) }, { argument := 30317592820023122271928320, coefficient := (-30317592820023122271928320) }, { argument := 33394059490306053406382358528, coefficient := (-33394059490306053406382358528) }, { argument := 30317592820023122271928320, coefficient := (-30317592820023122271928320) }, { argument := 81491143365312948813944586240, coefficient := (-81491143365312948813944586240) }, { argument := 293121219307692318775805214720, coefficient := (-293121219307692318775805214720) }, { argument := 81491170551202027443396280320, coefficient := (-81491170551202027443396280320) }, { argument := 1048419460741947031545037455360, coefficient := (-1048419460741947031545037455360) }, { argument := 783204481183930658691481600, coefficient := (-783204481183930658691481600) }, { argument := 1048419210949973843425571635200, coefficient := (-1048419210949973843425571635200) }, { argument := 783204481183930658691481600, coefficient := (-783204481183930658691481600) }, { argument := 41896533204564588678617235456, coefficient := (-41896533204564588678617235456) }, { argument := 33394067445464435193626492928, coefficient := (-33394067445464435193626492928) }, { argument := 30317592820023122271928320, coefficient := (-30317592820023122271928320) }, { argument := 33394059490306053406382358528, coefficient := (-33394059490306053406382358528) }, { argument := 30317592820023122271928320, coefficient := (-30317592820023122271928320) }, { argument := 40793992857076046871285202944, coefficient := (-40793992857076046871285202944) }, { argument := 79227500494054255791335014400, coefficient := (-79227500494054255791335014400) }, { argument := 284978963215811976587588403200, coefficient := (-284978963215811976587588403200) }, { argument := 79227526924779748903301939200, coefficient := (-79227526924779748903301939200) }, { argument := 1021740230886053406191684419584, coefficient := (-1021740230886053406191684419584) }] }

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

end TermShard4


end Parent1

namespace Parent1

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 326054079100294046792031784874803200
def positiveArguments : Array ℕ := #[
    42007, 489, 535, 489, 535, 189,
    31563, 819, 33957, 50841, 1575, 50841,
    52983, 31563, 1575, 20243, 22855, 9795,
    257935, 22855, 9795, 22855, 22855, 947503,
    5877, 257935, 947503, 20243, 22855, 5877,
    22855, 4155, 120495, 106645, 6925, 4155,
    6925, 211905, 6925, 4155, 3394635, 217445,
    120495, 211905, 6925
  ]
def positiveCoefficients : Array ℕ := #[
    3328137422736702029292000721764352, 37834542450659434651604484096, 41393620063604902941939466240, 37834542450659434651604484096, 41393620063604902941939466240, 29246333428117108994491809792,
    610517210311944650260016529408, 31683527880460201410699460608, 656823904906463406167961894912, 983407961520437789939787104256, 30464930654288655202595635200, 983407961520437789939787104256,
    1024840267210270361015317168128, 610517210311944650260016529408, 30464930654288655202595635200, 783113131726686028274467864576, 884159987433355193213108879360, 757851417800018737039807610880,
    9978377001033580037690800209920, 884159987433355193213108879360, 757851417800018737039807610880, 884159987433355193213108879360, 884159987433355193213108879360, 36654746907594239581492028112896,
    909421701360022484447769133056, 9978377001033580037690800209920, 36654746907594239581492028112896, 783113131726686028274467864576, 884159987433355193213108879360, 909421701360022484447769133056,
    884159987433355193213108879360, 160738776975961095068933160960, 2330712266151435878499530833920, 4125628609049668106769284464640, 133948980813300912557444300800, 2571820431615377521102930575360,
    133948980813300912557444300800, 4098838812887007924257795604480, 4286367386025629201838217625600, 2571820431615377521102930575360, 65661790394680107335659196252160, 4205997997537648654303751045120,
    2330712266151435878499530833920, 4098838812887007924257795604480, 133948980813300912557444300800
  ]
def positiveScales : Array ℕ := #[
    15, 8, 9, 8, 9, 7,
    14, 9, 15, 15, 10, 15,
    15, 14, 10, 14, 14, 13,
    17, 14, 13, 14, 14, 19,
    12, 17, 19, 14, 14, 12,
    14, 12, 16, 16, 12, 12,
    12, 17, 12, 12, 21, 17,
    16, 17, 12
  ]
def negativeArguments : Array ℕ := #[
    42265, 443109085647, 42265, 2109, 14480240061, 42265,
    14480236611, 42265, 66291, 2109, 72450166330733, 1605,
    72450168744595, 1605, 13320587, 171, 1, 63,
    653
  ]
def negativeCoefficients : Array ℕ := #[
    798363277593942219827445760, 1021739987458206923502013906944, 798363277593942219827445760, 40793992857076046871285202944, 1068453130124573544753401954304, 798363277593942219827445760,
    1068452875559505327561589653504, 798363277593942219827445760, 1282254424129174121927153811456, 40793992857076046871285202944, 81571635522504898565365563392, 30317592820023122271928320,
    81571638240271899496315617280, 30317592820023122271928320, 62904693580949118728171159552, 52921936679450006751937560576, 158456325028528675187087900672, 4991374238398653268393268871168,
    103471980243629224897168399138816
  ]
def negativeScales : Array ℕ := #[
    15, 38, 15, 11, 33, 15,
    33, 15, 16, 11, 46, 10,
    46, 10, 23, 7, 0, 5,
    9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    15358342136579123, 8933690654464738, 9063395081288509, 8933690654464738, 9063395081288509, 7562242424220952,
    14945946716094235, 9677719641638369, 15051421386252421, 15633704786776826, 10621136113274016, 15633704786776826,
    15693241913751229, 14945946716094235, 10621136113274016, 14305135491933305, 14480222198491388, 13257829777154949,
    17976648023609385, 14480222198491388, 13257829777154949, 14480222198491388, 14480222198491388, 19853770985498009,
    12520864182988709, 17976648023609385, 19853770985498009, 14305135491933305, 14480222198491388, 12520864182988709,
    14480222198491388, 12020632761657706, 16878613756602126, 16702456801626690, 12757598355807462, 12020632761657706,
    12757598355807462, 17693058103625387, 12757598355807462, 12020632761657706, 21694825029799412, 17730291009819162,
    16878613756602126, 17693058103625387, 12757598355807462
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    15367175829465614, 38688870952413140, 15367175829465614, 11042343379793692, 33753366469488636, 15367175829465614,
    33753366125758250, 15367175829465614, 16016525395637961, 11042343379793692, 46042054235453847, 10648357582030099,
    46042054283520909, 10648357582030099, 23667154323480008, 7417852514885912, 0, 5977279939904027,
    9350939181546432
  ]

abbrev PositiveTerm := Fin 45
abbrev NegativeTerm := Fin 19
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
noncomputable def positiveFloor : ℝ := 662807023907 / 1000000000000
noncomputable def negativeCeiling : ℝ := 6860725013 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 798363277593942219827445760, coefficient := (-798363277593942219827445760) }, { argument := 1021739987458206923502013906944, coefficient := (-1021739987458206923502013906944) }, { argument := 798363277593942219827445760, coefficient := (-798363277593942219827445760) }, { argument := 40793992857076046871285202944, coefficient := (-40793992857076046871285202944) }, { argument := 1068453130124573544753401954304, coefficient := (-1068453130124573544753401954304) }, { argument := 798363277593942219827445760, coefficient := (-798363277593942219827445760) }, { argument := 1068452875559505327561589653504, coefficient := (-1068452875559505327561589653504) }, { argument := 798363277593942219827445760, coefficient := (-798363277593942219827445760) }, { argument := 1282254424129174121927153811456, coefficient := (-1282254424129174121927153811456) }, { argument := 40793992857076046871285202944, coefficient := (-40793992857076046871285202944) }, { argument := 81571635522504898565365563392, coefficient := (-81571635522504898565365563392) }, { argument := 30317592820023122271928320, coefficient := (-30317592820023122271928320) }, { argument := 81571638240271899496315617280, coefficient := (-81571638240271899496315617280) }, { argument := 30317592820023122271928320, coefficient := (-30317592820023122271928320) }, { argument := 62904693580949118728171159552, coefficient := (-62904693580949118728171159552) }, { argument := 52921936679450006751937560576, coefficient := (-52921936679450006751937560576) }, { argument := 3328137422736702029292000721764352, coefficient := 3328137422736702029292000721764352 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 29246333428117108994491809792, coefficient := 29246333428117108994491809792 }, { argument := 610517210311944650260016529408, coefficient := 610517210311944650260016529408 }, { argument := 31683527880460201410699460608, coefficient := 31683527880460201410699460608 }, { argument := 656823904906463406167961894912, coefficient := 656823904906463406167961894912 }, { argument := 983407961520437789939787104256, coefficient := 983407961520437789939787104256 }, { argument := 30464930654288655202595635200, coefficient := 30464930654288655202595635200 }, { argument := 983407961520437789939787104256, coefficient := 983407961520437789939787104256 }, { argument := 1024840267210270361015317168128, coefficient := 1024840267210270361015317168128 }, { argument := 610517210311944650260016529408, coefficient := 610517210311944650260016529408 }, { argument := 30464930654288655202595635200, coefficient := 30464930654288655202595635200 }, { argument := 4991374238398653268393268871168, coefficient := (-4991374238398653268393268871168) }, { argument := 783113131726686028274467864576, coefficient := 783113131726686028274467864576 }, { argument := 884159987433355193213108879360, coefficient := 884159987433355193213108879360 }, { argument := 757851417800018737039807610880, coefficient := 757851417800018737039807610880 }, { argument := 9978377001033580037690800209920, coefficient := 9978377001033580037690800209920 }, { argument := 884159987433355193213108879360, coefficient := 884159987433355193213108879360 }, { argument := 757851417800018737039807610880, coefficient := 757851417800018737039807610880 }, { argument := 884159987433355193213108879360, coefficient := 884159987433355193213108879360 }, { argument := 884159987433355193213108879360, coefficient := 884159987433355193213108879360 }, { argument := 36654746907594239581492028112896, coefficient := 36654746907594239581492028112896 }, { argument := 909421701360022484447769133056, coefficient := 909421701360022484447769133056 }, { argument := 9978377001033580037690800209920, coefficient := 9978377001033580037690800209920 }, { argument := 36654746907594239581492028112896, coefficient := 36654746907594239581492028112896 }, { argument := 783113131726686028274467864576, coefficient := 783113131726686028274467864576 }, { argument := 884159987433355193213108879360, coefficient := 884159987433355193213108879360 }, { argument := 909421701360022484447769133056, coefficient := 909421701360022484447769133056 }, { argument := 884159987433355193213108879360, coefficient := 884159987433355193213108879360 }, { argument := 103471980243629224897168399138816, coefficient := (-103471980243629224897168399138816) }, { argument := 160738776975961095068933160960, coefficient := 160738776975961095068933160960 }, { argument := 2330712266151435878499530833920, coefficient := 2330712266151435878499530833920 }, { argument := 4125628609049668106769284464640, coefficient := 4125628609049668106769284464640 }, { argument := 133948980813300912557444300800, coefficient := 133948980813300912557444300800 }, { argument := 2571820431615377521102930575360, coefficient := 2571820431615377521102930575360 }, { argument := 133948980813300912557444300800, coefficient := 133948980813300912557444300800 }, { argument := 4098838812887007924257795604480, coefficient := 4098838812887007924257795604480 }, { argument := 4286367386025629201838217625600, coefficient := 4286367386025629201838217625600 }, { argument := 2571820431615377521102930575360, coefficient := 2571820431615377521102930575360 }, { argument := 65661790394680107335659196252160, coefficient := 65661790394680107335659196252160 }, { argument := 4205997997537648654303751045120, coefficient := 4205997997537648654303751045120 }, { argument := 2330712266151435878499530833920, coefficient := 2330712266151435878499530833920 }, { argument := 4098838812887007924257795604480, coefficient := 4098838812887007924257795604480 }, { argument := 133948980813300912557444300800, coefficient := 133948980813300912557444300800 }] }

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

end TermShard5


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10
