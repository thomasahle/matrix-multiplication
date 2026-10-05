import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 8, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8

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
def constantNumerator : ℤ := (-723435543152779221342393674498048)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    294525, 9625, 7805706991107, 26163, 78489, 165699,
    427329, 357561, 10002987, 305235, 357561, 322677,
    165699, 165699, 322677, 10002987, 322677, 26163,
    427329, 92653083, 32310834117, 173635, 1165856920943, 6765,
    11275, 345015, 11275, 6765, 5527005, 354035,
    129243420701, 345015, 11275, 354035, 11275, 345015,
    11275, 92653083, 83348643891807, 13058590849256797, 3264648704960929, 333398672007843,
    2700459, 952586421, 156695, 34449395519, 6105, 10175,
    311355, 10175, 6105, 4987785, 319495, 3810348173,
    311355, 10175, 319495, 10175, 311355, 10175,
    2700459, 3267667107, 257240258601, 257240241483
  ]
def negativeCoefficients : Array ℕ := #[
    1390854988367182256563814400, 1454488876723850725818368000, 17576889548256380367233089536, 1976820388661096443614855168, 1482615291495822332711141376, 1564982807690034684528427008,
    2018004146758202619523497984, 27016545311701651396069687296, 47237770537380783767213309952, 1441431533398716156802498560, 27016545311701651396069687296, 1523799049592928508619784192,
    1564982807690034684528427008, 1564982807690034684528427008, 1523799049592928508619784192, 47237770537380783767213309952, 1523799049592928508619784192, 1976820388661096443614855168,
    2018004146758202619523497984, 3418295419482338407540064256, 298014843882191071551512641536, 26238979336098267093763358720, 2688283030899818810389861236736, 16356766339385932733774561280,
    851914913509683996550758400, 26068596353396330294453207040, 27261277232309887889624268800, 16356766339385932733774561280, 417608690602447095109181767680, 26750128284204077491693813760,
    298015038110265266648595300352, 26068596353396330294453207040, 851914913509683996550758400, 26750128284204077491693813760, 851914913509683996550758400, 26068596353396330294453207040,
    27261277232309887889624268800, 3418295419482338407540064256, 93842230393244543180831981568, 3675666555168542491981310328832, 3675667672789403045141671837696, 93843383438771246891173675008,
    199258704218182488189566976, 17572117916277941967400206336, 1479942432066518113520189440, 158869795658247408286932402176, 922561516093413888947650560, 48050078963198640049356800,
    1470332416273878385510318080, 1537602526822356481579417600, 922561516093413888947650560, 23554148707759973352194703360, 1508772479444437297549803520, 17572129394764441833168699392,
    1470332416273878385510318080, 48050078963198640049356800, 1508772479444437297549803520, 48050078963198640049356800, 1470332416273878385510318080, 1537602526822356481579417600,
    199258704218182488189566976, 15069454710226971321830473728, 593155651983438657882949681152, 593155612512018026162936610816
  ]
def negativeScales : Array ℕ := #[
    18, 13, 42, 14, 16, 17,
    18, 18, 23, 18, 18, 18,
    17, 17, 18, 23, 18, 14,
    18, 26, 34, 17, 40, 12,
    13, 18, 13, 12, 22, 18,
    36, 18, 13, 18, 13, 18,
    13, 26, 46, 53, 51, 48,
    21, 29, 17, 35, 12, 13,
    18, 13, 12, 22, 18, 31,
    18, 13, 18, 13, 18, 13,
    21, 31, 37, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    18168030573162278, 13232570825356989, 42827666447999971, 14675240357618530, 16260202858299706, 17338205370300980,
    18704987701053965, 18447829861475521, 23253927532873219, 18219560873802360, 18447829861475521, 18299731222486344,
    17338205370300980, 17338205370300980, 18299731222486344, 23253927532873219, 18299731222486344, 14675240357618530,
    18704987701053965, 26465335646452397, 34911298949043322, 17405698258837653, 40084527884209212, 12723874218989575,
    13460839813030175, 18396299560835401, 13460839813030175, 12723874218989575, 22398066487009589, 18433532467034396,
    36911299889304588, 18396299560835401, 13460839813030175, 18433532467034396, 13460839813030175, 18396299560835401,
    13460839813030175, 26465335646452397, 46244223959844213, 53535848742458642, 51535849181123522, 48244241686222164,
    21364773213912652, 29827274743625789, 17257599619848511, 35003759617161909, 12575775579877617, 13312741174040972,
    18248200921846262, 13312741174040972, 12575775579877617, 22249967848020450, 18285433828045237, 31827275686025025,
    18248200921846262, 13312741174040972, 18285433828045237, 13312741174040972, 18248200921846262, 13312741174040972,
    21364773213912652, 31605613870664104, 37904325493396422, 37904325397392566
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
noncomputable def negativeCeiling : ℝ := 7162365057 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1390854988367182256563814400, coefficient := (-1390854988367182256563814400) }, { argument := 1454488876723850725818368000, coefficient := (-1454488876723850725818368000) }, { argument := 17576889548256380367233089536, coefficient := (-17576889548256380367233089536) }, { argument := 1976820388661096443614855168, coefficient := (-1976820388661096443614855168) }, { argument := 1482615291495822332711141376, coefficient := (-1482615291495822332711141376) }, { argument := 1564982807690034684528427008, coefficient := (-1564982807690034684528427008) }, { argument := 2018004146758202619523497984, coefficient := (-2018004146758202619523497984) }, { argument := 27016545311701651396069687296, coefficient := (-27016545311701651396069687296) }, { argument := 47237770537380783767213309952, coefficient := (-47237770537380783767213309952) }, { argument := 1441431533398716156802498560, coefficient := (-1441431533398716156802498560) }, { argument := 27016545311701651396069687296, coefficient := (-27016545311701651396069687296) }, { argument := 1523799049592928508619784192, coefficient := (-1523799049592928508619784192) }, { argument := 1564982807690034684528427008, coefficient := (-1564982807690034684528427008) }, { argument := 1564982807690034684528427008, coefficient := (-1564982807690034684528427008) }, { argument := 1523799049592928508619784192, coefficient := (-1523799049592928508619784192) }, { argument := 47237770537380783767213309952, coefficient := (-47237770537380783767213309952) }, { argument := 1523799049592928508619784192, coefficient := (-1523799049592928508619784192) }, { argument := 1976820388661096443614855168, coefficient := (-1976820388661096443614855168) }, { argument := 2018004146758202619523497984, coefficient := (-2018004146758202619523497984) }, { argument := 3418295419482338407540064256, coefficient := (-3418295419482338407540064256) }, { argument := 298014843882191071551512641536, coefficient := (-298014843882191071551512641536) }, { argument := 26238979336098267093763358720, coefficient := (-26238979336098267093763358720) }, { argument := 2688283030899818810389861236736, coefficient := (-2688283030899818810389861236736) }, { argument := 16356766339385932733774561280, coefficient := (-16356766339385932733774561280) }, { argument := 851914913509683996550758400, coefficient := (-851914913509683996550758400) }, { argument := 26068596353396330294453207040, coefficient := (-26068596353396330294453207040) }, { argument := 27261277232309887889624268800, coefficient := (-27261277232309887889624268800) }, { argument := 16356766339385932733774561280, coefficient := (-16356766339385932733774561280) }, { argument := 417608690602447095109181767680, coefficient := (-417608690602447095109181767680) }, { argument := 26750128284204077491693813760, coefficient := (-26750128284204077491693813760) }, { argument := 298015038110265266648595300352, coefficient := (-298015038110265266648595300352) }, { argument := 26068596353396330294453207040, coefficient := (-26068596353396330294453207040) }, { argument := 851914913509683996550758400, coefficient := (-851914913509683996550758400) }, { argument := 26750128284204077491693813760, coefficient := (-26750128284204077491693813760) }, { argument := 851914913509683996550758400, coefficient := (-851914913509683996550758400) }, { argument := 26068596353396330294453207040, coefficient := (-26068596353396330294453207040) }, { argument := 27261277232309887889624268800, coefficient := (-27261277232309887889624268800) }, { argument := 3418295419482338407540064256, coefficient := (-3418295419482338407540064256) }, { argument := 93842230393244543180831981568, coefficient := (-93842230393244543180831981568) }, { argument := 3675666555168542491981310328832, coefficient := (-3675666555168542491981310328832) }, { argument := 3675667672789403045141671837696, coefficient := (-3675667672789403045141671837696) }, { argument := 93843383438771246891173675008, coefficient := (-93843383438771246891173675008) }, { argument := 199258704218182488189566976, coefficient := (-199258704218182488189566976) }, { argument := 17572117916277941967400206336, coefficient := (-17572117916277941967400206336) }, { argument := 1479942432066518113520189440, coefficient := (-1479942432066518113520189440) }, { argument := 158869795658247408286932402176, coefficient := (-158869795658247408286932402176) }, { argument := 922561516093413888947650560, coefficient := (-922561516093413888947650560) }, { argument := 48050078963198640049356800, coefficient := (-48050078963198640049356800) }, { argument := 1470332416273878385510318080, coefficient := (-1470332416273878385510318080) }, { argument := 1537602526822356481579417600, coefficient := (-1537602526822356481579417600) }, { argument := 922561516093413888947650560, coefficient := (-922561516093413888947650560) }, { argument := 23554148707759973352194703360, coefficient := (-23554148707759973352194703360) }, { argument := 1508772479444437297549803520, coefficient := (-1508772479444437297549803520) }, { argument := 17572129394764441833168699392, coefficient := (-17572129394764441833168699392) }, { argument := 1470332416273878385510318080, coefficient := (-1470332416273878385510318080) }, { argument := 48050078963198640049356800, coefficient := (-48050078963198640049356800) }, { argument := 1508772479444437297549803520, coefficient := (-1508772479444437297549803520) }, { argument := 48050078963198640049356800, coefficient := (-48050078963198640049356800) }, { argument := 1470332416273878385510318080, coefficient := (-1470332416273878385510318080) }, { argument := 1537602526822356481579417600, coefficient := (-1537602526822356481579417600) }, { argument := 199258704218182488189566976, coefficient := (-199258704218182488189566976) }, { argument := 15069454710226971321830473728, coefficient := (-15069454710226971321830473728) }, { argument := 593155651983438657882949681152, coefficient := (-593155651983438657882949681152) }, { argument := 593155612512018026162936610816, coefficient := (-593155612512018026162936610816) }] }

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
def constantNumerator : ℤ := (-57517077730633068433500910125056)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3267667107, 4178949123, 15323251053, 261177513, 855, 2565,
    5415, 13965, 11685, 326895, 9975, 11685,
    10545, 5415, 5415, 10545, 326895, 10545,
    855, 13965, 26847, 80541, 170031, 438501,
    366909, 10264503, 313215, 366909, 331113, 170031,
    170031, 331113, 10264503, 331113, 26847, 438501,
    2721579, 953811381, 80465, 34449677119, 3135, 5225,
    159885, 5225, 3135, 2561295, 164065, 3815248013,
    159885, 5225, 164065, 5225, 159885, 5225,
    2721579, 855, 2565, 5415, 13965, 11685,
    326895, 9975, 11685, 10545
  ]
def negativeCoefficients : Array ℕ := #[
    15069454710226971321830473728, 77088004969033978082406432768, 282664090551891396416029851648, 77085995841903190006592176128, 64601973485656746523361280, 48451480114242559892520960,
    51143229009478257664327680, 65947847933274595409264640, 882893637637308869152604160, 1543717991417672672131153920, 47105605666624711006617600, 882893637637308869152604160,
    49797354561860408778424320, 51143229009478257664327680, 51143229009478257664327680, 49797354561860408778424320, 1543717991417672672131153920, 49797354561860408778424320,
    64601973485656746523361280, 65947847933274595409264640, 2028501967449621840833544192, 1521376475587216380625158144, 1605897390897617290659889152, 2070762425104822295850909696,
    27722860221811498491391770624, 48472744930514921904918233088, 1479116017932015925607792640, 27722860221811498491391770624, 1563636933242416835642523648, 1605897390897617290659889152,
    1605897390897617290659889152, 1563636933242416835642523648, 48472744930514921904918233088, 1563636933242416835642523648, 2028501967449621840833544192, 2070762425104822295850909696,
    200817085157529471110086656, 17594714439898473219747741696, 1519940876176424008480194560, 158871094309030197439366168576, 947495611122965615675965440, 49348729745987792483123200,
    1510071130227226449983569920, 1579159351871609359459942400, 947495611122965615675965440, 24190747321483215875226992640, 1549550114024016683970068480, 17594725918384973085516234752,
    1510071130227226449983569920, 49348729745987792483123200, 1549550114024016683970068480, 49348729745987792483123200, 1510071130227226449983569920, 1579159351871609359459942400,
    200817085157529471110086656, 64601973485656746523361280, 48451480114242559892520960, 51143229009478257664327680, 65947847933274595409264640, 882893637637308869152604160,
    1543717991417672672131153920, 47105605666624711006617600, 882893637637308869152604160, 49797354561860408778424320
  ]
def negativeScales : Array ℕ := #[
    31, 31, 33, 27, 9, 11,
    12, 13, 13, 18, 13, 13,
    13, 12, 12, 13, 18, 13,
    9, 13, 14, 16, 17, 18,
    18, 23, 18, 18, 18, 17,
    17, 18, 23, 18, 14, 18,
    21, 29, 16, 35, 11, 12,
    17, 12, 11, 21, 17, 31,
    17, 12, 17, 12, 17, 12,
    21, 9, 11, 12, 13, 13,
    18, 13, 13, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31605613870664104, 31960493060961510, 33835003368873105, 27960455459831178, 9739780609952834, 11324743110494417,
    12402745622495697, 13769527953509885, 13512370113670596, 18318467785067930, 13284101125997071, 13512370113670596,
    13364271474681056, 12402745622495697, 12402745622495697, 13364271474681056, 18318467785067930, 13364271474681056,
    9739780609952834, 13769527953509885, 14712473263874332, 16297435764498682, 17375438276499957, 18742220607361118,
    18485062767674616, 23291160439072194, 18256793780001336, 18485062767674616, 18336964128685319, 17375438276499957,
    17375438276499957, 18336964128685319, 23291160439072194, 18336964128685319, 14712473263874332, 18742220607361118,
    21376012483488986, 29829128757513200, 16296073767663147, 35003771410148606, 11614249727697750, 12351215321855609,
    17286675069660898, 12351215321855609, 11614249727697750, 21288441995835085, 17323907975859873, 31829129698702134,
    17286675069660898, 12351215321855609, 17323907975859873, 12351215321855609, 17286675069660898, 12351215321855609,
    21376012483488986, 9739780609952834, 11324743110494417, 12402745622495697, 13769527953509885, 13512370113670596,
    18318467785067930, 13284101125997071, 13512370113670596, 13364271474681056
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
noncomputable def negativeCeiling : ℝ := 310976581 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 15069454710226971321830473728, coefficient := (-15069454710226971321830473728) }, { argument := 77088004969033978082406432768, coefficient := (-77088004969033978082406432768) }, { argument := 282664090551891396416029851648, coefficient := (-282664090551891396416029851648) }, { argument := 77085995841903190006592176128, coefficient := (-77085995841903190006592176128) }, { argument := 64601973485656746523361280, coefficient := (-64601973485656746523361280) }, { argument := 48451480114242559892520960, coefficient := (-48451480114242559892520960) }, { argument := 51143229009478257664327680, coefficient := (-51143229009478257664327680) }, { argument := 65947847933274595409264640, coefficient := (-65947847933274595409264640) }, { argument := 882893637637308869152604160, coefficient := (-882893637637308869152604160) }, { argument := 1543717991417672672131153920, coefficient := (-1543717991417672672131153920) }, { argument := 47105605666624711006617600, coefficient := (-47105605666624711006617600) }, { argument := 882893637637308869152604160, coefficient := (-882893637637308869152604160) }, { argument := 49797354561860408778424320, coefficient := (-49797354561860408778424320) }, { argument := 51143229009478257664327680, coefficient := (-51143229009478257664327680) }, { argument := 51143229009478257664327680, coefficient := (-51143229009478257664327680) }, { argument := 49797354561860408778424320, coefficient := (-49797354561860408778424320) }, { argument := 1543717991417672672131153920, coefficient := (-1543717991417672672131153920) }, { argument := 49797354561860408778424320, coefficient := (-49797354561860408778424320) }, { argument := 64601973485656746523361280, coefficient := (-64601973485656746523361280) }, { argument := 65947847933274595409264640, coefficient := (-65947847933274595409264640) }, { argument := 2028501967449621840833544192, coefficient := (-2028501967449621840833544192) }, { argument := 1521376475587216380625158144, coefficient := (-1521376475587216380625158144) }, { argument := 1605897390897617290659889152, coefficient := (-1605897390897617290659889152) }, { argument := 2070762425104822295850909696, coefficient := (-2070762425104822295850909696) }, { argument := 27722860221811498491391770624, coefficient := (-27722860221811498491391770624) }, { argument := 48472744930514921904918233088, coefficient := (-48472744930514921904918233088) }, { argument := 1479116017932015925607792640, coefficient := (-1479116017932015925607792640) }, { argument := 27722860221811498491391770624, coefficient := (-27722860221811498491391770624) }, { argument := 1563636933242416835642523648, coefficient := (-1563636933242416835642523648) }, { argument := 1605897390897617290659889152, coefficient := (-1605897390897617290659889152) }, { argument := 1605897390897617290659889152, coefficient := (-1605897390897617290659889152) }, { argument := 1563636933242416835642523648, coefficient := (-1563636933242416835642523648) }, { argument := 48472744930514921904918233088, coefficient := (-48472744930514921904918233088) }, { argument := 1563636933242416835642523648, coefficient := (-1563636933242416835642523648) }, { argument := 2028501967449621840833544192, coefficient := (-2028501967449621840833544192) }, { argument := 2070762425104822295850909696, coefficient := (-2070762425104822295850909696) }, { argument := 200817085157529471110086656, coefficient := (-200817085157529471110086656) }, { argument := 17594714439898473219747741696, coefficient := (-17594714439898473219747741696) }, { argument := 1519940876176424008480194560, coefficient := (-1519940876176424008480194560) }, { argument := 158871094309030197439366168576, coefficient := (-158871094309030197439366168576) }, { argument := 947495611122965615675965440, coefficient := (-947495611122965615675965440) }, { argument := 49348729745987792483123200, coefficient := (-49348729745987792483123200) }, { argument := 1510071130227226449983569920, coefficient := (-1510071130227226449983569920) }, { argument := 1579159351871609359459942400, coefficient := (-1579159351871609359459942400) }, { argument := 947495611122965615675965440, coefficient := (-947495611122965615675965440) }, { argument := 24190747321483215875226992640, coefficient := (-24190747321483215875226992640) }, { argument := 1549550114024016683970068480, coefficient := (-1549550114024016683970068480) }, { argument := 17594725918384973085516234752, coefficient := (-17594725918384973085516234752) }, { argument := 1510071130227226449983569920, coefficient := (-1510071130227226449983569920) }, { argument := 49348729745987792483123200, coefficient := (-49348729745987792483123200) }, { argument := 1549550114024016683970068480, coefficient := (-1549550114024016683970068480) }, { argument := 49348729745987792483123200, coefficient := (-49348729745987792483123200) }, { argument := 1510071130227226449983569920, coefficient := (-1510071130227226449983569920) }, { argument := 1579159351871609359459942400, coefficient := (-1579159351871609359459942400) }, { argument := 200817085157529471110086656, coefficient := (-200817085157529471110086656) }, { argument := 64601973485656746523361280, coefficient := (-64601973485656746523361280) }, { argument := 48451480114242559892520960, coefficient := (-48451480114242559892520960) }, { argument := 51143229009478257664327680, coefficient := (-51143229009478257664327680) }, { argument := 65947847933274595409264640, coefficient := (-65947847933274595409264640) }, { argument := 882893637637308869152604160, coefficient := (-882893637637308869152604160) }, { argument := 1543717991417672672131153920, coefficient := (-1543717991417672672131153920) }, { argument := 47105605666624711006617600, coefficient := (-47105605666624711006617600) }, { argument := 882893637637308869152604160, coefficient := (-882893637637308869152604160) }, { argument := 49797354561860408778424320, coefficient := (-49797354561860408778424320) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8
