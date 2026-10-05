import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 15, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15

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
def constantNumerator : ℤ := (-171045315713200135622541330463326208)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    7563955, 1000990565, 335, 10423343981, 253, 3,
    335, 269, 253, 4697, 69, 500495379,
    335, 3, 69, 3, 21, 269,
    7580245, 725795641033941, 1069655649, 26590945095254699, 36794136297, 459327507,
    212721952935657091, 465618963, 465618963, 27498050481, 446744595, 36794136297,
    27498050481, 5811975693532541, 459327507, 446744595, 1069655649, 62037972360242791,
    214923627120919507, 31018986093161187, 727459870925007, 727459626360625, 1069655649, 1069439391,
    15280399, 725795396582187, 1069439391, 26590937883540821, 36790733079, 459225069,
    212721895241924989, 465516525, 465516525, 27489274959, 446642157, 36790733079,
    27489274959, 5811973737939587, 459225069, 446642157, 1069439391, 107463983951343003,
    744320637924714635, 214927967294225471, 26650853515208369, 26650846299412815
  ]
def negativeCoefficients : Array ℕ := #[
    71439535139868534524723855360, 9454088587649497967614209556480, 51838739145075299011400826880, 98445700510590912091567320727552, 39149853742400151193684803584, 1856910058928070412348686336,
    51838739145075299011400826880, 41625733820970911743483052032, 39149853742400151193684803584, 726825545565428893900148310016, 42708931355345619484019785728, 9454090410482960355297262043136,
    51838739145075299011400826880, 1856910058928070412348686336, 42708931355345619484019785728, 1856910058928070412348686336, 51993481649985971545763217408, 41625733820970911743483052032,
    71593389839880427565786071040, 6537385957015173927521036009472, 2466458000512586783913934848, 239509940844836761360817515921408, 42420750980246641034366287872, 2118274241911008146466275328,
    239503626993637365675588566646784, 2147288461581759246659223552, 2147288461581759246659223552, 63406187468619104408580390912, 2060245802569505946080378880, 42420750980246641034366287872,
    63406187468619104408580390912, 6543702891919882926628309827584, 2118274241911008146466275328, 2060245802569505946080378880, 2466458000512586783913934848, 69848547301102640946154867523584,
    241982491753722129944004020666368, 69848547105285659647824548069376, 6552376007249701285021240786944, 6552373804409581998429962240000, 2466458000512586783913934848, 2465959343515100248887263232,
    72159644082474843853715144704, 6537383755189517478592725909504, 2465959343515100248887263232, 239509875887492894033948214034432, 42416827337029575929814319104, 2117801830018652481704165376,
    239503562036269766630482835931136, 2146816049689403581897113600, 2146816049689403581897113600, 63385952492563203434603347968, 2059773390677150281318268928, 42416827337029575929814319104,
    63385952492563203434603347968, 6543700690117958195936428556288, 2117801830018652481704165376, 2059773390677150281318268928, 2465959343515100248887263232, 241987379039508655328948329119744,
    838030536900478675833999054602240, 241987378354442995655035169275904, 240049547920396168159298005762048, 240049482926287831807134510612480
  ]
def negativeScales : Array ℕ := #[
    22, 29, 8, 33, 7, 1,
    8, 8, 7, 12, 6, 28,
    8, 1, 6, 1, 4, 8,
    22, 49, 29, 54, 35, 28,
    57, 28, 28, 34, 28, 35,
    34, 52, 28, 28, 29, 55,
    57, 54, 49, 49, 29, 29,
    23, 49, 29, 54, 35, 28,
    57, 28, 28, 34, 28, 35,
    34, 52, 28, 28, 29, 56,
    59, 57, 54, 54
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    22850709351412794, 29898781234139747, 8388017285345139, 33279099141159718, 7982993592700323, 1584962500724866,
    8388017285345139, 8071462362556625, 7982993592700323, 12197523878257788, 6108524456778170, 28898781512304344,
    8388017285345139, 1584962500724866, 6108524456778170, 1584962500724866, 4392317422778766, 8071462362556625,
    22853813049473987, 49366556720763055, 29994499304596942, 54561784572567380, 35098756818164578, 28774947941962561,
    57561746540401166, 28794574574944207, 28794574574944207, 34678610288969174, 28734875033990868, 35098756818164578,
    34678610288969174, 52367950092748261, 28774947941962561, 28734875033990868, 29994499304596942, 55784001052979203,
    57576601703841167, 54784001048934678, 49369860994843625, 49369860509824596, 29994499304596942, 29994207597638930,
    23865178881869807, 49366556234855765, 29994207597638930, 54561784181294891, 35098623372096744, 28774626160062935,
    57561746149118220, 28794257141447473, 28794257141447473, 34678149804590635, 28734544187813790, 35098623372096744,
    34678149804590635, 52367949607315272, 28774626160062935, 28734544187813790, 29994207597638930, 56576630841452386,
    59368701851480379, 57576630837368120, 54565031255403490, 54565030864789588
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
noncomputable def negativeCeiling : ℝ := 1112105725717 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 71439535139868534524723855360, coefficient := (-71439535139868534524723855360) }, { argument := 9454088587649497967614209556480, coefficient := (-9454088587649497967614209556480) }, { argument := 51838739145075299011400826880, coefficient := (-51838739145075299011400826880) }, { argument := 98445700510590912091567320727552, coefficient := (-98445700510590912091567320727552) }, { argument := 39149853742400151193684803584, coefficient := (-39149853742400151193684803584) }, { argument := 1856910058928070412348686336, coefficient := (-1856910058928070412348686336) }, { argument := 51838739145075299011400826880, coefficient := (-51838739145075299011400826880) }, { argument := 41625733820970911743483052032, coefficient := (-41625733820970911743483052032) }, { argument := 39149853742400151193684803584, coefficient := (-39149853742400151193684803584) }, { argument := 726825545565428893900148310016, coefficient := (-726825545565428893900148310016) }, { argument := 42708931355345619484019785728, coefficient := (-42708931355345619484019785728) }, { argument := 9454090410482960355297262043136, coefficient := (-9454090410482960355297262043136) }, { argument := 51838739145075299011400826880, coefficient := (-51838739145075299011400826880) }, { argument := 1856910058928070412348686336, coefficient := (-1856910058928070412348686336) }, { argument := 42708931355345619484019785728, coefficient := (-42708931355345619484019785728) }, { argument := 1856910058928070412348686336, coefficient := (-1856910058928070412348686336) }, { argument := 51993481649985971545763217408, coefficient := (-51993481649985971545763217408) }, { argument := 41625733820970911743483052032, coefficient := (-41625733820970911743483052032) }, { argument := 71593389839880427565786071040, coefficient := (-71593389839880427565786071040) }, { argument := 6537385957015173927521036009472, coefficient := (-6537385957015173927521036009472) }, { argument := 2466458000512586783913934848, coefficient := (-2466458000512586783913934848) }, { argument := 239509940844836761360817515921408, coefficient := (-239509940844836761360817515921408) }, { argument := 42420750980246641034366287872, coefficient := (-42420750980246641034366287872) }, { argument := 2118274241911008146466275328, coefficient := (-2118274241911008146466275328) }, { argument := 239503626993637365675588566646784, coefficient := (-239503626993637365675588566646784) }, { argument := 2147288461581759246659223552, coefficient := (-2147288461581759246659223552) }, { argument := 2147288461581759246659223552, coefficient := (-2147288461581759246659223552) }, { argument := 63406187468619104408580390912, coefficient := (-63406187468619104408580390912) }, { argument := 2060245802569505946080378880, coefficient := (-2060245802569505946080378880) }, { argument := 42420750980246641034366287872, coefficient := (-42420750980246641034366287872) }, { argument := 63406187468619104408580390912, coefficient := (-63406187468619104408580390912) }, { argument := 6543702891919882926628309827584, coefficient := (-6543702891919882926628309827584) }, { argument := 2118274241911008146466275328, coefficient := (-2118274241911008146466275328) }, { argument := 2060245802569505946080378880, coefficient := (-2060245802569505946080378880) }, { argument := 2466458000512586783913934848, coefficient := (-2466458000512586783913934848) }, { argument := 69848547301102640946154867523584, coefficient := (-69848547301102640946154867523584) }, { argument := 241982491753722129944004020666368, coefficient := (-241982491753722129944004020666368) }, { argument := 69848547105285659647824548069376, coefficient := (-69848547105285659647824548069376) }, { argument := 6552376007249701285021240786944, coefficient := (-6552376007249701285021240786944) }, { argument := 6552373804409581998429962240000, coefficient := (-6552373804409581998429962240000) }, { argument := 2466458000512586783913934848, coefficient := (-2466458000512586783913934848) }, { argument := 2465959343515100248887263232, coefficient := (-2465959343515100248887263232) }, { argument := 72159644082474843853715144704, coefficient := (-72159644082474843853715144704) }, { argument := 6537383755189517478592725909504, coefficient := (-6537383755189517478592725909504) }, { argument := 2465959343515100248887263232, coefficient := (-2465959343515100248887263232) }, { argument := 239509875887492894033948214034432, coefficient := (-239509875887492894033948214034432) }, { argument := 42416827337029575929814319104, coefficient := (-42416827337029575929814319104) }, { argument := 2117801830018652481704165376, coefficient := (-2117801830018652481704165376) }, { argument := 239503562036269766630482835931136, coefficient := (-239503562036269766630482835931136) }, { argument := 2146816049689403581897113600, coefficient := (-2146816049689403581897113600) }, { argument := 2146816049689403581897113600, coefficient := (-2146816049689403581897113600) }, { argument := 63385952492563203434603347968, coefficient := (-63385952492563203434603347968) }, { argument := 2059773390677150281318268928, coefficient := (-2059773390677150281318268928) }, { argument := 42416827337029575929814319104, coefficient := (-42416827337029575929814319104) }, { argument := 63385952492563203434603347968, coefficient := (-63385952492563203434603347968) }, { argument := 6543700690117958195936428556288, coefficient := (-6543700690117958195936428556288) }, { argument := 2117801830018652481704165376, coefficient := (-2117801830018652481704165376) }, { argument := 2059773390677150281318268928, coefficient := (-2059773390677150281318268928) }, { argument := 2465959343515100248887263232, coefficient := (-2465959343515100248887263232) }, { argument := 241987379039508655328948329119744, coefficient := (-241987379039508655328948329119744) }, { argument := 838030536900478675833999054602240, coefficient := (-838030536900478675833999054602240) }, { argument := 241987378354442995655035169275904, coefficient := (-241987378354442995655035169275904) }, { argument := 240049547920396168159298005762048, coefficient := (-240049547920396168159298005762048) }, { argument := 240049482926287831807134510612480, coefficient := (-240049482926287831807134510612480) }] }

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
def constantNumerator : ℤ := 368380333688964246474142748671737856
def positiveArguments : Array ℕ := #[
    13553, 5, 21, 91, 3, 3,
    7, 91, 91, 3, 1123, 45,
    21, 91, 7, 45, 7
  ]
def positiveCoefficients : Array ℕ := #[
    4295117146223298269621204635615232, 1547425049106725343623905280, 25996740824992985772881608704, 56326271787484802507910152192, 1856910058928070412348686336, 29710560942849126597578981376,
    2166395068749415481073467392, 56326271787484802507910152192, 56326271787484802507910152192, 29710560942849126597578981376, 695103332058741024355858251776, 55707301767842112370460590080,
    25996740824992985772881608704, 56326271787484802507910152192, 2166395068749415481073467392, 55707301767842112370460590080, 2166395068749415481073467392
  ]
def positiveScales : Array ℕ := #[
    13, 2, 4, 6, 1, 1,
    2, 6, 6, 1, 10, 5,
    4, 6, 2, 5, 2
  ]
def negativeArguments : Array ℕ := #[
    36794136297, 36790733079, 2016048293, 459327507, 459225069, 335,
    62037972186234467, 107461813256317393, 62037972012314107, 213201215215984313, 213201157489598791, 21002798015,
    465618963, 465516525, 253, 3, 465618963, 465516525,
    27498050481, 27489274959, 335, 446744595, 446642157, 269,
    36794136297, 36790733079, 253, 27498050481, 27489274959, 4697,
    69, 5825294666489159, 5825292709995193, 1008024347, 335, 459327507,
    459225069, 3, 446744595, 446642157, 69, 3,
    1069655649, 1069439391, 21, 269, 15312983
  ]
def negativeCoefficients : Array ℕ := #[
    42420750980246641034366287872, 42416827337029575929814319104, 9520518886709761974587441020928, 2118274241911008146466275328, 2117801830018652481704165376, 51838739145075299011400826880,
    69848547105186685164713733521408, 241982491068854419236312489918464, 69848546909369768042678104096768, 240043228350410968474328143757312, 240043163356278886893129337667584, 99182909392517115997968599613440,
    2147288461581759246659223552, 2146816049689403581897113600, 39149853742400151193684803584, 1856910058928070412348686336, 2147288461581759246659223552, 2146816049689403581897113600,
    63406187468619104408580390912, 63385952492563203434603347968, 51838739145075299011400826880, 2060245802569505946080378880, 2059773390677150281318268928, 41625733820970911743483052032,
    42420750980246641034366287872, 42416827337029575929814319104, 39149853742400151193684803584, 63406187468619104408580390912, 63385952492563203434603347968, 726825545565428893900148310016,
    42708931355345619484019785728, 6558698722330978561174815113216, 6558696519514604503618847506432, 9520520780378721605315171713024, 51838739145075299011400826880, 2118274241911008146466275328,
    2117801830018652481704165376, 1856910058928070412348686336, 2060245802569505946080378880, 2059773390677150281318268928, 42708931355345619484019785728, 1856910058928070412348686336,
    2466458000512586783913934848, 2465959343515100248887263232, 51993481649985971545763217408, 41625733820970911743483052032, 72313517671952668373358215168
  ]
def negativeScales : Array ℕ := #[
    35, 35, 30, 28, 28, 8,
    55, 56, 55, 57, 57, 34,
    28, 28, 7, 1, 28, 28,
    34, 34, 8, 28, 28, 8,
    35, 35, 7, 34, 34, 12,
    6, 52, 52, 29, 8, 28,
    28, 1, 28, 28, 6, 1,
    29, 29, 4, 8, 23
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13726324611642090, 2321928094887362, 4392317422778759, 6507794640198673, 1584962500720924, 1584962500720924,
    2807354922011143, 6507794640198673, 6507794640198673, 1584962500720924, 10133142212400601, 5491853096329661,
    4392317422778759, 6507794640198673, 2807354922011143, 5491853096329661, 2807354922011143
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    35098756818164578, 35098623372096744, 30908883057086717, 28774947941962561, 28774626160062935, 8388017285345139,
    55784001048932634, 56576601699757999, 55784001044888110, 57564993274360117, 57564992883735789, 34289862486930134,
    28794574574944207, 28794257141447473, 7982993592700323, 1584962500724866, 28794574574944207, 28794257141447473,
    34678610288969174, 34678149804590635, 8388017285345139, 28734875033990868, 28734544187813790, 8071462362556625,
    35098756818164578, 35098623372096744, 7982993592700323, 34678610288969174, 34678149804590635, 12197523878257788,
    6108524456778170, 52371252452155548, 52371251967609310, 29908883344044479, 8388017285345139, 28774947941962561,
    28774626160062935, 1584962500724866, 28734875033990868, 28734544187813790, 6108524456778170, 1584962500724866,
    29994499304596942, 29994207597638930, 4392317422778766, 8071462362556625, 23868252016776821
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
noncomputable def positiveFloor : ℝ := 70977308823 / 100000000000
noncomputable def negativeCeiling : ℝ := 647787935153 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 42420750980246641034366287872, coefficient := (-42420750980246641034366287872) }, { argument := 42416827337029575929814319104, coefficient := (-42416827337029575929814319104) }, { argument := 9520518886709761974587441020928, coefficient := (-9520518886709761974587441020928) }, { argument := 2118274241911008146466275328, coefficient := (-2118274241911008146466275328) }, { argument := 2117801830018652481704165376, coefficient := (-2117801830018652481704165376) }, { argument := 51838739145075299011400826880, coefficient := (-51838739145075299011400826880) }, { argument := 69848547105186685164713733521408, coefficient := (-69848547105186685164713733521408) }, { argument := 241982491068854419236312489918464, coefficient := (-241982491068854419236312489918464) }, { argument := 69848546909369768042678104096768, coefficient := (-69848546909369768042678104096768) }, { argument := 240043228350410968474328143757312, coefficient := (-240043228350410968474328143757312) }, { argument := 240043163356278886893129337667584, coefficient := (-240043163356278886893129337667584) }, { argument := 99182909392517115997968599613440, coefficient := (-99182909392517115997968599613440) }, { argument := 2147288461581759246659223552, coefficient := (-2147288461581759246659223552) }, { argument := 2146816049689403581897113600, coefficient := (-2146816049689403581897113600) }, { argument := 39149853742400151193684803584, coefficient := (-39149853742400151193684803584) }, { argument := 1856910058928070412348686336, coefficient := (-1856910058928070412348686336) }, { argument := 2147288461581759246659223552, coefficient := (-2147288461581759246659223552) }, { argument := 2146816049689403581897113600, coefficient := (-2146816049689403581897113600) }, { argument := 63406187468619104408580390912, coefficient := (-63406187468619104408580390912) }, { argument := 63385952492563203434603347968, coefficient := (-63385952492563203434603347968) }, { argument := 51838739145075299011400826880, coefficient := (-51838739145075299011400826880) }, { argument := 2060245802569505946080378880, coefficient := (-2060245802569505946080378880) }, { argument := 2059773390677150281318268928, coefficient := (-2059773390677150281318268928) }, { argument := 41625733820970911743483052032, coefficient := (-41625733820970911743483052032) }, { argument := 42420750980246641034366287872, coefficient := (-42420750980246641034366287872) }, { argument := 42416827337029575929814319104, coefficient := (-42416827337029575929814319104) }, { argument := 39149853742400151193684803584, coefficient := (-39149853742400151193684803584) }, { argument := 63406187468619104408580390912, coefficient := (-63406187468619104408580390912) }, { argument := 63385952492563203434603347968, coefficient := (-63385952492563203434603347968) }, { argument := 726825545565428893900148310016, coefficient := (-726825545565428893900148310016) }, { argument := 42708931355345619484019785728, coefficient := (-42708931355345619484019785728) }, { argument := 6558698722330978561174815113216, coefficient := (-6558698722330978561174815113216) }, { argument := 6558696519514604503618847506432, coefficient := (-6558696519514604503618847506432) }, { argument := 9520520780378721605315171713024, coefficient := (-9520520780378721605315171713024) }, { argument := 51838739145075299011400826880, coefficient := (-51838739145075299011400826880) }, { argument := 2118274241911008146466275328, coefficient := (-2118274241911008146466275328) }, { argument := 2117801830018652481704165376, coefficient := (-2117801830018652481704165376) }, { argument := 1856910058928070412348686336, coefficient := (-1856910058928070412348686336) }, { argument := 2060245802569505946080378880, coefficient := (-2060245802569505946080378880) }, { argument := 2059773390677150281318268928, coefficient := (-2059773390677150281318268928) }, { argument := 42708931355345619484019785728, coefficient := (-42708931355345619484019785728) }, { argument := 1856910058928070412348686336, coefficient := (-1856910058928070412348686336) }, { argument := 2466458000512586783913934848, coefficient := (-2466458000512586783913934848) }, { argument := 2465959343515100248887263232, coefficient := (-2465959343515100248887263232) }, { argument := 51993481649985971545763217408, coefficient := (-51993481649985971545763217408) }, { argument := 41625733820970911743483052032, coefficient := (-41625733820970911743483052032) }, { argument := 72313517671952668373358215168, coefficient := (-72313517671952668373358215168) }, { argument := 4295117146223298269621204635615232, coefficient := 4295117146223298269621204635615232 }, { argument := 1547425049106725343623905280, coefficient := 1547425049106725343623905280 }, { argument := 25996740824992985772881608704, coefficient := 25996740824992985772881608704 }, { argument := 56326271787484802507910152192, coefficient := 56326271787484802507910152192 }, { argument := 1856910058928070412348686336, coefficient := 1856910058928070412348686336 }, { argument := 29710560942849126597578981376, coefficient := 29710560942849126597578981376 }, { argument := 2166395068749415481073467392, coefficient := 2166395068749415481073467392 }, { argument := 56326271787484802507910152192, coefficient := 56326271787484802507910152192 }, { argument := 56326271787484802507910152192, coefficient := 56326271787484802507910152192 }, { argument := 29710560942849126597578981376, coefficient := 29710560942849126597578981376 }, { argument := 695103332058741024355858251776, coefficient := 695103332058741024355858251776 }, { argument := 55707301767842112370460590080, coefficient := 55707301767842112370460590080 }, { argument := 25996740824992985772881608704, coefficient := 25996740824992985772881608704 }, { argument := 56326271787484802507910152192, coefficient := 56326271787484802507910152192 }, { argument := 2166395068749415481073467392, coefficient := 2166395068749415481073467392 }, { argument := 55707301767842112370460590080, coefficient := 55707301767842112370460590080 }, { argument := 2166395068749415481073467392, coefficient := 2166395068749415481073467392 }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15
