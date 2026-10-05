import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 4, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-103772047123053274049083254767616)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    257071671147, 9177, 9177, 310569, 16905, 561729,
    310569, 7279310997, 17871, 16905, 22701, 465873965,
    790320091, 465873949, 3441, 41181, 61605, 17871,
    3441, 71373, 35853, 3441, 41181, 3441,
    14541435, 1222778245, 611388975, 7270865, 3255, 38955,
    58275, 16905, 3255, 67515, 33915, 3255,
    38955, 3255, 8724861, 733666947, 366833385, 4362519,
    479535, 35412405, 369097575, 35412405, 479535, 14541435,
    1222778245, 611388975, 7270865, 205515, 15176745, 158184675,
    15176745, 205515, 28595859, 4371, 995789421, 108159,
    3441, 7966318293, 1767, 1767
  ]
def negativeCoefficients : Array ℕ := #[
    592766915781191622677646802944, 346697257706357873008705536, 346697257706357873008705536, 5866482544873371377489412096, 319326421571645409350123520, 10610760808223531744976961536,
    5866482544873371377489412096, 16784948374324814707785990144, 337573645661453718455844864, 319326421571645409350123520, 428809766110495263984451584, 34375431211837284278872309760,
    116630659639902748325810536448, 34375430031245663561461006336, 16249663067554449180327936, 388943548262109719090429952, 290921387177184493389742080, 337573645661453718455844864,
    16249663067554449180327936, 337049462981855187837124608, 338622011020650779693285376, 16249663067554449180327936, 388943548262109719090429952, 16249663067554449180327936,
    67060532477370663425802240, 5639069336103679041187348480, 5639067975656303605107916800, 67061892924746099505233920, 15371302901740695170580480, 367919572680374058599055360,
    275195906789228574828134400, 319326421571645409350123520, 15371302901740695170580480, 318830573090944096602685440, 320318118533048034844999680, 15371302901740695170580480,
    367919572680374058599055360, 15371302901740695170580480, 1287562223565516737775403008, 108270131253190637590797090816, 108270105132601029218072002560, 1287588344155125110500491264,
    141533750710180957346856960, 20903794306225679814214287360, 217876752136058136185693798400, 20903794306225679814214287360, 141533750710180957346856960, 67060532477370663425802240,
    5639069336103679041187348480, 5639067975656303605107916800, 67061892924746099505233920, 121314643465869392011591680, 17917537976764868412183674880, 186751501830906973873451827200,
    17917537976764868412183674880, 121314643465869392011591680, 527500492540883944964358144, 20641463896623219229065216, 18369072600494415725866254336, 510766436420697956668145664,
    16249663067554449180327936, 18369079345085217675921063936, 16688843150461326185201664, 16688843150461326185201664
  ]
def negativeScales : Array ℕ := #[
    37, 13, 13, 18, 14, 19,
    18, 32, 14, 14, 14, 28,
    29, 28, 11, 15, 15, 14,
    11, 16, 15, 11, 15, 11,
    23, 30, 29, 22, 11, 15,
    15, 14, 11, 16, 15, 11,
    15, 11, 23, 29, 28, 22,
    18, 25, 28, 25, 18, 23,
    30, 29, 22, 17, 23, 27,
    23, 17, 24, 12, 29, 16,
    11, 32, 10, 10
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    37903379684836313, 13163806892279359, 13163806892279359, 18244554306163721, 14045162395780740, 19099514760308992,
    18244554306163721, 32761154756859702, 14125332744464723, 14045162395780740, 14470468230513509, 28795364468508291,
    29557861842984200, 28795364418960295, 11748612176955137, 15329691242970910, 15910759832877788, 14125332744464723,
    11748612176955137, 16123090793678054, 15129806221044031, 11748612176955137, 15329691242970910, 11748612176955137,
    23793666311287512, 30187515643913075, 29187515295857252, 22793695578737739, 11668441828086828, 15249520894286927,
    15830589480093830, 14045162395780740, 11668441828086828, 16042920444994070, 15049635872360048, 11668441828086828,
    15249520894286927, 11668441828086828, 23056700716553848, 29450550049746917, 28450549701691094, 22056729984003733,
    18871276594630224, 25077751490537107, 28459427018094118, 25077751490537107, 18871276594630224, 23793666311287512,
    30187515643913075, 29187515295857252, 22793695578737739, 17648884170728738, 23855359071118675, 27237034596757604,
    23855359071118675, 17648884170728738, 24769302908314568, 12093747662785669, 29891265451510100, 16722794192703879,
    11748612176955137, 32891265981225823, 10787086325046961, 10787086325046961
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
noncomputable def negativeCeiling : ℝ := 151464467 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 592766915781191622677646802944, coefficient := (-592766915781191622677646802944) }, { argument := 346697257706357873008705536, coefficient := (-346697257706357873008705536) }, { argument := 346697257706357873008705536, coefficient := (-346697257706357873008705536) }, { argument := 5866482544873371377489412096, coefficient := (-5866482544873371377489412096) }, { argument := 319326421571645409350123520, coefficient := (-319326421571645409350123520) }, { argument := 10610760808223531744976961536, coefficient := (-10610760808223531744976961536) }, { argument := 5866482544873371377489412096, coefficient := (-5866482544873371377489412096) }, { argument := 16784948374324814707785990144, coefficient := (-16784948374324814707785990144) }, { argument := 337573645661453718455844864, coefficient := (-337573645661453718455844864) }, { argument := 319326421571645409350123520, coefficient := (-319326421571645409350123520) }, { argument := 428809766110495263984451584, coefficient := (-428809766110495263984451584) }, { argument := 34375431211837284278872309760, coefficient := (-34375431211837284278872309760) }, { argument := 116630659639902748325810536448, coefficient := (-116630659639902748325810536448) }, { argument := 34375430031245663561461006336, coefficient := (-34375430031245663561461006336) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 388943548262109719090429952, coefficient := (-388943548262109719090429952) }, { argument := 290921387177184493389742080, coefficient := (-290921387177184493389742080) }, { argument := 337573645661453718455844864, coefficient := (-337573645661453718455844864) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 337049462981855187837124608, coefficient := (-337049462981855187837124608) }, { argument := 338622011020650779693285376, coefficient := (-338622011020650779693285376) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 388943548262109719090429952, coefficient := (-388943548262109719090429952) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 67060532477370663425802240, coefficient := (-67060532477370663425802240) }, { argument := 5639069336103679041187348480, coefficient := (-5639069336103679041187348480) }, { argument := 5639067975656303605107916800, coefficient := (-5639067975656303605107916800) }, { argument := 67061892924746099505233920, coefficient := (-67061892924746099505233920) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 367919572680374058599055360, coefficient := (-367919572680374058599055360) }, { argument := 275195906789228574828134400, coefficient := (-275195906789228574828134400) }, { argument := 319326421571645409350123520, coefficient := (-319326421571645409350123520) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 318830573090944096602685440, coefficient := (-318830573090944096602685440) }, { argument := 320318118533048034844999680, coefficient := (-320318118533048034844999680) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 367919572680374058599055360, coefficient := (-367919572680374058599055360) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 1287562223565516737775403008, coefficient := (-1287562223565516737775403008) }, { argument := 108270131253190637590797090816, coefficient := (-108270131253190637590797090816) }, { argument := 108270105132601029218072002560, coefficient := (-108270105132601029218072002560) }, { argument := 1287588344155125110500491264, coefficient := (-1287588344155125110500491264) }, { argument := 141533750710180957346856960, coefficient := (-141533750710180957346856960) }, { argument := 20903794306225679814214287360, coefficient := (-20903794306225679814214287360) }, { argument := 217876752136058136185693798400, coefficient := (-217876752136058136185693798400) }, { argument := 20903794306225679814214287360, coefficient := (-20903794306225679814214287360) }, { argument := 141533750710180957346856960, coefficient := (-141533750710180957346856960) }, { argument := 67060532477370663425802240, coefficient := (-67060532477370663425802240) }, { argument := 5639069336103679041187348480, coefficient := (-5639069336103679041187348480) }, { argument := 5639067975656303605107916800, coefficient := (-5639067975656303605107916800) }, { argument := 67061892924746099505233920, coefficient := (-67061892924746099505233920) }, { argument := 121314643465869392011591680, coefficient := (-121314643465869392011591680) }, { argument := 17917537976764868412183674880, coefficient := (-17917537976764868412183674880) }, { argument := 186751501830906973873451827200, coefficient := (-186751501830906973873451827200) }, { argument := 17917537976764868412183674880, coefficient := (-17917537976764868412183674880) }, { argument := 121314643465869392011591680, coefficient := (-121314643465869392011591680) }, { argument := 527500492540883944964358144, coefficient := (-527500492540883944964358144) }, { argument := 20641463896623219229065216, coefficient := (-20641463896623219229065216) }, { argument := 18369072600494415725866254336, coefficient := (-18369072600494415725866254336) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 18369079345085217675921063936, coefficient := (-18369079345085217675921063936) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }] }

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


end Parent0

namespace Parent0

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-400874914156045844644261359779840)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    59799, 3255, 108159, 59799, 228763947, 3441,
    3255, 4371, 4371, 52311, 78255, 22701,
    4371, 90663, 45543, 4371, 52311, 4371,
    223938099, 18830784973, 9415390215, 111971321, 479535, 35412405,
    369097575, 35412405, 479535, 253020969, 21276341463, 10638168165,
    126513051, 5411895, 399654285, 4165529775, 399654285, 5411895,
    909888813, 90663, 32133918675, 2243427, 71373, 257071443819,
    36651, 36651, 1240347, 67515, 2243427, 1240347,
    7279016085, 71373, 67515, 90663, 205515, 15176745,
    158184675, 15176745, 205515, 615702441, 45543, 21468584535,
    1126947, 35853, 171748739343, 18411
  ]
def negativeCoefficients : Array ℕ := #[
    282392793309121914133807104, 15371302901740695170580480, 510766436420697956668145664, 282392793309121914133807104, 527493747950081994909548544, 16249663067554449180327936,
    15371302901740695170580480, 20641463896623219229065216, 20641463896623219229065216, 494063426170788021547302912, 369548789116964086197780480, 428809766110495263984451584,
    20641463896623219229065216, 428143912436410644009320448, 430141473458664503934713856, 20641463896623219229065216, 494063426170788021547302912, 20641463896623219229065216,
    2065464400303016433514708992, 173683335551993314468570333184, 173683293650214151037323837440, 2065506302082179864761204736, 141533750710180957346856960, 20903794306225679814214287360,
    217876752136058136185693798400, 20903794306225679814214287360, 141533750710180957346856960, 1166853265106249543608958976, 98119806448204015316659863552, 98119782776419682728877752320,
    1166876936890582131391070208, 1597309472300613661485957120, 235914250027404100760418385920, 2458894774106941822667115724800, 235914250027404100760418385920, 1597309472300613661485957120,
    16784486068942368426644471808, 428143912436410644009320448, 592766173883120937199258828800, 10594284471564799552826376192, 337049462981855187837124608, 592766391598512024147028082688,
    346158907927310733454344192, 346158907927310733454344192, 5857373099927915831872192512, 318830573090944096602685440, 10594284471564799552826376192, 5857373099927915831872192512,
    16784268353551281478875217920, 337049462981855187837124608, 318830573090944096602685440, 428143912436410644009320448, 121314643465869392011591680, 17917537976764868412183674880,
    186751501830906973873451827200, 17917537976764868412183674880, 121314643465869392011591680, 11357705354685254854986694656, 430141473458664503934713856, 396025484541943779905041858560,
    10643713481540996129278132224, 338622011020650779693285376, 396025629955321469948223553536, 347773957264452152117428224
  ]
def negativeScales : Array ℕ := #[
    15, 11, 16, 15, 27, 11,
    11, 12, 12, 15, 16, 14,
    12, 16, 15, 12, 15, 12,
    27, 34, 33, 26, 18, 25,
    28, 25, 18, 27, 34, 33,
    26, 22, 28, 31, 28, 22,
    29, 16, 34, 21, 16, 37,
    15, 15, 20, 16, 21, 20,
    32, 16, 16, 16, 17, 23,
    27, 23, 17, 29, 15, 34,
    20, 15, 37, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15867833740861174, 11668441828086828, 16722794192703879, 15867833740861174, 27769284461981119, 11748612176955137,
    11668441828086828, 12093747662785669, 12093747662785669, 15674826729059175, 16255895313636262, 14470468230513509,
    12093747662785669, 16468226279726832, 15474941707092834, 12093747662785669, 15674826729059175, 12093747662785669,
    27738524756702229, 34132374089720614, 33132373741664791, 26738554024152229, 18871276594630224, 25077751490537107,
    28459427018094118, 25077751490537107, 18871276594630224, 27914681717350857, 34308531044874441, 33308530696818618,
    26914710984803665, 22367702418163978, 28574177316659328, 31955852855716562, 28574177316659328, 22367702418163978,
    29761115020373351, 16468226279726832, 34903377879179827, 21097272809522322, 16123090793678054, 37903378409063106,
    15161564941492690, 15161564941492690, 20242312355377051, 16042920444994070, 21097272809522322, 20242312355377051,
    32761096306725949, 16123090793678054, 16042920444994070, 16468226279726832, 17648884170728738, 23855359071118675,
    27237034596757604, 23855359071118675, 17648884170728738, 29197658047339433, 15474941707092834, 34321508023551734,
    20103988236888300, 15129806221044031, 37321508553283098, 14168280368858667
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
noncomputable def negativeCeiling : ℝ := 1190287173 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 527493747950081994909548544, coefficient := (-527493747950081994909548544) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 20641463896623219229065216, coefficient := (-20641463896623219229065216) }, { argument := 20641463896623219229065216, coefficient := (-20641463896623219229065216) }, { argument := 494063426170788021547302912, coefficient := (-494063426170788021547302912) }, { argument := 369548789116964086197780480, coefficient := (-369548789116964086197780480) }, { argument := 428809766110495263984451584, coefficient := (-428809766110495263984451584) }, { argument := 20641463896623219229065216, coefficient := (-20641463896623219229065216) }, { argument := 428143912436410644009320448, coefficient := (-428143912436410644009320448) }, { argument := 430141473458664503934713856, coefficient := (-430141473458664503934713856) }, { argument := 20641463896623219229065216, coefficient := (-20641463896623219229065216) }, { argument := 494063426170788021547302912, coefficient := (-494063426170788021547302912) }, { argument := 20641463896623219229065216, coefficient := (-20641463896623219229065216) }, { argument := 2065464400303016433514708992, coefficient := (-2065464400303016433514708992) }, { argument := 173683335551993314468570333184, coefficient := (-173683335551993314468570333184) }, { argument := 173683293650214151037323837440, coefficient := (-173683293650214151037323837440) }, { argument := 2065506302082179864761204736, coefficient := (-2065506302082179864761204736) }, { argument := 141533750710180957346856960, coefficient := (-141533750710180957346856960) }, { argument := 20903794306225679814214287360, coefficient := (-20903794306225679814214287360) }, { argument := 217876752136058136185693798400, coefficient := (-217876752136058136185693798400) }, { argument := 20903794306225679814214287360, coefficient := (-20903794306225679814214287360) }, { argument := 141533750710180957346856960, coefficient := (-141533750710180957346856960) }, { argument := 1166853265106249543608958976, coefficient := (-1166853265106249543608958976) }, { argument := 98119806448204015316659863552, coefficient := (-98119806448204015316659863552) }, { argument := 98119782776419682728877752320, coefficient := (-98119782776419682728877752320) }, { argument := 1166876936890582131391070208, coefficient := (-1166876936890582131391070208) }, { argument := 1597309472300613661485957120, coefficient := (-1597309472300613661485957120) }, { argument := 235914250027404100760418385920, coefficient := (-235914250027404100760418385920) }, { argument := 2458894774106941822667115724800, coefficient := (-2458894774106941822667115724800) }, { argument := 235914250027404100760418385920, coefficient := (-235914250027404100760418385920) }, { argument := 1597309472300613661485957120, coefficient := (-1597309472300613661485957120) }, { argument := 16784486068942368426644471808, coefficient := (-16784486068942368426644471808) }, { argument := 428143912436410644009320448, coefficient := (-428143912436410644009320448) }, { argument := 592766173883120937199258828800, coefficient := (-592766173883120937199258828800) }, { argument := 10594284471564799552826376192, coefficient := (-10594284471564799552826376192) }, { argument := 337049462981855187837124608, coefficient := (-337049462981855187837124608) }, { argument := 592766391598512024147028082688, coefficient := (-592766391598512024147028082688) }, { argument := 346158907927310733454344192, coefficient := (-346158907927310733454344192) }, { argument := 346158907927310733454344192, coefficient := (-346158907927310733454344192) }, { argument := 5857373099927915831872192512, coefficient := (-5857373099927915831872192512) }, { argument := 318830573090944096602685440, coefficient := (-318830573090944096602685440) }, { argument := 10594284471564799552826376192, coefficient := (-10594284471564799552826376192) }, { argument := 5857373099927915831872192512, coefficient := (-5857373099927915831872192512) }, { argument := 16784268353551281478875217920, coefficient := (-16784268353551281478875217920) }, { argument := 337049462981855187837124608, coefficient := (-337049462981855187837124608) }, { argument := 318830573090944096602685440, coefficient := (-318830573090944096602685440) }, { argument := 428143912436410644009320448, coefficient := (-428143912436410644009320448) }, { argument := 121314643465869392011591680, coefficient := (-121314643465869392011591680) }, { argument := 17917537976764868412183674880, coefficient := (-17917537976764868412183674880) }, { argument := 186751501830906973873451827200, coefficient := (-186751501830906973873451827200) }, { argument := 17917537976764868412183674880, coefficient := (-17917537976764868412183674880) }, { argument := 121314643465869392011591680, coefficient := (-121314643465869392011591680) }, { argument := 11357705354685254854986694656, coefficient := (-11357705354685254854986694656) }, { argument := 430141473458664503934713856, coefficient := (-430141473458664503934713856) }, { argument := 396025484541943779905041858560, coefficient := (-396025484541943779905041858560) }, { argument := 10643713481540996129278132224, coefficient := (-10643713481540996129278132224) }, { argument := 338622011020650779693285376, coefficient := (-338622011020650779693285376) }, { argument := 396025629955321469948223553536, coefficient := (-396025629955321469948223553536) }, { argument := 347773957264452152117428224, coefficient := (-347773957264452152117428224) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4
