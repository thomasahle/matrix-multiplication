import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 13, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-17106194823599604871949435292090368)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    61457, 60007, 70631, 82901, 1500369, 1153477,
    17734587, 1365143, 1153477, 686309, 686309, 51433421,
    1350193, 17734587, 51433421, 82901, 1365143, 1350193,
    1500369, 16091027282692897, 28072394719698143, 16091027248528161, 289, 9857,
    30599, 667169, 16983, 30599, 2151, 2151,
    257763, 16533, 667169, 257763, 289, 16983,
    16533, 9857, 134912886925, 471844658069, 67456421359, 468611032126997,
    468610919459307, 499944716112167, 64208553707745333, 34150809083, 668004314325386175, 26333149929,
    76064533, 34150809083, 26954044673, 26333149929, 482820901469, 6935868045,
    32104284271934019, 34150809083, 76064533, 6935868045, 76064533, 4282481371,
    26954044673, 501511021381215, 8015269756938499, 70631
  ]
def negativeCoefficients : Array ℕ := #[
    290222476937719785898115072, 283375045537558800338255872, 333545467051565911088562176, 6263822460742023325769793536, 7085292277536646719627853824, 5447141123561029752158420992,
    83749219236335732701425303552, 6446705547524116075960598528, 5447141123561029752158420992, 6482005236983566673932976128, 6482005236983566673932976128, 242887463429723750396661334016,
    6376106168605214880015843328, 83749219236335732701425303552, 242887463429723750396661334016, 6263822460742023325769793536, 6446705547524116075960598528, 6376106168605214880015843328,
    7085292277536646719627853824, 18116886118586053932219501641728, 63213413199515018160730972094464, 18116886080119980852516659134464, 349379561868627831490084864, 372386931373168742971211776,
    288999384018656547787767808, 6301233048019316655152693248, 320799799914300738656796672, 288999384018656547787767808, 325049929748883419349123072, 325049929748883419349123072,
    9738010813791426873743376384, 312299540245135377272143872, 6301233048019316655152693248, 9738010813791426873743376384, 349379561868627831490084864, 320799799914300738656796672,
    312299540245135377272143872, 372386931373168742971211776, 155543968584424412653866188800, 543999853121614719666926649344, 155543917617223458498981920768, 263804558708605902348630360064,
    263804495282335064761810550784, 140721927324287731806400151552, 18073101159512522564018475368448, 157492808766054144207887532032, 188026498817355803800078437580800, 121440219348721462475873058816,
    5612571893348938485241741312, 157492808766054144207887532032, 124303590958541314771115835392, 121440219348721462475873058816, 2226618400709094773528226430976, 127944182755135203664692510720,
    18073105335509815430328172412928, 157492808766054144207887532032, 5612571893348938485241741312, 127944182755135203664692510720, 5612571893348938485241741312, 157995675702531611320565891072,
    124303590958541314771115835392, 141162803063414795386528727040, 18048782945311115071103279562752, 333545467051565911088562176
  ]
def negativeScales : Array ℕ := #[
    15, 15, 16, 16, 20, 20,
    24, 20, 20, 19, 19, 25,
    20, 24, 25, 16, 20, 20,
    20, 53, 54, 53, 8, 13,
    14, 19, 14, 14, 11, 11,
    17, 14, 19, 17, 8, 14,
    14, 13, 36, 38, 35, 48,
    48, 48, 55, 34, 59, 34,
    26, 34, 34, 34, 38, 32,
    54, 34, 26, 32, 26, 31,
    34, 48, 52, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15907289728565838, 15872843187536501, 16108013902001033, 16339101884000748, 20516885929379953, 20137557806707222,
    24080062397642820, 20380620652033502, 20137557806707222, 19388498748206514, 19388498748206514, 25616202779326119,
    20364734213816189, 24080062397642820, 25616202779326119, 16339101884000748, 20380620652033502, 20364734213816189,
    20516885929379953, 53837105953027435, 54640001656623695, 53837105949964281, 8174925682500679, 13266932910607358,
    14901196889262501, 19347692729968054, 14051803709042758, 14901196889262501, 11070791809423061, 11070791809423061,
    17975685680621011, 14013060912553662, 19347692729968054, 17975685680621011, 8174925682500679, 14051803709042758,
    14013060912553662, 13266932910607358, 36973237220703773, 38779521014108729, 35973236747974683, 48735384247378424,
    48735383900512630, 48828761900057871, 55833615021944074, 34991200727928511, 59212635033502661, 34616161053446810,
    26180720581904095, 34991200727928511, 34649782726208231, 34616161053446810, 38812697176763901, 32691429305570065,
    54833615355295278, 34991200727928511, 26180720581904095, 32691429305570065, 26180720581904095, 31995799846655602,
    34649782726208231, 48833274736032941, 52831672500170909, 16108013902001033
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
noncomputable def negativeCeiling : ℝ := 9493043711 / 40000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 290222476937719785898115072, coefficient := (-290222476937719785898115072) }, { argument := 283375045537558800338255872, coefficient := (-283375045537558800338255872) }, { argument := 333545467051565911088562176, coefficient := (-333545467051565911088562176) }, { argument := 6263822460742023325769793536, coefficient := (-6263822460742023325769793536) }, { argument := 7085292277536646719627853824, coefficient := (-7085292277536646719627853824) }, { argument := 5447141123561029752158420992, coefficient := (-5447141123561029752158420992) }, { argument := 83749219236335732701425303552, coefficient := (-83749219236335732701425303552) }, { argument := 6446705547524116075960598528, coefficient := (-6446705547524116075960598528) }, { argument := 5447141123561029752158420992, coefficient := (-5447141123561029752158420992) }, { argument := 6482005236983566673932976128, coefficient := (-6482005236983566673932976128) }, { argument := 6482005236983566673932976128, coefficient := (-6482005236983566673932976128) }, { argument := 242887463429723750396661334016, coefficient := (-242887463429723750396661334016) }, { argument := 6376106168605214880015843328, coefficient := (-6376106168605214880015843328) }, { argument := 83749219236335732701425303552, coefficient := (-83749219236335732701425303552) }, { argument := 242887463429723750396661334016, coefficient := (-242887463429723750396661334016) }, { argument := 6263822460742023325769793536, coefficient := (-6263822460742023325769793536) }, { argument := 6446705547524116075960598528, coefficient := (-6446705547524116075960598528) }, { argument := 6376106168605214880015843328, coefficient := (-6376106168605214880015843328) }, { argument := 7085292277536646719627853824, coefficient := (-7085292277536646719627853824) }, { argument := 18116886118586053932219501641728, coefficient := (-18116886118586053932219501641728) }, { argument := 63213413199515018160730972094464, coefficient := (-63213413199515018160730972094464) }, { argument := 18116886080119980852516659134464, coefficient := (-18116886080119980852516659134464) }, { argument := 349379561868627831490084864, coefficient := (-349379561868627831490084864) }, { argument := 372386931373168742971211776, coefficient := (-372386931373168742971211776) }, { argument := 288999384018656547787767808, coefficient := (-288999384018656547787767808) }, { argument := 6301233048019316655152693248, coefficient := (-6301233048019316655152693248) }, { argument := 320799799914300738656796672, coefficient := (-320799799914300738656796672) }, { argument := 288999384018656547787767808, coefficient := (-288999384018656547787767808) }, { argument := 325049929748883419349123072, coefficient := (-325049929748883419349123072) }, { argument := 325049929748883419349123072, coefficient := (-325049929748883419349123072) }, { argument := 9738010813791426873743376384, coefficient := (-9738010813791426873743376384) }, { argument := 312299540245135377272143872, coefficient := (-312299540245135377272143872) }, { argument := 6301233048019316655152693248, coefficient := (-6301233048019316655152693248) }, { argument := 9738010813791426873743376384, coefficient := (-9738010813791426873743376384) }, { argument := 349379561868627831490084864, coefficient := (-349379561868627831490084864) }, { argument := 320799799914300738656796672, coefficient := (-320799799914300738656796672) }, { argument := 312299540245135377272143872, coefficient := (-312299540245135377272143872) }, { argument := 372386931373168742971211776, coefficient := (-372386931373168742971211776) }, { argument := 155543968584424412653866188800, coefficient := (-155543968584424412653866188800) }, { argument := 543999853121614719666926649344, coefficient := (-543999853121614719666926649344) }, { argument := 155543917617223458498981920768, coefficient := (-155543917617223458498981920768) }, { argument := 263804558708605902348630360064, coefficient := (-263804558708605902348630360064) }, { argument := 263804495282335064761810550784, coefficient := (-263804495282335064761810550784) }, { argument := 140721927324287731806400151552, coefficient := (-140721927324287731806400151552) }, { argument := 18073101159512522564018475368448, coefficient := (-18073101159512522564018475368448) }, { argument := 157492808766054144207887532032, coefficient := (-157492808766054144207887532032) }, { argument := 188026498817355803800078437580800, coefficient := (-188026498817355803800078437580800) }, { argument := 121440219348721462475873058816, coefficient := (-121440219348721462475873058816) }, { argument := 5612571893348938485241741312, coefficient := (-5612571893348938485241741312) }, { argument := 157492808766054144207887532032, coefficient := (-157492808766054144207887532032) }, { argument := 124303590958541314771115835392, coefficient := (-124303590958541314771115835392) }, { argument := 121440219348721462475873058816, coefficient := (-121440219348721462475873058816) }, { argument := 2226618400709094773528226430976, coefficient := (-2226618400709094773528226430976) }, { argument := 127944182755135203664692510720, coefficient := (-127944182755135203664692510720) }, { argument := 18073105335509815430328172412928, coefficient := (-18073105335509815430328172412928) }, { argument := 157492808766054144207887532032, coefficient := (-157492808766054144207887532032) }, { argument := 5612571893348938485241741312, coefficient := (-5612571893348938485241741312) }, { argument := 127944182755135203664692510720, coefficient := (-127944182755135203664692510720) }, { argument := 5612571893348938485241741312, coefficient := (-5612571893348938485241741312) }, { argument := 157995675702531611320565891072, coefficient := (-157995675702531611320565891072) }, { argument := 124303590958541314771115835392, coefficient := (-124303590958541314771115835392) }, { argument := 141162803063414795386528727040, coefficient := (-141162803063414795386528727040) }, { argument := 18048782945311115071103279562752, coefficient := (-18048782945311115071103279562752) }, { argument := 333545467051565911088562176, coefficient := (-333545467051565911088562176) }] }

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


end Parent0

namespace Parent0

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-123294134436819333566128490761158656)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    589528006850707815, 1130813, 61457, 294754270404509245, 31091, 31091,
    1949579, 60007, 1130813, 1949579, 16050014090539033, 61457,
    60007, 70631, 83704901880646933, 146108480762650091, 83704901879904021, 1169,
    19961, 121, 41941, 17217, 121, 8721,
    8721, 525549, 16767, 41941, 525549, 1169,
    17217, 16767, 19961, 104440997905, 367935501867, 26110240881,
    33167447299484139, 33167437865915925, 4803116545, 8383776017, 4803114973, 1015,
    1015, 13609059, 1169, 19961, 121, 41941,
    17217, 121, 8721, 8721, 525549, 16767,
    41941, 525549, 1169, 17217, 16767, 19961,
    74543, 1223567, 477793, 12458083
  ]
def negativeCoefficients : Array ℕ := #[
    663749527994329732186536211906560, 5340113409593272113035214848, 290222476937719785898115072, 663727611179805126533920336117760, 293646192637800278678044672, 293646192637800278678044672,
    9206626525306520046072233984, 283375045537558800338255872, 5340113409593272113035214848, 9206626525306520046072233984, 18070709369360699817057260142592, 290222476937719785898115072,
    283375045537558800338255872, 333545467051565911088562176, 188486682459382728652333078544384, 658014099518340233047754865115136, 188486682457709839549148543582208, 353308570782375376307879936,
    377052629458243952442343424, 292560048346740260278894592, 6337944725057145277043965952, 325219934942266726576816128, 292560048346740260278894592, 329470064776849407269142528,
    329470064776849407269142528, 9927339930822636689650876416, 316719675273101365192163328, 6337944725057145277043965952, 9927339930822636689650876416, 353308570782375376307879936,
    325219934942266726576816128, 316719675273101365192163328, 377052629458243952442343424, 120412272447273152869071585280, 424200752410776994639031304192, 120412232808678902981065703424,
    18671612912348416530935728570368, 18671607601721629862866295193600, 5537616353863440430708817920, 19331671319612877382755549184, 5537614541470835188745371648, 39265910621083155594456596480,
    39265910621083155594456596480, 64266964084995491022256472064, 353308570782375376307879936, 377052629458243952442343424, 292560048346740260278894592, 6337944725057145277043965952,
    325219934942266726576816128, 292560048346740260278894592, 329470064776849407269142528, 329470064776849407269142528, 9927339930822636689650876416, 316719675273101365192163328,
    6337944725057145277043965952, 9927339930822636689650876416, 353308570782375376307879936, 325219934942266726576816128, 316719675273101365192163328, 377052629458243952442343424,
    11264619671441662821265309696, 11556263580690726370372747264, 9025254595798945582349811712, 235326534400032473011110019072
  ]
def negativeScales : Array ℕ := #[
    59, 20, 15, 58, 14, 14,
    20, 15, 20, 20, 53, 15,
    15, 16, 56, 57, 56, 10,
    14, 6, 15, 14, 6, 13,
    13, 19, 14, 15, 19, 10,
    14, 14, 14, 36, 38, 34,
    54, 54, 32, 32, 32, 9,
    9, 23, 10, 14, 6, 15,
    14, 6, 13, 13, 19, 14,
    15, 19, 10, 14, 14, 14,
    16, 20, 18, 23
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    59032337966383224, 20108928943145099, 15907289728565838, 58032290328230074, 14924209406009814, 14924209406009814,
    20894731189483595, 15872843187536501, 20108928943145099, 20894731189483595, 53833424083366750, 15907289728565838,
    15872843187536501, 16108013902001033, 56216161629764641, 57019817533862581, 56216161629751836, 10191059214531657,
    14284896377724746, 6918863243376152, 15356073639597253, 14071546159788425, 6918863243376152, 13090277856857394,
    13090277856857394, 19003465755772477, 14033336960383950, 15356073639597253, 19003465755772477, 10191059214531657,
    14071546159788425, 14033336960383950, 14284896377724746, 36603897191150715, 38420661931532529, 34603896716228918,
    54880617502039993, 54880617091704984, 32161323669193615, 32964953041373573, 32161323197017486, 9987264031369531,
    9987264031369531, 23698063979251387, 10191059214531657, 14284896377724746, 6918863243376152, 15356073639597253,
    14071546159788425, 6918863243376152, 13090277856857394, 13090277856857394, 19003465755772477, 14033336960383950,
    15356073639597253, 19003465755772477, 10191059214531657, 14071546159788425, 14033336960383950, 14284896377724746,
    16185785261374854, 20222661671903083, 18866026194244076, 23570578753509629
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
noncomputable def negativeCeiling : ℝ := 1678815870739 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 663749527994329732186536211906560, coefficient := (-663749527994329732186536211906560) }, { argument := 5340113409593272113035214848, coefficient := (-5340113409593272113035214848) }, { argument := 290222476937719785898115072, coefficient := (-290222476937719785898115072) }, { argument := 663727611179805126533920336117760, coefficient := (-663727611179805126533920336117760) }, { argument := 293646192637800278678044672, coefficient := (-293646192637800278678044672) }, { argument := 293646192637800278678044672, coefficient := (-293646192637800278678044672) }, { argument := 9206626525306520046072233984, coefficient := (-9206626525306520046072233984) }, { argument := 283375045537558800338255872, coefficient := (-283375045537558800338255872) }, { argument := 5340113409593272113035214848, coefficient := (-5340113409593272113035214848) }, { argument := 9206626525306520046072233984, coefficient := (-9206626525306520046072233984) }, { argument := 18070709369360699817057260142592, coefficient := (-18070709369360699817057260142592) }, { argument := 290222476937719785898115072, coefficient := (-290222476937719785898115072) }, { argument := 283375045537558800338255872, coefficient := (-283375045537558800338255872) }, { argument := 333545467051565911088562176, coefficient := (-333545467051565911088562176) }, { argument := 188486682459382728652333078544384, coefficient := (-188486682459382728652333078544384) }, { argument := 658014099518340233047754865115136, coefficient := (-658014099518340233047754865115136) }, { argument := 188486682457709839549148543582208, coefficient := (-188486682457709839549148543582208) }, { argument := 353308570782375376307879936, coefficient := (-353308570782375376307879936) }, { argument := 377052629458243952442343424, coefficient := (-377052629458243952442343424) }, { argument := 292560048346740260278894592, coefficient := (-292560048346740260278894592) }, { argument := 6337944725057145277043965952, coefficient := (-6337944725057145277043965952) }, { argument := 325219934942266726576816128, coefficient := (-325219934942266726576816128) }, { argument := 292560048346740260278894592, coefficient := (-292560048346740260278894592) }, { argument := 329470064776849407269142528, coefficient := (-329470064776849407269142528) }, { argument := 329470064776849407269142528, coefficient := (-329470064776849407269142528) }, { argument := 9927339930822636689650876416, coefficient := (-9927339930822636689650876416) }, { argument := 316719675273101365192163328, coefficient := (-316719675273101365192163328) }, { argument := 6337944725057145277043965952, coefficient := (-6337944725057145277043965952) }, { argument := 9927339930822636689650876416, coefficient := (-9927339930822636689650876416) }, { argument := 353308570782375376307879936, coefficient := (-353308570782375376307879936) }, { argument := 325219934942266726576816128, coefficient := (-325219934942266726576816128) }, { argument := 316719675273101365192163328, coefficient := (-316719675273101365192163328) }, { argument := 377052629458243952442343424, coefficient := (-377052629458243952442343424) }, { argument := 120412272447273152869071585280, coefficient := (-120412272447273152869071585280) }, { argument := 424200752410776994639031304192, coefficient := (-424200752410776994639031304192) }, { argument := 120412232808678902981065703424, coefficient := (-120412232808678902981065703424) }, { argument := 18671612912348416530935728570368, coefficient := (-18671612912348416530935728570368) }, { argument := 18671607601721629862866295193600, coefficient := (-18671607601721629862866295193600) }, { argument := 5537616353863440430708817920, coefficient := (-5537616353863440430708817920) }, { argument := 19331671319612877382755549184, coefficient := (-19331671319612877382755549184) }, { argument := 5537614541470835188745371648, coefficient := (-5537614541470835188745371648) }, { argument := 39265910621083155594456596480, coefficient := (-39265910621083155594456596480) }, { argument := 39265910621083155594456596480, coefficient := (-39265910621083155594456596480) }, { argument := 64266964084995491022256472064, coefficient := (-64266964084995491022256472064) }, { argument := 353308570782375376307879936, coefficient := (-353308570782375376307879936) }, { argument := 377052629458243952442343424, coefficient := (-377052629458243952442343424) }, { argument := 292560048346740260278894592, coefficient := (-292560048346740260278894592) }, { argument := 6337944725057145277043965952, coefficient := (-6337944725057145277043965952) }, { argument := 325219934942266726576816128, coefficient := (-325219934942266726576816128) }, { argument := 292560048346740260278894592, coefficient := (-292560048346740260278894592) }, { argument := 329470064776849407269142528, coefficient := (-329470064776849407269142528) }, { argument := 329470064776849407269142528, coefficient := (-329470064776849407269142528) }, { argument := 9927339930822636689650876416, coefficient := (-9927339930822636689650876416) }, { argument := 316719675273101365192163328, coefficient := (-316719675273101365192163328) }, { argument := 6337944725057145277043965952, coefficient := (-6337944725057145277043965952) }, { argument := 9927339930822636689650876416, coefficient := (-9927339930822636689650876416) }, { argument := 353308570782375376307879936, coefficient := (-353308570782375376307879936) }, { argument := 325219934942266726576816128, coefficient := (-325219934942266726576816128) }, { argument := 316719675273101365192163328, coefficient := (-316719675273101365192163328) }, { argument := 377052629458243952442343424, coefficient := (-377052629458243952442343424) }, { argument := 11264619671441662821265309696, coefficient := (-11264619671441662821265309696) }, { argument := 11556263580690726370372747264, coefficient := (-11556263580690726370372747264) }, { argument := 9025254595798945582349811712, coefficient := (-9025254595798945582349811712) }, { argument := 235326534400032473011110019072, coefficient := (-235326534400032473011110019072) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13
