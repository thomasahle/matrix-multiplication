import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 11, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11

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
def constantNumerator : ℤ := (-482890236419010465771012357095424)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    948425, 1715425, 51625, 948425, 28025, 28025,
    54575, 54575, 1715425, 54575, 69325, 4425,
    6718979, 5003495, 5289409, 428871, 91921351, 166258991,
    5003495, 91921351, 2716183, 2716183, 5289409, 5289409,
    166258991, 5289409, 6718979, 428871, 35294733, 913005345,
    1473113, 17700853743, 466175, 55941, 1473113, 2927579,
    466175, 45181681, 2890285, 913005345, 1473113, 55941,
    2890285, 55941, 1473113, 1473113, 35294733, 429815,
    320075, 338365, 27435, 5880235, 10635635, 320075,
    5880235, 173755, 173755, 338365, 338365, 10635635,
    338365, 429815, 27435, 1001193255
  ]
def negativeCoefficients : Array ℕ := #[
    17915241726062573047198515200, 32403462095506644562817843200, 975168678712581736628224000, 17915241726062573047198515200, 1058754565459374456910643200, 1058754565459374456910643200,
    1030892603210443550149836800, 1030892603210443550149836800, 32403462095506644562817843200, 1030892603210443550149836800, 1309512225699752617757900800, 1337374187948683524518707200,
    31729481228705005928273936384, 23628337085205855478501867520, 24978527775789047220130545664, 32404576573996601799088275456, 434086307022496144933620023296, 785135886574125997757076340736,
    23628337085205855478501867520, 434086307022496144933620023296, 25653623121080643090944884736, 25653623121080643090944884736, 24978527775789047220130545664, 24978527775789047220130545664,
    785135886574125997757076340736, 24978527775789047220130545664, 31729481228705005928273936384, 32404576573996601799088275456, 2604291627203643775345754112, 269471614994302313647382200320,
    27826317826718206678733422592, 2612184951066278276935402389504, 17611593561214054859957862400, 1056695613672843291597471744, 27826317826718206678733422592, 27650201891106066130133843968,
    17611593561214054859957862400, 426728911988216549256779005952, 27297970019881785032934686720, 269471614994302313647382200320, 27826317826718206678733422592, 1056695613672843291597471744,
    27297970019881785032934686720, 1056695613672843291597471744, 27826317826718206678733422592, 27826317826718206678733422592, 2604291627203643775345754112, 2029743949834616557524746240,
    1511511452004501691773747200, 1597883534976187502732247040, 2072929991320459463003996160, 27768624675396988223157698560, 50225366248035299072367656960, 1511511452004501691773747200,
    27768624675396988223157698560, 1641069576462030408211496960, 1641069576462030408211496960, 1597883534976187502732247040, 1597883534976187502732247040, 50225366248035299072367656960,
    1597883534976187502732247040, 2029743949834616557524746240, 2072929991320459463003996160, 4617188935827306476753387520
  ]
def negativeScales : Array ℕ := #[
    19, 20, 15, 19, 14, 14,
    15, 15, 20, 15, 16, 12,
    22, 22, 22, 18, 26, 27,
    22, 26, 21, 21, 22, 22,
    27, 22, 22, 18, 25, 29,
    20, 34, 18, 15, 20, 21,
    18, 25, 21, 29, 20, 15,
    21, 15, 20, 20, 25, 18,
    18, 18, 14, 22, 23, 18,
    22, 17, 17, 18, 18, 23,
    18, 18, 14, 29
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19855174168375817, 20710134620701494, 15655782256106199, 19855174168375817, 14774426752960191, 14774426752960191,
    15735952604930435, 15735952604930435, 20710134620701494, 15735952604930435, 16081088090814204, 12111461739857723,
    22679810590535512, 22254504755758155, 22334675104442138, 18710184239626159, 26453896666141189, 27308857120286407,
    22254504755758155, 26453896666141189, 21373149252256776, 21373149252256776, 22334675104442138, 22334675104442138,
    27308857120286407, 22334675104442138, 22679810590535512, 18710184239626159, 25072949571738482, 29766048065609420,
    20490436670632819, 34043099894554130, 18830512113418682, 15771618423534793, 20490436670632819, 21481276671347290,
    18830512113418682, 25429234611906888, 21462780327729832, 29766048065609420, 20490436670632819, 15771618423534793,
    21462780327729832, 15771618423534793, 20490436670632819, 20490436670632819, 25072949571738482, 18713356306412515,
    18288050471581046, 18368220820265031, 14743729955553198, 22487442381964204, 23342402836109298, 18288050471581046,
    22487442381964204, 17406694968079673, 17406694968079673, 18368220820265031, 18368220820265031, 23342402836109298,
    18368220820265031, 18713356306412515, 14743729955553198, 29899073335073144
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
noncomputable def negativeCeiling : ℝ := 2412782599 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 17915241726062573047198515200, coefficient := (-17915241726062573047198515200) }, { argument := 32403462095506644562817843200, coefficient := (-32403462095506644562817843200) }, { argument := 975168678712581736628224000, coefficient := (-975168678712581736628224000) }, { argument := 17915241726062573047198515200, coefficient := (-17915241726062573047198515200) }, { argument := 1058754565459374456910643200, coefficient := (-1058754565459374456910643200) }, { argument := 1058754565459374456910643200, coefficient := (-1058754565459374456910643200) }, { argument := 1030892603210443550149836800, coefficient := (-1030892603210443550149836800) }, { argument := 1030892603210443550149836800, coefficient := (-1030892603210443550149836800) }, { argument := 32403462095506644562817843200, coefficient := (-32403462095506644562817843200) }, { argument := 1030892603210443550149836800, coefficient := (-1030892603210443550149836800) }, { argument := 1309512225699752617757900800, coefficient := (-1309512225699752617757900800) }, { argument := 1337374187948683524518707200, coefficient := (-1337374187948683524518707200) }, { argument := 31729481228705005928273936384, coefficient := (-31729481228705005928273936384) }, { argument := 23628337085205855478501867520, coefficient := (-23628337085205855478501867520) }, { argument := 24978527775789047220130545664, coefficient := (-24978527775789047220130545664) }, { argument := 32404576573996601799088275456, coefficient := (-32404576573996601799088275456) }, { argument := 434086307022496144933620023296, coefficient := (-434086307022496144933620023296) }, { argument := 785135886574125997757076340736, coefficient := (-785135886574125997757076340736) }, { argument := 23628337085205855478501867520, coefficient := (-23628337085205855478501867520) }, { argument := 434086307022496144933620023296, coefficient := (-434086307022496144933620023296) }, { argument := 25653623121080643090944884736, coefficient := (-25653623121080643090944884736) }, { argument := 25653623121080643090944884736, coefficient := (-25653623121080643090944884736) }, { argument := 24978527775789047220130545664, coefficient := (-24978527775789047220130545664) }, { argument := 24978527775789047220130545664, coefficient := (-24978527775789047220130545664) }, { argument := 785135886574125997757076340736, coefficient := (-785135886574125997757076340736) }, { argument := 24978527775789047220130545664, coefficient := (-24978527775789047220130545664) }, { argument := 31729481228705005928273936384, coefficient := (-31729481228705005928273936384) }, { argument := 32404576573996601799088275456, coefficient := (-32404576573996601799088275456) }, { argument := 2604291627203643775345754112, coefficient := (-2604291627203643775345754112) }, { argument := 269471614994302313647382200320, coefficient := (-269471614994302313647382200320) }, { argument := 27826317826718206678733422592, coefficient := (-27826317826718206678733422592) }, { argument := 2612184951066278276935402389504, coefficient := (-2612184951066278276935402389504) }, { argument := 17611593561214054859957862400, coefficient := (-17611593561214054859957862400) }, { argument := 1056695613672843291597471744, coefficient := (-1056695613672843291597471744) }, { argument := 27826317826718206678733422592, coefficient := (-27826317826718206678733422592) }, { argument := 27650201891106066130133843968, coefficient := (-27650201891106066130133843968) }, { argument := 17611593561214054859957862400, coefficient := (-17611593561214054859957862400) }, { argument := 426728911988216549256779005952, coefficient := (-426728911988216549256779005952) }, { argument := 27297970019881785032934686720, coefficient := (-27297970019881785032934686720) }, { argument := 269471614994302313647382200320, coefficient := (-269471614994302313647382200320) }, { argument := 27826317826718206678733422592, coefficient := (-27826317826718206678733422592) }, { argument := 1056695613672843291597471744, coefficient := (-1056695613672843291597471744) }, { argument := 27297970019881785032934686720, coefficient := (-27297970019881785032934686720) }, { argument := 1056695613672843291597471744, coefficient := (-1056695613672843291597471744) }, { argument := 27826317826718206678733422592, coefficient := (-27826317826718206678733422592) }, { argument := 27826317826718206678733422592, coefficient := (-27826317826718206678733422592) }, { argument := 2604291627203643775345754112, coefficient := (-2604291627203643775345754112) }, { argument := 2029743949834616557524746240, coefficient := (-2029743949834616557524746240) }, { argument := 1511511452004501691773747200, coefficient := (-1511511452004501691773747200) }, { argument := 1597883534976187502732247040, coefficient := (-1597883534976187502732247040) }, { argument := 2072929991320459463003996160, coefficient := (-2072929991320459463003996160) }, { argument := 27768624675396988223157698560, coefficient := (-27768624675396988223157698560) }, { argument := 50225366248035299072367656960, coefficient := (-50225366248035299072367656960) }, { argument := 1511511452004501691773747200, coefficient := (-1511511452004501691773747200) }, { argument := 27768624675396988223157698560, coefficient := (-27768624675396988223157698560) }, { argument := 1641069576462030408211496960, coefficient := (-1641069576462030408211496960) }, { argument := 1641069576462030408211496960, coefficient := (-1641069576462030408211496960) }, { argument := 1597883534976187502732247040, coefficient := (-1597883534976187502732247040) }, { argument := 1597883534976187502732247040, coefficient := (-1597883534976187502732247040) }, { argument := 50225366248035299072367656960, coefficient := (-50225366248035299072367656960) }, { argument := 1597883534976187502732247040, coefficient := (-1597883534976187502732247040) }, { argument := 2029743949834616557524746240, coefficient := (-2029743949834616557524746240) }, { argument := 2072929991320459463003996160, coefficient := (-2072929991320459463003996160) }, { argument := 4617188935827306476753387520, coefficient := (-4617188935827306476753387520) }] }

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
def constantNumerator : ℤ := (-3503071319761999392097225043607552)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    25593637155, 2664433, 495199077453, 843175, 101181, 2664433,
    5295139, 843175, 81720521, 5227685, 25593637155, 2664433,
    101181, 5227685, 101181, 2664433, 2664433, 1001193255,
    3862969939, 604122185099, 151030568609, 15452057253, 2335533743067, 1970448393,
    87693741912381, 826377129, 81064101, 826010175, 1658212275, 293056851549,
    1970448393, 81064101, 74504056879179, 7376673093502901, 837010035, 2159391825,
    1806903945, 50654536155, 7375995204150097, 1806903945, 1635332805, 838369395,
    837010035, 1632614085, 50654536155, 1632614085, 74503550573743, 2159391825,
    5029060634075, 3717722512411545, 80185, 150845822479816499, 25375, 3045,
    80185, 159355, 25375, 2459345, 157325, 14870919955169033,
    80185, 3045, 157325, 3045
  ]
def negativeCoefficients : Array ℕ := #[
    472119274513668838917647892480, 50329716380207269622654697472, 4567405323656282495858742657024, 31854250873548904824464998400, 1911255052412934289467899904, 50329716380207269622654697472,
    50011173871471780574410047488, 31854250873548904824464998400, 771828498666089963896786911232, 49374088854000802477920747520, 472119274513668838917647892480, 50329716380207269622654697472,
    1911255052412934289467899904, 49374088854000802477920747520, 1911255052412934289467899904, 50329716380207269622654697472, 50329716380207269622654697472, 4617188935827306476753387520,
    17814804457291599527444217856, 696505458610715190057840410624, 696505561609263647119728705536, 17815009097399902728961916928, 2629577223746940236420087808, 18174178608061629765248876544,
    98734375849830879721364127744, 15243967407029863644307390464, 747684362356171268432068608, 15237198300505039629503692800, 15294308728404341637198643200, 2639621454868894326988996608,
    18174178608061629765248876544, 747684362356171268432068608, 41942055349832597940467662848, 4152697774391703617683547226112, 15440109902771674377942466560, 19916874175317801592002969600,
    266651957113529276793052200960, 467205632311876233650755338240, 4152316156612117802546326667264, 266651957113529276793052200960, 15083282864588283899742781440, 15465185668795712194027192320,
    15440109902771674377942466560, 15058207098564246083658055680, 467205632311876233650755338240, 15058207098564246083658055680, 41941770325210984783403810816, 19916874175317801592002969600,
    22648875597643800338707251200, 4185783430390884563113035694080, 1514651825715610005840855040, 42459324369406098360645497913344, 958640396022537978380288000, 57518423761352278702817280,
    1514651825715610005840855040, 1505065421755384626057052160, 958640396022537978380288000, 23227856795626095216154378240, 1485892613834933866489446400, 4185791848047233131278812315648,
    1514651825715610005840855040, 57518423761352278702817280, 1485892613834933866489446400, 57518423761352278702817280
  ]
def negativeScales : Array ℕ := #[
    34, 21, 38, 19, 16, 21,
    22, 19, 26, 22, 34, 21,
    16, 22, 16, 21, 21, 29,
    31, 39, 37, 33, 41, 30,
    46, 29, 26, 29, 30, 38,
    30, 26, 46, 52, 29, 31,
    30, 35, 52, 30, 30, 29,
    29, 30, 35, 30, 46, 31,
    42, 51, 16, 57, 14, 11,
    16, 17, 14, 21, 17, 53,
    16, 11, 17, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34575066134652059, 21345397124777895, 38849217672307118, 19685472566426753, 16626578877333553, 21345397124777895,
    22336237125492418, 19685472566426753, 26284195066052138, 22317740781875029, 34575066134652059, 21345397124777895,
    16626578877333553, 22317740781875029, 16626578877333553, 21345397124777895, 21345397124777895, 29899073335073144,
    31847063306420562, 39136049411207201, 37136049624551522, 33847079878681219, 41086889427547431, 30875876821889066,
    46317539124847492, 29622225085511053, 26272559826799642, 29621584312341711, 30626981558350889, 38092389611110268,
    30875876821889066, 26272559826799642, 46082384218575226, 52711891725642043, 29640669678615245, 31007977900355233,
    30750872668799005, 35559972418203732, 52711759141137237, 30750872668799005, 30606937121070438, 29643010810811211,
    29640669678615245, 30604536662985166, 35559972418203732, 30604536662985166, 46082374414453757, 31007977900355233,
    42193426086368480, 51723340516202066, 16291044760249642, 57065852356165033, 14631120201860344, 11572226512796267,
    16291044760249642, 17281884760964166, 14631120201860344, 21229842701523886, 17263388417346777, 53723343417474694,
    16291044760249642, 11572226512796267, 17263388417346777, 11572226512796267
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
noncomputable def negativeCeiling : ℝ := 44096640447 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 472119274513668838917647892480, coefficient := (-472119274513668838917647892480) }, { argument := 50329716380207269622654697472, coefficient := (-50329716380207269622654697472) }, { argument := 4567405323656282495858742657024, coefficient := (-4567405323656282495858742657024) }, { argument := 31854250873548904824464998400, coefficient := (-31854250873548904824464998400) }, { argument := 1911255052412934289467899904, coefficient := (-1911255052412934289467899904) }, { argument := 50329716380207269622654697472, coefficient := (-50329716380207269622654697472) }, { argument := 50011173871471780574410047488, coefficient := (-50011173871471780574410047488) }, { argument := 31854250873548904824464998400, coefficient := (-31854250873548904824464998400) }, { argument := 771828498666089963896786911232, coefficient := (-771828498666089963896786911232) }, { argument := 49374088854000802477920747520, coefficient := (-49374088854000802477920747520) }, { argument := 472119274513668838917647892480, coefficient := (-472119274513668838917647892480) }, { argument := 50329716380207269622654697472, coefficient := (-50329716380207269622654697472) }, { argument := 1911255052412934289467899904, coefficient := (-1911255052412934289467899904) }, { argument := 49374088854000802477920747520, coefficient := (-49374088854000802477920747520) }, { argument := 1911255052412934289467899904, coefficient := (-1911255052412934289467899904) }, { argument := 50329716380207269622654697472, coefficient := (-50329716380207269622654697472) }, { argument := 50329716380207269622654697472, coefficient := (-50329716380207269622654697472) }, { argument := 4617188935827306476753387520, coefficient := (-4617188935827306476753387520) }, { argument := 17814804457291599527444217856, coefficient := (-17814804457291599527444217856) }, { argument := 696505458610715190057840410624, coefficient := (-696505458610715190057840410624) }, { argument := 696505561609263647119728705536, coefficient := (-696505561609263647119728705536) }, { argument := 17815009097399902728961916928, coefficient := (-17815009097399902728961916928) }, { argument := 2629577223746940236420087808, coefficient := (-2629577223746940236420087808) }, { argument := 18174178608061629765248876544, coefficient := (-18174178608061629765248876544) }, { argument := 98734375849830879721364127744, coefficient := (-98734375849830879721364127744) }, { argument := 15243967407029863644307390464, coefficient := (-15243967407029863644307390464) }, { argument := 747684362356171268432068608, coefficient := (-747684362356171268432068608) }, { argument := 15237198300505039629503692800, coefficient := (-15237198300505039629503692800) }, { argument := 15294308728404341637198643200, coefficient := (-15294308728404341637198643200) }, { argument := 2639621454868894326988996608, coefficient := (-2639621454868894326988996608) }, { argument := 18174178608061629765248876544, coefficient := (-18174178608061629765248876544) }, { argument := 747684362356171268432068608, coefficient := (-747684362356171268432068608) }, { argument := 41942055349832597940467662848, coefficient := (-41942055349832597940467662848) }, { argument := 4152697774391703617683547226112, coefficient := (-4152697774391703617683547226112) }, { argument := 15440109902771674377942466560, coefficient := (-15440109902771674377942466560) }, { argument := 19916874175317801592002969600, coefficient := (-19916874175317801592002969600) }, { argument := 266651957113529276793052200960, coefficient := (-266651957113529276793052200960) }, { argument := 467205632311876233650755338240, coefficient := (-467205632311876233650755338240) }, { argument := 4152316156612117802546326667264, coefficient := (-4152316156612117802546326667264) }, { argument := 266651957113529276793052200960, coefficient := (-266651957113529276793052200960) }, { argument := 15083282864588283899742781440, coefficient := (-15083282864588283899742781440) }, { argument := 15465185668795712194027192320, coefficient := (-15465185668795712194027192320) }, { argument := 15440109902771674377942466560, coefficient := (-15440109902771674377942466560) }, { argument := 15058207098564246083658055680, coefficient := (-15058207098564246083658055680) }, { argument := 467205632311876233650755338240, coefficient := (-467205632311876233650755338240) }, { argument := 15058207098564246083658055680, coefficient := (-15058207098564246083658055680) }, { argument := 41941770325210984783403810816, coefficient := (-41941770325210984783403810816) }, { argument := 19916874175317801592002969600, coefficient := (-19916874175317801592002969600) }, { argument := 22648875597643800338707251200, coefficient := (-22648875597643800338707251200) }, { argument := 4185783430390884563113035694080, coefficient := (-4185783430390884563113035694080) }, { argument := 1514651825715610005840855040, coefficient := (-1514651825715610005840855040) }, { argument := 42459324369406098360645497913344, coefficient := (-42459324369406098360645497913344) }, { argument := 958640396022537978380288000, coefficient := (-958640396022537978380288000) }, { argument := 57518423761352278702817280, coefficient := (-57518423761352278702817280) }, { argument := 1514651825715610005840855040, coefficient := (-1514651825715610005840855040) }, { argument := 1505065421755384626057052160, coefficient := (-1505065421755384626057052160) }, { argument := 958640396022537978380288000, coefficient := (-958640396022537978380288000) }, { argument := 23227856795626095216154378240, coefficient := (-23227856795626095216154378240) }, { argument := 1485892613834933866489446400, coefficient := (-1485892613834933866489446400) }, { argument := 4185791848047233131278812315648, coefficient := (-4185791848047233131278812315648) }, { argument := 1514651825715610005840855040, coefficient := (-1514651825715610005840855040) }, { argument := 57518423761352278702817280, coefficient := (-57518423761352278702817280) }, { argument := 1485892613834933866489446400, coefficient := (-1485892613834933866489446400) }, { argument := 57518423761352278702817280, coefficient := (-57518423761352278702817280) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11
