import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 15, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent0

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2286152683033116058665717046706176)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    4870459887, 38963693415, 1075132569, 12939553241846033, 7209, 405,
    46946247957819739, 21897, 3234888179900261, 21897, 21897, 7209,
    405, 313584509, 11364406403, 90915284635, 2508642661, 1028931575,
    28035, 1575, 1767321065, 85155, 1028931575, 85155,
    85155, 28035, 1575, 4244136921, 4244136487, 85155,
    21897, 85155, 75423, 3530283, 961035, 21897,
    3530283, 85155, 85155, 36495, 85155, 961035,
    36495, 85155, 75423, 42422679, 4447941381, 47944362375,
    2223972387, 42422679, 85155, 21897, 85155, 75423,
    3530283, 961035, 21897, 3530283, 85155, 85155,
    36495, 85155, 961035, 36495
  ]
def negativeCoefficients : Array ℕ := #[
    1437506032908117478951744438272, 1437506561185974261845883617280, 39665390691305751177496363008, 7284320894789810966015084855296, 272348319800058178764275712, 15300467404497650492375040,
    26428388101159985672127216877568, 413622635501586484977205248, 7284320600792018733951487049728, 413622635501586484977205248, 413622635501586484977205248, 272348319800058178764275712,
    15300467404497650492375040, 2892306591501434776056758272, 104818148232883566173564698624, 104818186753143956592929013760, 2892268071241044356692443136, 75921749733535540147178700800,
    264783088694501007131934720, 14875454421039382423142400, 260810555057046426101292728320, 402133117848764638172282880, 75921749733535540147178700800, 402133117848764638172282880,
    402133117848764638172282880, 264783088694501007131934720, 14875454421039382423142400, 39145253797734326721910407168, 39145249794790862726937706496, 402133117848764638172282880,
    413622635501586484977205248, 402133117848764638172282880, 356175047237477250952593408, 16671290114244499713942355968, 4538359472864629487944335360, 413622635501586484977205248,
    16671290114244499713942355968, 402133117848764638172282880, 402133117848764638172282880, 344685529584655404147671040, 402133117848764638172282880, 4538359472864629487944335360,
    344685529584655404147671040, 402133117848764638172282880, 356175047237477250952593408, 195640075608533161859874816, 20512509077542307201940455424, 221104345627203613294067712000,
    20512524724992967726067613696, 195640075608533161859874816, 402133117848764638172282880, 413622635501586484977205248, 402133117848764638172282880, 356175047237477250952593408,
    16671290114244499713942355968, 4538359472864629487944335360, 413622635501586484977205248, 16671290114244499713942355968, 402133117848764638172282880, 402133117848764638172282880,
    344685529584655404147671040, 402133117848764638172282880, 4538359472864629487944335360, 344685529584655404147671040
  ]
def negativeScales : Array ℕ := #[
    32, 35, 30, 53, 12, 8,
    55, 14, 51, 14, 14, 12,
    8, 28, 33, 36, 31, 29,
    14, 10, 30, 16, 29, 16,
    16, 14, 10, 31, 31, 16,
    14, 16, 16, 21, 19, 14,
    21, 16, 16, 15, 16, 19,
    15, 16, 16, 25, 32, 35,
    31, 25, 16, 14, 16, 16,
    21, 19, 14, 21, 16, 16,
    15, 16, 19, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32181410857375873, 35181411387560573, 30001867415984216, 53522637325103757, 12815583434735727, 8661778097800657,
    55381859377483621, 14418445606380756, 51522637266876069, 14418445606380756, 14418445606380756, 12815583434735727,
    8661778097800657, 28224279051521148, 33403803278712329, 36403803808897028, 31224259837320665, 29938499907288165,
    14774941449737867, 10621136113284685, 30718917008762599, 16377803621883399, 29938499907288165, 16377803621883399,
    16377803621883399, 14774941449737867, 10621136113284685, 31982824072036423, 31982823924508227, 16377803621883399,
    14418445606380756, 16377803621883399, 16202716915325305, 21751352409236794, 19874229450734182, 14418445606380756,
    21751352409236794, 16377803621883399, 16377803621883399, 15155411200546948, 16377803621883399, 19874229450734182,
    15155411200546948, 16377803621883399, 16202716915325305, 25338332394414632, 32050490629031076, 35480642132171395,
    31050491729554214, 25338332394414632, 16377803621883399, 14418445606380756, 16377803621883399, 16202716915325305,
    21751352409236794, 19874229450734182, 14418445606380756, 21751352409236794, 16377803621883399, 16377803621883399,
    15155411200546948, 16377803621883399, 19874229450734182, 15155411200546948
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
noncomputable def negativeCeiling : ℝ := 14207104141 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1437506032908117478951744438272, coefficient := (-1437506032908117478951744438272) }, { argument := 1437506561185974261845883617280, coefficient := (-1437506561185974261845883617280) }, { argument := 39665390691305751177496363008, coefficient := (-39665390691305751177496363008) }, { argument := 7284320894789810966015084855296, coefficient := (-7284320894789810966015084855296) }, { argument := 272348319800058178764275712, coefficient := (-272348319800058178764275712) }, { argument := 15300467404497650492375040, coefficient := (-15300467404497650492375040) }, { argument := 26428388101159985672127216877568, coefficient := (-26428388101159985672127216877568) }, { argument := 413622635501586484977205248, coefficient := (-413622635501586484977205248) }, { argument := 7284320600792018733951487049728, coefficient := (-7284320600792018733951487049728) }, { argument := 413622635501586484977205248, coefficient := (-413622635501586484977205248) }, { argument := 413622635501586484977205248, coefficient := (-413622635501586484977205248) }, { argument := 272348319800058178764275712, coefficient := (-272348319800058178764275712) }, { argument := 15300467404497650492375040, coefficient := (-15300467404497650492375040) }, { argument := 2892306591501434776056758272, coefficient := (-2892306591501434776056758272) }, { argument := 104818148232883566173564698624, coefficient := (-104818148232883566173564698624) }, { argument := 104818186753143956592929013760, coefficient := (-104818186753143956592929013760) }, { argument := 2892268071241044356692443136, coefficient := (-2892268071241044356692443136) }, { argument := 75921749733535540147178700800, coefficient := (-75921749733535540147178700800) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 260810555057046426101292728320, coefficient := (-260810555057046426101292728320) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 75921749733535540147178700800, coefficient := (-75921749733535540147178700800) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 39145253797734326721910407168, coefficient := (-39145253797734326721910407168) }, { argument := 39145249794790862726937706496, coefficient := (-39145249794790862726937706496) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 413622635501586484977205248, coefficient := (-413622635501586484977205248) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 356175047237477250952593408, coefficient := (-356175047237477250952593408) }, { argument := 16671290114244499713942355968, coefficient := (-16671290114244499713942355968) }, { argument := 4538359472864629487944335360, coefficient := (-4538359472864629487944335360) }, { argument := 413622635501586484977205248, coefficient := (-413622635501586484977205248) }, { argument := 16671290114244499713942355968, coefficient := (-16671290114244499713942355968) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 344685529584655404147671040, coefficient := (-344685529584655404147671040) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 4538359472864629487944335360, coefficient := (-4538359472864629487944335360) }, { argument := 344685529584655404147671040, coefficient := (-344685529584655404147671040) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 356175047237477250952593408, coefficient := (-356175047237477250952593408) }, { argument := 195640075608533161859874816, coefficient := (-195640075608533161859874816) }, { argument := 20512509077542307201940455424, coefficient := (-20512509077542307201940455424) }, { argument := 221104345627203613294067712000, coefficient := (-221104345627203613294067712000) }, { argument := 20512524724992967726067613696, coefficient := (-20512524724992967726067613696) }, { argument := 195640075608533161859874816, coefficient := (-195640075608533161859874816) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 413622635501586484977205248, coefficient := (-413622635501586484977205248) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 356175047237477250952593408, coefficient := (-356175047237477250952593408) }, { argument := 16671290114244499713942355968, coefficient := (-16671290114244499713942355968) }, { argument := 4538359472864629487944335360, coefficient := (-4538359472864629487944335360) }, { argument := 413622635501586484977205248, coefficient := (-413622635501586484977205248) }, { argument := 16671290114244499713942355968, coefficient := (-16671290114244499713942355968) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 344685529584655404147671040, coefficient := (-344685529584655404147671040) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 4538359472864629487944335360, coefficient := (-4538359472864629487944335360) }, { argument := 344685529584655404147671040, coefficient := (-344685529584655404147671040) }] }

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


end Parent0

namespace Parent0

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-6770712650916762308966815979536384)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    85155, 75423, 3634209501, 381040311639, 4107233710125, 190520301153,
    3634209501, 4076598617, 147737283239, 1181898700255, 32612354593, 42422679,
    4447941381, 47944362375, 2223972387, 42422679, 4076598617, 147737283239,
    1181898700255, 32612354593, 9671490245, 24831, 1395, 16609124411,
    75423, 9671490245, 75423, 75423, 24831, 1395,
    28035, 7209, 28035, 24831, 1162251, 316395,
    7209, 1162251, 28035, 28035, 12015, 28035,
    316395, 12015, 28035, 24831, 1409375669, 147770496991,
    1592818261125, 73885304857, 1409375669, 134393361, 4870459887, 38963693415,
    1075132569, 3634209501, 381040311639, 4107233710125, 190520301153, 3634209501,
    50307914801, 1823175484367, 14585409235015, 402457958329
  ]
def negativeCoefficients : Array ℕ := #[
    402133117848764638172282880, 356175047237477250952593408, 8379916571898837099664637952, 878619138821395491816449507328, 9470636137698554769429233664000, 878619809053865450933229453312,
    8379916571898837099664637952, 75199971379037304177475715072, 2725271854054972720512682164224, 2725272855581742871416154357760, 75198969852267153274003521536, 195640075608533161859874816,
    20512509077542307201940455424, 221104345627203613294067712000, 20512524724992967726067613696, 195640075608533161859874816, 75199971379037304177475715072, 2725271854054972720512682164224,
    2725272855581742871416154357760, 75198969852267153274003521536, 89203752680446744708733992960, 234522164272272320602570752, 13175402487206310146211840, 306384267298118897069170098176,
    356175047237477250952593408, 89203752680446744708733992960, 356175047237477250952593408, 356175047237477250952593408, 234522164272272320602570752, 13175402487206310146211840,
    264783088694501007131934720, 272348319800058178764275712, 264783088694501007131934720, 234522164272272320602570752, 10977150334163456038526779392, 2988266286695082794774691840,
    272348319800058178764275712, 10977150334163456038526779392, 264783088694501007131934720, 264783088694501007131934720, 226956933166715148970229760, 264783088694501007131934720,
    2988266286695082794774691840, 226956933166715148970229760, 264783088694501007131934720, 234522164272272320602570752, 1624899516859761538780626944, 170367783727365273705005449216,
    1836394426181496677081284608000, 170367913688136037502617124864, 1624899516859761538780626944, 39665918969162534071635542016, 1437506032908117478951744438272, 1437506561185974261845883617280,
    39665390691305751177496363008, 8379916571898837099664637952, 878619138821395491816449507328, 9470636137698554769429233664000, 878619809053865450933229453312, 8379916571898837099664637952,
    928017229216031786717639868416, 33631651561579498517975187587072, 33631663921080189501102652129280, 928004869715340803590175326208
  ]
def negativeScales : Array ℕ := #[
    16, 16, 31, 38, 41, 37,
    31, 31, 37, 40, 34, 25,
    32, 35, 31, 25, 31, 37,
    40, 34, 33, 14, 10, 33,
    16, 33, 16, 16, 14, 10,
    14, 12, 14, 14, 20, 18,
    12, 20, 14, 14, 13, 14,
    18, 13, 14, 14, 30, 37,
    40, 36, 30, 27, 32, 35,
    30, 31, 38, 41, 37, 31,
    35, 40, 43, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    16377803621883399, 16202716915325305, 31758994443160739, 38471152677503898, 41901304185114832, 37471153778027036,
    31758994443160739, 31924718776420632, 37104242996853413, 40104243527038113, 34924699562217890, 25338332394414632,
    32050490629031076, 35480642132171395, 31050491729554214, 25338332394414632, 31924718776420632, 37104242996853413,
    40104243527038113, 34924699562217890, 33171091060484885, 14599854742801218, 10446049406716591, 33951256979768792,
    16202716915325305, 33171091060484885, 16202716915325305, 16202716915325305, 14599854742801218, 10446049406716591,
    14774941449737867, 12815583434735727, 14774941449737867, 14599854742801218, 20148490236475455, 18271367275473176,
    12815583434735727, 20148490236475455, 14774941449737867, 14774941449737867, 13552549028018665, 14774941449737867,
    18271367275473176, 13552549028018665, 14774941449737867, 14599854742801218, 30392409067170429, 37104567301786868,
    40534718804927879, 36104568402310006, 30392409067170429, 27001886630184700, 32181410857375873, 35181411387560573,
    30001867415984216, 31758994443160739, 38471152677503898, 41901304185114832, 37471153778027036, 31758994443160739,
    35550066341865477, 40729590569198327, 43729591099383029, 38550047127664993
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
noncomputable def negativeCeiling : ℝ := 2696622947 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 356175047237477250952593408, coefficient := (-356175047237477250952593408) }, { argument := 8379916571898837099664637952, coefficient := (-8379916571898837099664637952) }, { argument := 878619138821395491816449507328, coefficient := (-878619138821395491816449507328) }, { argument := 9470636137698554769429233664000, coefficient := (-9470636137698554769429233664000) }, { argument := 878619809053865450933229453312, coefficient := (-878619809053865450933229453312) }, { argument := 8379916571898837099664637952, coefficient := (-8379916571898837099664637952) }, { argument := 75199971379037304177475715072, coefficient := (-75199971379037304177475715072) }, { argument := 2725271854054972720512682164224, coefficient := (-2725271854054972720512682164224) }, { argument := 2725272855581742871416154357760, coefficient := (-2725272855581742871416154357760) }, { argument := 75198969852267153274003521536, coefficient := (-75198969852267153274003521536) }, { argument := 195640075608533161859874816, coefficient := (-195640075608533161859874816) }, { argument := 20512509077542307201940455424, coefficient := (-20512509077542307201940455424) }, { argument := 221104345627203613294067712000, coefficient := (-221104345627203613294067712000) }, { argument := 20512524724992967726067613696, coefficient := (-20512524724992967726067613696) }, { argument := 195640075608533161859874816, coefficient := (-195640075608533161859874816) }, { argument := 75199971379037304177475715072, coefficient := (-75199971379037304177475715072) }, { argument := 2725271854054972720512682164224, coefficient := (-2725271854054972720512682164224) }, { argument := 2725272855581742871416154357760, coefficient := (-2725272855581742871416154357760) }, { argument := 75198969852267153274003521536, coefficient := (-75198969852267153274003521536) }, { argument := 89203752680446744708733992960, coefficient := (-89203752680446744708733992960) }, { argument := 234522164272272320602570752, coefficient := (-234522164272272320602570752) }, { argument := 13175402487206310146211840, coefficient := (-13175402487206310146211840) }, { argument := 306384267298118897069170098176, coefficient := (-306384267298118897069170098176) }, { argument := 356175047237477250952593408, coefficient := (-356175047237477250952593408) }, { argument := 89203752680446744708733992960, coefficient := (-89203752680446744708733992960) }, { argument := 356175047237477250952593408, coefficient := (-356175047237477250952593408) }, { argument := 356175047237477250952593408, coefficient := (-356175047237477250952593408) }, { argument := 234522164272272320602570752, coefficient := (-234522164272272320602570752) }, { argument := 13175402487206310146211840, coefficient := (-13175402487206310146211840) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 272348319800058178764275712, coefficient := (-272348319800058178764275712) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 234522164272272320602570752, coefficient := (-234522164272272320602570752) }, { argument := 10977150334163456038526779392, coefficient := (-10977150334163456038526779392) }, { argument := 2988266286695082794774691840, coefficient := (-2988266286695082794774691840) }, { argument := 272348319800058178764275712, coefficient := (-272348319800058178764275712) }, { argument := 10977150334163456038526779392, coefficient := (-10977150334163456038526779392) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 226956933166715148970229760, coefficient := (-226956933166715148970229760) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 2988266286695082794774691840, coefficient := (-2988266286695082794774691840) }, { argument := 226956933166715148970229760, coefficient := (-226956933166715148970229760) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 234522164272272320602570752, coefficient := (-234522164272272320602570752) }, { argument := 1624899516859761538780626944, coefficient := (-1624899516859761538780626944) }, { argument := 170367783727365273705005449216, coefficient := (-170367783727365273705005449216) }, { argument := 1836394426181496677081284608000, coefficient := (-1836394426181496677081284608000) }, { argument := 170367913688136037502617124864, coefficient := (-170367913688136037502617124864) }, { argument := 1624899516859761538780626944, coefficient := (-1624899516859761538780626944) }, { argument := 39665918969162534071635542016, coefficient := (-39665918969162534071635542016) }, { argument := 1437506032908117478951744438272, coefficient := (-1437506032908117478951744438272) }, { argument := 1437506561185974261845883617280, coefficient := (-1437506561185974261845883617280) }, { argument := 39665390691305751177496363008, coefficient := (-39665390691305751177496363008) }, { argument := 8379916571898837099664637952, coefficient := (-8379916571898837099664637952) }, { argument := 878619138821395491816449507328, coefficient := (-878619138821395491816449507328) }, { argument := 9470636137698554769429233664000, coefficient := (-9470636137698554769429233664000) }, { argument := 878619809053865450933229453312, coefficient := (-878619809053865450933229453312) }, { argument := 8379916571898837099664637952, coefficient := (-8379916571898837099664637952) }, { argument := 928017229216031786717639868416, coefficient := (-928017229216031786717639868416) }, { argument := 33631651561579498517975187587072, coefficient := (-33631651561579498517975187587072) }, { argument := 33631663921080189501102652129280, coefficient := (-33631663921080189501102652129280) }, { argument := 928004869715340803590175326208, coefficient := (-928004869715340803590175326208) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15
