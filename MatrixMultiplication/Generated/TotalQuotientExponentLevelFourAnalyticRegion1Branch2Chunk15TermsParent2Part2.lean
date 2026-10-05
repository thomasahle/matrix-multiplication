import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 15, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent2

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-189724771902437935717688071421952)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1536001785, 46227, 46227, 15219, 855, 7299,
    114351, 90021, 2829579, 90021, 90021, 46227,
    46227, 1564419, 85155, 2829579, 1564419, 7299,
    90021, 85155, 114351, 16425337695, 515043, 28935,
    450746050485, 1564419, 131402659155, 1564419, 1564419, 515043,
    28935, 5433, 5433, 191965725, 28035, 1575,
    5290794015, 85155, 1535725305, 85155, 85155, 28035,
    1575, 1317, 1317, 135, 2403, 37647,
    29637, 931563, 29637, 29637, 15219, 15219,
    515043, 28035, 931563, 515043, 2403, 29637,
    28035, 37647, 6417723815, 931563
  ]
def negativeCoefficients : Array ℕ := #[
    7083557956164010713431408640, 436601670807230178587049984, 436601670807230178587049984, 287478782011172522028957696, 16150493371414186630840320, 551496847335448646636273664,
    540007329682626799831351296, 425112153154408331782127616, 13362309030231807834124713984, 425112153154408331782127616, 425112153154408331782127616, 436601670807230178587049984,
    436601670807230178587049984, 7387759850764447495565082624, 402133117848764638172282880, 13362309030231807834124713984, 7387759850764447495565082624, 551496847335448646636273664,
    425112153154408331782127616, 402133117848764638172282880, 540007329682626799831351296, 302994000783919356639832965120, 4864443600873261359595257856, 273283348363666368516587520,
    1039349629441520014241531166720, 7387759850764447495565082624, 302993903004646550933140930560, 7387759850764447495565082624, 7387759850764447495565082624, 4864443600873261359595257856,
    273283348363666368516587520, 210179007294920969797716934656, 210179007294920969797716934656, 7082285199998215030780723200, 264783088694501007131934720, 14875454421039382423142400,
    24399480785354803634566594560, 402133117848764638172282880, 7082282917213635909223710720, 402133117848764638172282880, 402133117848764638172282880, 264783088694501007131934720,
    14875454421039382423142400, 203795878967355727755268325376, 203795878967355727755268325376, 20890238162940792138922721280, 363131093066744238352367616, 355565861961187066720026624,
    279913550905615350396616704, 8798363775762990608412573696, 279913550905615350396616704, 279913550905615350396616704, 287478782011172522028957696, 287478782011172522028957696,
    4864443600873261359595257856, 264783088694501007131934720, 8798363775762990608412573696, 4864443600873261359595257856, 363131093066744238352367616, 279913550905615350396616704,
    264783088694501007131934720, 355565861961187066720026624, 59193054375527952399487467520, 8798363775762990608412573696
  ]
def negativeScales : Array ℕ := #[
    30, 15, 15, 13, 9, 12,
    16, 16, 21, 16, 16, 15,
    15, 20, 16, 21, 20, 12,
    16, 16, 16, 33, 18, 14,
    38, 20, 36, 20, 20, 18,
    14, 12, 12, 27, 14, 10,
    32, 16, 30, 16, 16, 14,
    10, 10, 10, 7, 11, 15,
    14, 19, 14, 14, 13, 13,
    18, 14, 19, 18, 11, 14,
    14, 15, 32, 19
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30516532746614255, 15496448118382256, 15496448118382256, 13893585949743706, 9739780609952834, 12833483106919052,
    16803109457304290, 16457973970567442, 21432155986411672, 16457973970567442, 16457973970567442, 15496448118382256,
    15496448118382256, 20577195532269347, 16377803621883399, 21432155986411672, 20577195532269347, 12833483106919052,
    16457973970567442, 16377803621883399, 16803109457304290, 33935203988764626, 18974333375367452, 14820528024633809,
    38713523894429226, 20577195532269347, 36935203523191994, 20577195532269347, 20577195532269347, 18974333375367452,
    14820528024633809, 12407533331671334, 12407533331671334, 27516273503448370, 14774941449737867, 10621136113284685,
    32300837104783336, 16377803621883399, 30516273038434263, 16377803621883399, 16377803621883399, 14774941449737867,
    10621136113284685, 10363039630256516, 10363039630256516, 7076815597050831, 11230620933129867, 15200247284086348,
    14855111799946705, 19829293815042335, 14855111799946705, 14855111799946705, 13893585949743706, 13893585949743706,
    18974333375367452, 14774941449737867, 19829293815042335, 18974333375367452, 11230620933129867, 14855111799946705,
    14774941449737867, 15200247284086348, 32579414558956085, 19829293815042335
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
noncomputable def negativeCeiling : ℝ := 463780983 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7083557956164010713431408640, coefficient := (-7083557956164010713431408640) }, { argument := 436601670807230178587049984, coefficient := (-436601670807230178587049984) }, { argument := 436601670807230178587049984, coefficient := (-436601670807230178587049984) }, { argument := 287478782011172522028957696, coefficient := (-287478782011172522028957696) }, { argument := 16150493371414186630840320, coefficient := (-16150493371414186630840320) }, { argument := 551496847335448646636273664, coefficient := (-551496847335448646636273664) }, { argument := 540007329682626799831351296, coefficient := (-540007329682626799831351296) }, { argument := 425112153154408331782127616, coefficient := (-425112153154408331782127616) }, { argument := 13362309030231807834124713984, coefficient := (-13362309030231807834124713984) }, { argument := 425112153154408331782127616, coefficient := (-425112153154408331782127616) }, { argument := 425112153154408331782127616, coefficient := (-425112153154408331782127616) }, { argument := 436601670807230178587049984, coefficient := (-436601670807230178587049984) }, { argument := 436601670807230178587049984, coefficient := (-436601670807230178587049984) }, { argument := 7387759850764447495565082624, coefficient := (-7387759850764447495565082624) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 13362309030231807834124713984, coefficient := (-13362309030231807834124713984) }, { argument := 7387759850764447495565082624, coefficient := (-7387759850764447495565082624) }, { argument := 551496847335448646636273664, coefficient := (-551496847335448646636273664) }, { argument := 425112153154408331782127616, coefficient := (-425112153154408331782127616) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 540007329682626799831351296, coefficient := (-540007329682626799831351296) }, { argument := 302994000783919356639832965120, coefficient := (-302994000783919356639832965120) }, { argument := 4864443600873261359595257856, coefficient := (-4864443600873261359595257856) }, { argument := 273283348363666368516587520, coefficient := (-273283348363666368516587520) }, { argument := 1039349629441520014241531166720, coefficient := (-1039349629441520014241531166720) }, { argument := 7387759850764447495565082624, coefficient := (-7387759850764447495565082624) }, { argument := 302993903004646550933140930560, coefficient := (-302993903004646550933140930560) }, { argument := 7387759850764447495565082624, coefficient := (-7387759850764447495565082624) }, { argument := 7387759850764447495565082624, coefficient := (-7387759850764447495565082624) }, { argument := 4864443600873261359595257856, coefficient := (-4864443600873261359595257856) }, { argument := 273283348363666368516587520, coefficient := (-273283348363666368516587520) }, { argument := 210179007294920969797716934656, coefficient := (-210179007294920969797716934656) }, { argument := 210179007294920969797716934656, coefficient := (-210179007294920969797716934656) }, { argument := 7082285199998215030780723200, coefficient := (-7082285199998215030780723200) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 24399480785354803634566594560, coefficient := (-24399480785354803634566594560) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 7082282917213635909223710720, coefficient := (-7082282917213635909223710720) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 402133117848764638172282880, coefficient := (-402133117848764638172282880) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 203795878967355727755268325376, coefficient := (-203795878967355727755268325376) }, { argument := 203795878967355727755268325376, coefficient := (-203795878967355727755268325376) }, { argument := 20890238162940792138922721280, coefficient := (-20890238162940792138922721280) }, { argument := 363131093066744238352367616, coefficient := (-363131093066744238352367616) }, { argument := 355565861961187066720026624, coefficient := (-355565861961187066720026624) }, { argument := 279913550905615350396616704, coefficient := (-279913550905615350396616704) }, { argument := 8798363775762990608412573696, coefficient := (-8798363775762990608412573696) }, { argument := 279913550905615350396616704, coefficient := (-279913550905615350396616704) }, { argument := 279913550905615350396616704, coefficient := (-279913550905615350396616704) }, { argument := 287478782011172522028957696, coefficient := (-287478782011172522028957696) }, { argument := 287478782011172522028957696, coefficient := (-287478782011172522028957696) }, { argument := 4864443600873261359595257856, coefficient := (-4864443600873261359595257856) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 8798363775762990608412573696, coefficient := (-8798363775762990608412573696) }, { argument := 4864443600873261359595257856, coefficient := (-4864443600873261359595257856) }, { argument := 363131093066744238352367616, coefficient := (-363131093066744238352367616) }, { argument := 279913550905615350396616704, coefficient := (-279913550905615350396616704) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 355565861961187066720026624, coefficient := (-355565861961187066720026624) }, { argument := 59193054375527952399487467520, coefficient := (-59193054375527952399487467520) }, { argument := 8798363775762990608412573696, coefficient := (-8798363775762990608412573696) }] }

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


end Parent2

namespace Parent2

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4657746260621328389996407852892160)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    52335, 180863407565, 2829579, 51341774075, 2829579, 2829579,
    931563, 52335, 6113, 6113, 16425337695, 515043,
    28935, 450746050485, 1564419, 131402659155, 1564419, 1564419,
    515043, 28935, 34227, 34227, 2001, 5235,
    5235, 27393, 18738112740076651, 2403, 135, 16430925403491849,
    7299, 18738112600972145, 7299, 7299, 2403, 135,
    8382153218457263, 8382150620873041, 11101737, 5433, 5433, 2001,
    945, 135, 2115, 1665, 52335, 1665,
    1665, 855, 855, 28935, 1575, 52335,
    28935, 135, 1665, 1575, 2115, 191988765,
    29637, 1665, 5293712415, 90021
  ]
def negativeCoefficients : Array ℕ := #[
    494290099761965764517560320, 208521311978161189709875773440, 13362309030231807834124713984, 59193035415733809139888947200, 13362309030231807834124713984, 13362309030231807834124713984,
    8798363775762990608412573696, 494290099761965764517560320, 118242616564867650319661662208, 118242616564867650319661662208, 302994000783919356639832965120, 4864443600873261359595257856,
    273283348363666368516587520, 1039349629441520014241531166720, 7387759850764447495565082624, 302993903004646550933140930560, 7387759850764447495565082624, 7387759850764447495565082624,
    4864443600873261359595257856, 273283348363666368516587520, 2648185857788794416810770300928, 2648185857788794416810770300928, 309639752326255741259143446528, 202519253301842679346778603520,
    202519253301842679346778603520, 529857679627256591723620466688, 5274309847114721825797288493056, 363131093066744238352367616, 20400623205996867323166720, 18499577381129576948058109771776,
    551496847335448646636273664, 5274309807960284239099980677120, 551496847335448646636273664, 551496847335448646636273664, 363131093066744238352367616, 20400623205996867323166720,
    18874931055603266700533221556224, 18874925206363599569193342599168, 6710588250935527225057509113856, 210179007294920969797716934656, 210179007294920969797716934656, 309639752326255741259143446528,
    18278958392573193121557381120, 20400623205996867323166720, 19975610222538599253934080, 15725480387955918561607680, 494290099761965764517560320, 15725480387955918561607680,
    15725480387955918561607680, 16150493371414186630840320, 16150493371414186630840320, 273283348363666368516587520, 14875454421039382423142400, 494290099761965764517560320,
    273283348363666368516587520, 20400623205996867323166720, 15725480387955918561607680, 14875454421039382423142400, 19975610222538599253934080, 7083135225965131566919188480,
    279913550905615350396616704, 15725480387955918561607680, 24412939529830982123425628160, 425112153154408331782127616
  ]
def negativeScales : Array ℕ := #[
    15, 37, 21, 35, 21, 21,
    19, 15, 12, 12, 33, 18,
    14, 38, 20, 36, 20, 20,
    18, 14, 15, 15, 10, 12,
    12, 14, 54, 11, 7, 53,
    12, 54, 12, 12, 11, 7,
    52, 52, 23, 12, 12, 10,
    9, 7, 11, 10, 15, 10,
    10, 9, 9, 14, 10, 15,
    14, 7, 10, 10, 11, 27,
    14, 10, 32, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15675488477843117, 37396109593983378, 21432155986411672, 35579414096854481, 21432155986411672, 21432155986411672,
    19829293815042335, 15675488477843117, 12577664851767857, 12577664851767857, 33935203988764626, 18974333375367452,
    14820528024633809, 38713523894429226, 20577195532269347, 36935203523191994, 20577195532269347, 20577195532269347,
    18974333375367452, 14820528024633809, 15062847225072904, 15062847225072904, 10966505465643660, 12353973821818172,
    12353973821818172, 14741519654107753, 54056825173561932, 11230620933129867, 7076815597050831, 53867263256967552,
    12833483106919052, 54056825162851921, 12833483106919052, 12833483106919052, 11230620933129867, 7076815597050831,
    52896242320310719, 52896241873227179, 23404282085402416, 12407533331671334, 12407533331671334, 10966505465643660,
    9884170522387776, 7076815597050831, 11046441948007313, 10701306462033270, 15675488477843117, 10701306462033270,
    10701306462033270, 9739780609952834, 9739780609952834, 14820528024633809, 10621136113284685, 15675488477843117,
    14820528024633809, 7076815597050831, 10701306462033270, 10621136113284685, 11046441948007313, 27516446647373747,
    14855111799946705, 10701306462033270, 32301632675430276, 16457973970567442
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
noncomputable def negativeCeiling : ℝ := 9395518907 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 494290099761965764517560320, coefficient := (-494290099761965764517560320) }, { argument := 208521311978161189709875773440, coefficient := (-208521311978161189709875773440) }, { argument := 13362309030231807834124713984, coefficient := (-13362309030231807834124713984) }, { argument := 59193035415733809139888947200, coefficient := (-59193035415733809139888947200) }, { argument := 13362309030231807834124713984, coefficient := (-13362309030231807834124713984) }, { argument := 13362309030231807834124713984, coefficient := (-13362309030231807834124713984) }, { argument := 8798363775762990608412573696, coefficient := (-8798363775762990608412573696) }, { argument := 494290099761965764517560320, coefficient := (-494290099761965764517560320) }, { argument := 118242616564867650319661662208, coefficient := (-118242616564867650319661662208) }, { argument := 118242616564867650319661662208, coefficient := (-118242616564867650319661662208) }, { argument := 302994000783919356639832965120, coefficient := (-302994000783919356639832965120) }, { argument := 4864443600873261359595257856, coefficient := (-4864443600873261359595257856) }, { argument := 273283348363666368516587520, coefficient := (-273283348363666368516587520) }, { argument := 1039349629441520014241531166720, coefficient := (-1039349629441520014241531166720) }, { argument := 7387759850764447495565082624, coefficient := (-7387759850764447495565082624) }, { argument := 302993903004646550933140930560, coefficient := (-302993903004646550933140930560) }, { argument := 7387759850764447495565082624, coefficient := (-7387759850764447495565082624) }, { argument := 7387759850764447495565082624, coefficient := (-7387759850764447495565082624) }, { argument := 4864443600873261359595257856, coefficient := (-4864443600873261359595257856) }, { argument := 273283348363666368516587520, coefficient := (-273283348363666368516587520) }, { argument := 2648185857788794416810770300928, coefficient := (-2648185857788794416810770300928) }, { argument := 2648185857788794416810770300928, coefficient := (-2648185857788794416810770300928) }, { argument := 309639752326255741259143446528, coefficient := (-309639752326255741259143446528) }, { argument := 202519253301842679346778603520, coefficient := (-202519253301842679346778603520) }, { argument := 202519253301842679346778603520, coefficient := (-202519253301842679346778603520) }, { argument := 529857679627256591723620466688, coefficient := (-529857679627256591723620466688) }, { argument := 5274309847114721825797288493056, coefficient := (-5274309847114721825797288493056) }, { argument := 363131093066744238352367616, coefficient := (-363131093066744238352367616) }, { argument := 20400623205996867323166720, coefficient := (-20400623205996867323166720) }, { argument := 18499577381129576948058109771776, coefficient := (-18499577381129576948058109771776) }, { argument := 551496847335448646636273664, coefficient := (-551496847335448646636273664) }, { argument := 5274309807960284239099980677120, coefficient := (-5274309807960284239099980677120) }, { argument := 551496847335448646636273664, coefficient := (-551496847335448646636273664) }, { argument := 551496847335448646636273664, coefficient := (-551496847335448646636273664) }, { argument := 363131093066744238352367616, coefficient := (-363131093066744238352367616) }, { argument := 20400623205996867323166720, coefficient := (-20400623205996867323166720) }, { argument := 18874931055603266700533221556224, coefficient := (-18874931055603266700533221556224) }, { argument := 18874925206363599569193342599168, coefficient := (-18874925206363599569193342599168) }, { argument := 6710588250935527225057509113856, coefficient := (-6710588250935527225057509113856) }, { argument := 210179007294920969797716934656, coefficient := (-210179007294920969797716934656) }, { argument := 210179007294920969797716934656, coefficient := (-210179007294920969797716934656) }, { argument := 309639752326255741259143446528, coefficient := (-309639752326255741259143446528) }, { argument := 18278958392573193121557381120, coefficient := (-18278958392573193121557381120) }, { argument := 20400623205996867323166720, coefficient := (-20400623205996867323166720) }, { argument := 19975610222538599253934080, coefficient := (-19975610222538599253934080) }, { argument := 15725480387955918561607680, coefficient := (-15725480387955918561607680) }, { argument := 494290099761965764517560320, coefficient := (-494290099761965764517560320) }, { argument := 15725480387955918561607680, coefficient := (-15725480387955918561607680) }, { argument := 15725480387955918561607680, coefficient := (-15725480387955918561607680) }, { argument := 16150493371414186630840320, coefficient := (-16150493371414186630840320) }, { argument := 16150493371414186630840320, coefficient := (-16150493371414186630840320) }, { argument := 273283348363666368516587520, coefficient := (-273283348363666368516587520) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 494290099761965764517560320, coefficient := (-494290099761965764517560320) }, { argument := 273283348363666368516587520, coefficient := (-273283348363666368516587520) }, { argument := 20400623205996867323166720, coefficient := (-20400623205996867323166720) }, { argument := 15725480387955918561607680, coefficient := (-15725480387955918561607680) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 19975610222538599253934080, coefficient := (-19975610222538599253934080) }, { argument := 7083135225965131566919188480, coefficient := (-7083135225965131566919188480) }, { argument := 279913550905615350396616704, coefficient := (-279913550905615350396616704) }, { argument := 15725480387955918561607680, coefficient := (-15725480387955918561607680) }, { argument := 24412939529830982123425628160, coefficient := (-24412939529830982123425628160) }, { argument := 425112153154408331782127616, coefficient := (-425112153154408331782127616) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15
