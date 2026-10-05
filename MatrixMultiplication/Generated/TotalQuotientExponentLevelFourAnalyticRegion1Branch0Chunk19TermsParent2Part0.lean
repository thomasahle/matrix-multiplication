import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 19, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk19

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    189, 217, 257, 495, 507, 515,
    789, 987, 1031, 2029, 8351, 18617,
    18695, 38591
  ]
def positiveCoefficients : Array ℕ := #[
    1426106925256758076683791106048, 676766964196845971724052423770112, 34543478856219251190785162346496, 289182793177064832216435418726400, 16162545152909924869082965868544, 306929901580260043837389263601664,
    638975130677541882691931959459840, 288707424201979246190874155024384, 307722183205402687213324703105024, 16321001477938453544270053769216, 2646537540626485932974742117023744, 278090850425067824953339265679360,
    279200044700267525679648880984064, 731909765306773950689159013203968
  ]
def positiveScales : Array ℕ := #[
    7, 7, 8, 8, 8, 9,
    9, 9, 10, 10, 13, 14,
    14, 15
  ]
def negativeArguments : Array ℕ := #[
    5, 9, 23, 25, 27, 31,
    49, 51, 103, 107, 123, 129,
    259, 261, 691, 881, 947, 1613,
    1623, 1755, 1891, 2603, 4619, 341663379085
  ]
def negativeCoefficients : Array ℕ := #[
    792281625142643375935439503360, 1426106925256758076683791106048, 3644495475656159529303021715456, 7922816251426433759354395033600, 8556641551540548460102746636288, 9824292151768777861599449841664,
    3882179963198952542083653566464, 16162545152909924869082965868544, 16321001477938453544270053769216, 8477413389026284122509202685952, 9745063989254513524005905891328, 20440865928680199099134339186688,
    20520094091194463436727883137024, 20678550416222992111914971037696, 218986641189426629108555478728704, 279200044700267525679648880984064, 150058139802016655402172241936384, 127795026135508376538386391891968,
    128587307760651019914321831395328, 278090850425067824953339265679360, 149820455314473862389391610085376, 412461814049260141511989805449216, 731909765306773950689159013203968, 1323268770313242966487371058511872
  ]
def negativeScales : Array ℕ := #[
    2, 3, 4, 4, 4, 4,
    5, 5, 6, 6, 6, 7,
    8, 8, 9, 9, 9, 10,
    10, 10, 10, 11, 12, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7562242424220952, 7761551232426566, 8005624549193878, 8951284714309401, 8985841935840350, 9008428622070580,
    9623881490012786, 9946906273845666, 10009828617368108, 10986553148580219, 13027733249752832, 14184332990908866,
    14190364850745531, 15235976808148715
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2321928094887363, 3169925001442313, 4523561956057598, 4643856189792934, 4754887502413606, 4954196321574415,
    5614709844123661, 5672425342008812, 6686500527235738, 6741466986587556, 6942514514520450, 7011227255423255,
    8016808287686554, 8027905996569885, 9432541900388283, 9782998209375365, 9887220618935413, 10655530723180153,
    10664447284578613, 10777255315595305, 10884933651275152, 11345959596404113, 12173364830849037, 38313784665704979
  ]

abbrev PositiveTerm := Fin 14
abbrev NegativeTerm := Fin 24
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
noncomputable def positiveFloor : ℝ := 9251179137 / 10000000000
noncomputable def negativeCeiling : ℝ := 949733851863 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5, coefficient := (-792281625142643375935439503360) }, { argument := 9, coefficient := (-1426106925256758076683791106048) }, { argument := 23, coefficient := (-3644495475656159529303021715456) }, { argument := 25, coefficient := (-7922816251426433759354395033600) }, { argument := 27, coefficient := (-8556641551540548460102746636288) }, { argument := 31, coefficient := (-9824292151768777861599449841664) }, { argument := 49, coefficient := (-3882179963198952542083653566464) }, { argument := 51, coefficient := (-16162545152909924869082965868544) }, { argument := 103, coefficient := (-16321001477938453544270053769216) }, { argument := 107, coefficient := (-8477413389026284122509202685952) }, { argument := 123, coefficient := (-9745063989254513524005905891328) }, { argument := 129, coefficient := (-20440865928680199099134339186688) }, { argument := 189, coefficient := 1426106925256758076683791106048 }, { argument := 217, coefficient := 676766964196845971724052423770112 }, { argument := 257, coefficient := 34543478856219251190785162346496 }, { argument := 259, coefficient := (-20520094091194463436727883137024) }, { argument := 261, coefficient := (-20678550416222992111914971037696) }, { argument := 495, coefficient := 289182793177064832216435418726400 }, { argument := 507, coefficient := 16162545152909924869082965868544 }, { argument := 515, coefficient := 306929901580260043837389263601664 }, { argument := 691, coefficient := (-218986641189426629108555478728704) }, { argument := 789, coefficient := 638975130677541882691931959459840 }, { argument := 881, coefficient := (-279200044700267525679648880984064) }, { argument := 947, coefficient := (-150058139802016655402172241936384) }, { argument := 987, coefficient := 288707424201979246190874155024384 }, { argument := 1031, coefficient := 307722183205402687213324703105024 }, { argument := 1613, coefficient := (-127795026135508376538386391891968) }, { argument := 1623, coefficient := (-128587307760651019914321831395328) }, { argument := 1755, coefficient := (-278090850425067824953339265679360) }, { argument := 1891, coefficient := (-149820455314473862389391610085376) }, { argument := 2029, coefficient := 16321001477938453544270053769216 }, { argument := 2603, coefficient := (-412461814049260141511989805449216) }, { argument := 4619, coefficient := (-731909765306773950689159013203968) }, { argument := 8351, coefficient := 2646537540626485932974742117023744 }, { argument := 18617, coefficient := 278090850425067824953339265679360 }, { argument := 18695, coefficient := 279200044700267525679648880984064 }, { argument := 38591, coefficient := 731909765306773950689159013203968 }, { argument := 341663379085, coefficient := (-1323268770313242966487371058511872) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  rfl

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk19
