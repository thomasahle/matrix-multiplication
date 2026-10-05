import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 3, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk3

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 3045334911241419374903007641600
def positiveArguments : Array ℕ := #[
    11, 16776665, 16777767, 1693039, 96807011, 27099309,
    1827359, 9208815, 73689687, 903689, 22111, 2161417,
    7264937, 2157297, 43763
  ]
def positiveCoefficients : Array ℕ := #[
    1743019575313815427057966907392, 158451120980664552838062407680, 158461529076392797536113393664, 255844820089316520414421188608, 914316368106386111536732045312, 255945737061055444732637872128,
    17258917787540384016108617728, 695798388847155710216990883840, 695979416043910035196612706304, 17070202578151947254078898176, 835329962421845802560258048, 20414006392609319897702334464,
    274461559911676413518823817216, 20375094092790474021141479424, 826659697559297133947912192
  ]
def positiveScales : Array ℕ := #[
    3, 23, 24, 20, 26, 24,
    20, 23, 26, 19, 14, 21,
    22, 21, 15
  ]
def negativeArguments : Array ℕ := #[
    741896617305, 18130679005515, 243762842323985, 18096118516265, 367098000785, 688411393953,
    110864895322585, 110893858751253, 1361724172871, 688411393953, 19641869933741, 5508835567179,
    741896617305, 741947474599, 741947474599, 18131880869557, 243778826777583, 18097319228887,
    367123303023, 19641869933741, 99054819723275, 792644272423821, 9713716858807, 110864895322585,
    99054819723275, 110908939220475, 18130679005515, 18131880869557, 5508835567179, 110908939220475,
    221875805845065, 2724220345275, 110893858751253, 792644272423821, 221875805845065, 243762842323985,
    243778826777583, 1361724172871, 9713716858807, 2724220345275, 18096118516265, 18097319228887,
    367098000785, 367123303023, 1, 9, 9, 1
  ]
def negativeCoefficients : Array ℕ := #[
    208825333077639342147502080, 5103332450825714311983267840, 68613140366066988573953884160, 5093604537918961684934819840, 206657802442972506011729920, 1550164648642167261672505344,
    62411387657907856366653931520, 62427692618727428459316903936, 1533165119380808119567253504, 1550164648642167261672505344, 5528694882153482284848644096, 1550599362974542461533159424,
    208825333077639342147502080, 208839648133283559132626944, 208839648133283559132626944, 5103670745478945636867899392, 68617639589771218185458024448, 5093942508476275325635919872,
    206672046336676060962226176, 5528694882153482284848644096, 223051624597496473853309747200, 223109528120329885866918936576, 5468336453213213763288694784, 62411387657907856366653931520,
    223051624597496473853309747200, 62436182168173524888531763200, 5103332450825714311983267840, 5103670745478945636867899392, 1550599362974542461533159424, 62436182168173524888531763200,
    62452487282897703272070512640, 1533599716481951744183500800, 62427692618727428459316903936, 223109528120329885866918936576, 62452487282897703272070512640, 68613140366066988573953884160,
    68617639589771218185458024448, 1533165119380808119567253504, 5468336453213213763288694784, 1533599716481951744183500800, 5093604537918961684934819840, 5093942508476275325635919872,
    206657802442972506011729920, 206672046336676060962226176, 316912650057057350374175801344, 1426106925256758076683791106048, 1426106925256758076683791106048, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    39, 44, 47, 44, 38, 39,
    46, 46, 40, 39, 44, 42,
    39, 39, 39, 44, 47, 44,
    38, 44, 46, 49, 43, 46,
    46, 46, 44, 44, 42, 46,
    47, 41, 46, 49, 47, 47,
    47, 40, 43, 41, 44, 44,
    38, 38, 0, 3, 3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3459431618637292, 23999952616543138, 24000047380442278, 20691183776138570, 26528608198990866, 24691752729256244,
    20801328660632548, 23134584090069135, 26134959389976316, 19785466836257743, 14432476654021382, 21043546006072685,
    22792518856455357, 21040793378613849, 15417424019342894
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    39432427206223190, 44043498189480756, 47792471556327482, 44040745516598312, 38417374301305461, 39324480019499729,
    46655795945873083, 46656172800399928, 40308571643223968, 39324480019499729, 44158997516330697, 42324884539297612,
    39432427206223190, 39432526100124882, 39432526100124882, 44043593821079839, 47792566156209585, 44040841239041597,
    38417473735667039, 44158997516330697, 46493292407759205, 49493666878397012, 43143160573090244, 46655795945873083,
    46493292407759205, 46656368979333711, 44043498189480756, 44043593821079839, 42324884539297612, 46656368979333711,
    47656745687779811, 41308980537365096, 46656172800399928, 49493666878397012, 47656745687779811, 47792471556327482,
    47792566156209585, 40308571643223968, 43143160573090244, 41308980537365096, 44040745516598312, 44040841239041597,
    38417374301305461, 38417473735667039, 0, 3169925001442313, 3169925001442313, 0
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 48
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
noncomputable def positiveFloor : ℝ := 8616533 / 7812500000
noncomputable def negativeCeiling : ℝ := 1104240579 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 208825333077639342147502080, coefficient := (-208825333077639342147502080) }, { argument := 5103332450825714311983267840, coefficient := (-5103332450825714311983267840) }, { argument := 68613140366066988573953884160, coefficient := (-68613140366066988573953884160) }, { argument := 5093604537918961684934819840, coefficient := (-5093604537918961684934819840) }, { argument := 206657802442972506011729920, coefficient := (-206657802442972506011729920) }, { argument := 1550164648642167261672505344, coefficient := (-1550164648642167261672505344) }, { argument := 62411387657907856366653931520, coefficient := (-62411387657907856366653931520) }, { argument := 62427692618727428459316903936, coefficient := (-62427692618727428459316903936) }, { argument := 1533165119380808119567253504, coefficient := (-1533165119380808119567253504) }, { argument := 1550164648642167261672505344, coefficient := (-1550164648642167261672505344) }, { argument := 5528694882153482284848644096, coefficient := (-5528694882153482284848644096) }, { argument := 1550599362974542461533159424, coefficient := (-1550599362974542461533159424) }, { argument := 208825333077639342147502080, coefficient := (-208825333077639342147502080) }, { argument := 208839648133283559132626944, coefficient := (-208839648133283559132626944) }, { argument := 208839648133283559132626944, coefficient := (-208839648133283559132626944) }, { argument := 5103670745478945636867899392, coefficient := (-5103670745478945636867899392) }, { argument := 68617639589771218185458024448, coefficient := (-68617639589771218185458024448) }, { argument := 5093942508476275325635919872, coefficient := (-5093942508476275325635919872) }, { argument := 206672046336676060962226176, coefficient := (-206672046336676060962226176) }, { argument := 5528694882153482284848644096, coefficient := (-5528694882153482284848644096) }, { argument := 223051624597496473853309747200, coefficient := (-223051624597496473853309747200) }, { argument := 223109528120329885866918936576, coefficient := (-223109528120329885866918936576) }, { argument := 5468336453213213763288694784, coefficient := (-5468336453213213763288694784) }, { argument := 62411387657907856366653931520, coefficient := (-62411387657907856366653931520) }, { argument := 223051624597496473853309747200, coefficient := (-223051624597496473853309747200) }, { argument := 62436182168173524888531763200, coefficient := (-62436182168173524888531763200) }, { argument := 5103332450825714311983267840, coefficient := (-5103332450825714311983267840) }, { argument := 5103670745478945636867899392, coefficient := (-5103670745478945636867899392) }, { argument := 1550599362974542461533159424, coefficient := (-1550599362974542461533159424) }, { argument := 62436182168173524888531763200, coefficient := (-62436182168173524888531763200) }, { argument := 62452487282897703272070512640, coefficient := (-62452487282897703272070512640) }, { argument := 1533599716481951744183500800, coefficient := (-1533599716481951744183500800) }, { argument := 62427692618727428459316903936, coefficient := (-62427692618727428459316903936) }, { argument := 223109528120329885866918936576, coefficient := (-223109528120329885866918936576) }, { argument := 62452487282897703272070512640, coefficient := (-62452487282897703272070512640) }, { argument := 68613140366066988573953884160, coefficient := (-68613140366066988573953884160) }, { argument := 68617639589771218185458024448, coefficient := (-68617639589771218185458024448) }, { argument := 1533165119380808119567253504, coefficient := (-1533165119380808119567253504) }, { argument := 5468336453213213763288694784, coefficient := (-5468336453213213763288694784) }, { argument := 1533599716481951744183500800, coefficient := (-1533599716481951744183500800) }, { argument := 5093604537918961684934819840, coefficient := (-5093604537918961684934819840) }, { argument := 5093942508476275325635919872, coefficient := (-5093942508476275325635919872) }, { argument := 206657802442972506011729920, coefficient := (-206657802442972506011729920) }, { argument := 206672046336676060962226176, coefficient := (-206672046336676060962226176) }, { argument := 1743019575313815427057966907392, coefficient := 1743019575313815427057966907392 }, { argument := 158451120980664552838062407680, coefficient := 158451120980664552838062407680 }, { argument := 158461529076392797536113393664, coefficient := 158461529076392797536113393664 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 255844820089316520414421188608, coefficient := 255844820089316520414421188608 }, { argument := 914316368106386111536732045312, coefficient := 914316368106386111536732045312 }, { argument := 255945737061055444732637872128, coefficient := 255945737061055444732637872128 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 17258917787540384016108617728, coefficient := 17258917787540384016108617728 }, { argument := 695798388847155710216990883840, coefficient := 695798388847155710216990883840 }, { argument := 695979416043910035196612706304, coefficient := 695979416043910035196612706304 }, { argument := 17070202578151947254078898176, coefficient := 17070202578151947254078898176 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 835329962421845802560258048, coefficient := 835329962421845802560258048 }, { argument := 20414006392609319897702334464, coefficient := 20414006392609319897702334464 }, { argument := 274461559911676413518823817216, coefficient := 274461559911676413518823817216 }, { argument := 20375094092790474021141479424, coefficient := 20375094092790474021141479424 }, { argument := 826659697559297133947912192, coefficient := 826659697559297133947912192 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk3
