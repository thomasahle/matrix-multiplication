import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 15, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk15

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
    129, 687, 1367, 1521, 1903, 2227,
    2237, 3087, 7669, 9115, 9191, 12351,
    33981, 34757, 34877
  ]
def positiveCoefficients : Array ℕ := #[
    31691265005705735037417580134400, 474972834273014703873295982264320, 474180552647872060497360542760960, 110127145894827429255026090967040, 2203889796659291078839612066496512, 352486095025962037953677035044864,
    352248410538419244940896403193856, 111949393632655509019677601824768, 2199928388533577861959934868979712, 2324554288168515664994579502858240, 2324554288168515664994579502858240, 2494498696761612669132731276328960,
    10769008761588865823064867905470464, 1330399304939526756870790014042112, 1334994538365354088451215563161600
  ]
def positiveScales : Array ℕ := #[
    7, 9, 10, 10, 10, 11,
    11, 11, 12, 13, 13, 13,
    15, 15, 15
  ]
def negativeArguments : Array ℕ := #[
    3, 5, 11, 21, 29, 55,
    57, 59, 111, 113, 115, 119,
    163, 283, 321, 325, 363, 573,
    695, 709, 961, 1223, 1227, 1413,
    1801, 2099, 3851, 7215, 8425, 10317,
    31485, 3997250738227
  ]
def negativeCoefficients : Array ℕ := #[
    950737950171172051122527404032, 1584563250285286751870879006720, 1743019575313815427057966907392, 1663791412799551089464422957056, 4595233425827331580425549119488, 4357548938284538567644917268480,
    4516005263313067242832005169152, 4674461588341595918019093069824, 8794326039083341472883378487296, 8952782364111870148070466387968, 9111238689140398823257554288640, 9428151339197456173631730089984,
    103313523918600696221981311238144, 44843139983073615077945875890176, 813831685346523275760883457851392, 102996611268543638871607135436800, 57519645985355909092912907943936, 45397737120673465441100683542528,
    110127145894827429255026090967040, 56172767222613415353822660788224, 304553056704832113709582945091584, 193792085509890569753808502521856, 194425910810004684454556854124544, 111949393632655509019677601824768,
    1141519365505520576047781236441088, 1330399304939526756870790014042112, 305107653842431964072737752743936, 1143262385080834391474839203348480, 1334994538365354088451215563161600, 817396952659665170952592935616512,
    2494498696761612669132731276328960, 5384504380794432911532433952735232
  ]
def negativeScales : Array ℕ := #[
    1, 2, 3, 4, 4, 5,
    5, 5, 6, 6, 6, 6,
    7, 8, 8, 8, 8, 9,
    9, 9, 9, 10, 10, 10,
    10, 11, 11, 12, 13, 13,
    14, 41
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7011227255423254, 9424166288818098, 10416797527606058, 10570804437724342, 10894059846031384, 11120885842787789,
    11127349541059118, 11591989767614842, 12904822753999971, 13154026940926496, 13166006122950490, 13592340234042140,
    15052440688628755, 15085015942947346, 15089988329318507
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 2321928094887363, 3459431618637364, 4392317422778766, 4857980997143165, 5781359713964302,
    5832890015409720, 5882643052550791, 6794415866926375, 6820178963384638, 6845490052533228, 6894817767286876,
    7348728154231079, 8144658242831883, 8326429487122304, 8344295907915818, 8503825737996059, 9162391328756905,
    9440869167610903, 9469641817239612, 9908392625846646, 10256208688527387, 10260919533662906, 10464545750334019,
    10814582466773464, 11035486451292155, 11911017413111362, 12816783680284705, 13040460970956584, 13332735901247948,
    14942377056060408, 41862145213324366
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 32
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
noncomputable def positiveFloor : ℝ := 4450591598153 / 1000000000000
noncomputable def negativeCeiling : ℝ := 4286134892383 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-950737950171172051122527404032) }, { argument := 5, coefficient := (-1584563250285286751870879006720) }, { argument := 11, coefficient := (-1743019575313815427057966907392) }, { argument := 21, coefficient := (-1663791412799551089464422957056) }, { argument := 29, coefficient := (-4595233425827331580425549119488) }, { argument := 55, coefficient := (-4357548938284538567644917268480) }, { argument := 57, coefficient := (-4516005263313067242832005169152) }, { argument := 59, coefficient := (-4674461588341595918019093069824) }, { argument := 111, coefficient := (-8794326039083341472883378487296) }, { argument := 113, coefficient := (-8952782364111870148070466387968) }, { argument := 115, coefficient := (-9111238689140398823257554288640) }, { argument := 119, coefficient := (-9428151339197456173631730089984) }, { argument := 129, coefficient := 31691265005705735037417580134400 }, { argument := 163, coefficient := (-103313523918600696221981311238144) }, { argument := 283, coefficient := (-44843139983073615077945875890176) }, { argument := 321, coefficient := (-813831685346523275760883457851392) }, { argument := 325, coefficient := (-102996611268543638871607135436800) }, { argument := 363, coefficient := (-57519645985355909092912907943936) }, { argument := 573, coefficient := (-45397737120673465441100683542528) }, { argument := 687, coefficient := 474972834273014703873295982264320 }, { argument := 695, coefficient := (-110127145894827429255026090967040) }, { argument := 709, coefficient := (-56172767222613415353822660788224) }, { argument := 961, coefficient := (-304553056704832113709582945091584) }, { argument := 1223, coefficient := (-193792085509890569753808502521856) }, { argument := 1227, coefficient := (-194425910810004684454556854124544) }, { argument := 1367, coefficient := 474180552647872060497360542760960 }, { argument := 1413, coefficient := (-111949393632655509019677601824768) }, { argument := 1521, coefficient := 110127145894827429255026090967040 }, { argument := 1801, coefficient := (-1141519365505520576047781236441088) }, { argument := 1903, coefficient := 2203889796659291078839612066496512 }, { argument := 2099, coefficient := (-1330399304939526756870790014042112) }, { argument := 2227, coefficient := 352486095025962037953677035044864 }, { argument := 2237, coefficient := 352248410538419244940896403193856 }, { argument := 3087, coefficient := 111949393632655509019677601824768 }, { argument := 3851, coefficient := (-305107653842431964072737752743936) }, { argument := 7215, coefficient := (-1143262385080834391474839203348480) }, { argument := 7669, coefficient := 2199928388533577861959934868979712 }, { argument := 8425, coefficient := (-1334994538365354088451215563161600) }, { argument := 9115, coefficient := 2324554288168515664994579502858240 }, { argument := 9191, coefficient := 2324554288168515664994579502858240 }, { argument := 10317, coefficient := (-817396952659665170952592935616512) }, { argument := 12351, coefficient := 2494498696761612669132731276328960 }, { argument := 31485, coefficient := (-2494498696761612669132731276328960) }, { argument := 33981, coefficient := 10769008761588865823064867905470464 }, { argument := 34757, coefficient := 1330399304939526756870790014042112 }, { argument := 34877, coefficient := 1334994538365354088451215563161600 }, { argument := 3997250738227, coefficient := (-5384504380794432911532433952735232) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk15
