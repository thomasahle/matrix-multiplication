import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 1, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk1

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
def constantNumerator : ℤ := 28506956110653345237105844944896
def positiveArguments : Array ℕ := #[
    5, 402319, 8187443, 8187449, 402329, 111549
  ]
def positiveCoefficients : Array ℕ := #[
    792281625142643375935439503360, 3799795522043265585457922048, 154656425614422786469435277312, 154656538951218375340920406016, 3799889969372922978362195968, 2107101035190504215770300416
  ]
def positiveScales : Array ℕ := #[
    2, 18, 22, 22, 18, 16
  ]
def negativeArguments : Array ℕ := #[
    71142731485, 825966623493, 3303119656337, 35831941055, 4135314999, 266111695899,
    3193822959285, 266112762573, 8645287413, 2907104744585, 134460969582025, 67215838416453,
    731312059465, 266111695899, 534421927359, 12818079799569, 8550786140019, 138862709757,
    71142731485, 2907104744585, 90847089055, 35572278365, 90847089055, 67230534071039,
    67215887684535, 731312590765, 3193822959285, 12818079799569, 9603198565929, 102545068889205,
    1665076157415, 825966623493, 134460969582025, 67230534071039, 3303948562469, 35572278365,
    3303948562469, 3303201711735, 35832852565, 266112762573, 8550786140019, 102545068889205,
    2137705360587, 277726572063, 3303119656337, 67215838416453, 67215887684535, 3303201711735,
    8645287413, 138862709757, 1665076157415, 277726572063, 2255010057, 35831941055,
    731312059465, 731312590765, 35832852565, 1
  ]
def negativeCoefficients : Array ℕ := #[
    20024898687872828346204160, 929955744445885391812165632, 929745528339967125405827072, 20171589547907447164764160, 2327975386069502879858688, 74903783405604196784799744,
    898981243082703801113640960, 74904083647643504647077888, 2433432073231102459772928, 818277240277500434327797760, 37847398281592711705683558400, 37839153105716650091621646336,
    823384179624531003084636160, 74903783405604196784799744, 2406822392912614681491800064, 28863749704472115227092058112, 2406832329619648139665342464, 78172755989660317394141184,
    20024898687872828346204160, 818277240277500434327797760, 818277832831584531183042560, 20025412448666694587514880, 818277832831584531183042560, 37847426023781334481704583168,
    37839180841181117149001809920, 823384777815151508570767360, 898981243082703801113640960, 28863749704472115227092058112, 345991691864661807714923446272, 28863870877381592510606868480,
    937354545259711417527828480, 929955744445885391812165632, 37847398281592711705683558400, 37847426023781334481704583168, 929978844674167145353969664, 20025412448666694587514880,
    929978844674167145353969664, 929768624881208159014748160, 20172102682419490224865280, 74904083647643504647077888, 2406832329619648139665342464, 28863870877381592510606868480,
    2406842266341881246581260288, 78173080403363250284003328, 929745528339967125405827072, 37839153105716650091621646336, 37839180841181117149001809920, 929768624881208159014748160,
    2433432073231102459772928, 78172755989660317394141184, 937354545259711417527828480, 78173080403363250284003328, 2538915613105480236269568, 20171589547907447164764160,
    823384179624531003084636160, 823384777815151508570767360, 20172102682419490224865280, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    36, 39, 41, 35, 31, 37,
    41, 37, 33, 41, 46, 45,
    39, 37, 38, 43, 42, 37,
    36, 41, 36, 35, 36, 45,
    45, 39, 41, 43, 43, 46,
    40, 39, 46, 45, 41, 35,
    41, 41, 35, 37, 42, 46,
    40, 38, 41, 45, 45, 41,
    33, 37, 40, 38, 31, 35,
    39, 39, 35, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 18617980347021960, 22964981526199501, 22964982583448627, 18618016206056990, 16767318054771281
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    36049997315798160, 39587292528685689, 41586966371211597, 35060527146889820, 31945350091490769, 37953240974542930,
    41538421481817786, 37953246757387181, 33009266781117809, 41402720192155853, 46934180794205157, 45933866464227065,
    39411696196278949, 37953240974542930, 38959188258802104, 43543245390101300, 42959194215041885, 37014868273234859,
    36049997315798160, 41402720192155853, 36402721236880656, 35050034329250916, 36402721236880656, 45934181851702120,
    45933867521698085, 39411697244400045, 41538421481817786, 43543245390101300, 43126652147255744, 46543251446666730,
    40598725303585325, 39587292528685689, 46934180794205157, 45934181851702120, 41587328364983358, 35050034329250916,
    41587328364983358, 41587002209890703, 35060563846387310, 37953246757387181, 42959194215041885, 46543251446666730,
    40959200171266185, 38014874260347163, 41586966371211597, 45933866464227065, 45933867521698085, 41587002209890703,
    33009266781117809, 37014868273234859, 40598725303585325, 38014874260347163, 31070486721680520, 35060527146889820,
    39411696196278949, 39411697244400045, 35060563846387310, 0
  ]

abbrev PositiveTerm := Fin 6
abbrev NegativeTerm := Fin 58
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
noncomputable def positiveFloor : ℝ := 109775707 / 1000000000000
noncomputable def negativeCeiling : ℝ := 424255919 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 20024898687872828346204160, coefficient := (-20024898687872828346204160) }, { argument := 929955744445885391812165632, coefficient := (-929955744445885391812165632) }, { argument := 929745528339967125405827072, coefficient := (-929745528339967125405827072) }, { argument := 20171589547907447164764160, coefficient := (-20171589547907447164764160) }, { argument := 2327975386069502879858688, coefficient := (-2327975386069502879858688) }, { argument := 74903783405604196784799744, coefficient := (-74903783405604196784799744) }, { argument := 898981243082703801113640960, coefficient := (-898981243082703801113640960) }, { argument := 74904083647643504647077888, coefficient := (-74904083647643504647077888) }, { argument := 2433432073231102459772928, coefficient := (-2433432073231102459772928) }, { argument := 818277240277500434327797760, coefficient := (-818277240277500434327797760) }, { argument := 37847398281592711705683558400, coefficient := (-37847398281592711705683558400) }, { argument := 37839153105716650091621646336, coefficient := (-37839153105716650091621646336) }, { argument := 823384179624531003084636160, coefficient := (-823384179624531003084636160) }, { argument := 74903783405604196784799744, coefficient := (-74903783405604196784799744) }, { argument := 2406822392912614681491800064, coefficient := (-2406822392912614681491800064) }, { argument := 28863749704472115227092058112, coefficient := (-28863749704472115227092058112) }, { argument := 2406832329619648139665342464, coefficient := (-2406832329619648139665342464) }, { argument := 78172755989660317394141184, coefficient := (-78172755989660317394141184) }, { argument := 20024898687872828346204160, coefficient := (-20024898687872828346204160) }, { argument := 818277240277500434327797760, coefficient := (-818277240277500434327797760) }, { argument := 818277832831584531183042560, coefficient := (-818277832831584531183042560) }, { argument := 20025412448666694587514880, coefficient := (-20025412448666694587514880) }, { argument := 818277832831584531183042560, coefficient := (-818277832831584531183042560) }, { argument := 37847426023781334481704583168, coefficient := (-37847426023781334481704583168) }, { argument := 37839180841181117149001809920, coefficient := (-37839180841181117149001809920) }, { argument := 823384777815151508570767360, coefficient := (-823384777815151508570767360) }, { argument := 898981243082703801113640960, coefficient := (-898981243082703801113640960) }, { argument := 28863749704472115227092058112, coefficient := (-28863749704472115227092058112) }, { argument := 345991691864661807714923446272, coefficient := (-345991691864661807714923446272) }, { argument := 28863870877381592510606868480, coefficient := (-28863870877381592510606868480) }, { argument := 937354545259711417527828480, coefficient := (-937354545259711417527828480) }, { argument := 929955744445885391812165632, coefficient := (-929955744445885391812165632) }, { argument := 37847398281592711705683558400, coefficient := (-37847398281592711705683558400) }, { argument := 37847426023781334481704583168, coefficient := (-37847426023781334481704583168) }, { argument := 929978844674167145353969664, coefficient := (-929978844674167145353969664) }, { argument := 20025412448666694587514880, coefficient := (-20025412448666694587514880) }, { argument := 929978844674167145353969664, coefficient := (-929978844674167145353969664) }, { argument := 929768624881208159014748160, coefficient := (-929768624881208159014748160) }, { argument := 20172102682419490224865280, coefficient := (-20172102682419490224865280) }, { argument := 74904083647643504647077888, coefficient := (-74904083647643504647077888) }, { argument := 2406832329619648139665342464, coefficient := (-2406832329619648139665342464) }, { argument := 28863870877381592510606868480, coefficient := (-28863870877381592510606868480) }, { argument := 2406842266341881246581260288, coefficient := (-2406842266341881246581260288) }, { argument := 78173080403363250284003328, coefficient := (-78173080403363250284003328) }, { argument := 929745528339967125405827072, coefficient := (-929745528339967125405827072) }, { argument := 37839153105716650091621646336, coefficient := (-37839153105716650091621646336) }, { argument := 37839180841181117149001809920, coefficient := (-37839180841181117149001809920) }, { argument := 929768624881208159014748160, coefficient := (-929768624881208159014748160) }, { argument := 2433432073231102459772928, coefficient := (-2433432073231102459772928) }, { argument := 78172755989660317394141184, coefficient := (-78172755989660317394141184) }, { argument := 937354545259711417527828480, coefficient := (-937354545259711417527828480) }, { argument := 78173080403363250284003328, coefficient := (-78173080403363250284003328) }, { argument := 2538915613105480236269568, coefficient := (-2538915613105480236269568) }, { argument := 20171589547907447164764160, coefficient := (-20171589547907447164764160) }, { argument := 823384179624531003084636160, coefficient := (-823384179624531003084636160) }, { argument := 823384777815151508570767360, coefficient := (-823384777815151508570767360) }, { argument := 20172102682419490224865280, coefficient := (-20172102682419490224865280) }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 3799795522043265585457922048, coefficient := 3799795522043265585457922048 }, { argument := 154656425614422786469435277312, coefficient := 154656425614422786469435277312 }, { argument := 154656538951218375340920406016, coefficient := 154656538951218375340920406016 }, { argument := 3799889969372922978362195968, coefficient := 3799889969372922978362195968 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 2107101035190504215770300416, coefficient := 2107101035190504215770300416 }] }

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


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-31683259234475723922322543869952)
def positiveArguments : Array ℕ := #[
    7163883, 85879749, 7163913, 232653, 355035, 16422859,
    8209639, 89315
  ]
def positiveCoefficients : Array ℕ := #[
    67660961932799285124856283136, 811111296469715861342527684608, 67661245274788257303569104896, 2197345458678143135804030976, 3353210768491248976889118720, 155109517788988197449108553728,
    155075696200237885050088062976, 3374225299340018898090065920
  ]
def positiveScales : Array ℕ := #[
    22, 26, 22, 17, 18, 23,
    22, 16
  ]
def negativeArguments : Array ℕ := #[
    3, 1
  ]
def negativeCoefficients : Array ℕ := #[
    950737950171172051122527404032, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    1, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    22772310344830689, 26355814638862059, 22772316386353224, 17827820264759902, 18437601729582122, 23969201966206902,
    22968887352642833, 16446614868538854
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 0
  ]

abbrev PositiveTerm := Fin 8
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 383926429 / 1000000000000
noncomputable def negativeCeiling : ℝ := 18138457 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 67660961932799285124856283136, coefficient := 67660961932799285124856283136 }, { argument := 811111296469715861342527684608, coefficient := 811111296469715861342527684608 }, { argument := 67661245274788257303569104896, coefficient := 67661245274788257303569104896 }, { argument := 2197345458678143135804030976, coefficient := 2197345458678143135804030976 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 3353210768491248976889118720, coefficient := 3353210768491248976889118720 }, { argument := 155109517788988197449108553728, coefficient := 155109517788988197449108553728 }, { argument := 155075696200237885050088062976, coefficient := 155075696200237885050088062976 }, { argument := 3374225299340018898090065920, coefficient := 3374225299340018898090065920 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk1
