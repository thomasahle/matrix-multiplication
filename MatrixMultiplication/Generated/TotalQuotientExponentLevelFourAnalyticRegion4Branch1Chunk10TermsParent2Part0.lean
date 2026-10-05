import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 10, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk10

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
def constantNumerator : ℤ := 282809986053684550070565863424
def positiveArguments : Array ℕ := #[
    5, 8388629, 8388587, 1538515, 5311313, 384695,
    107027, 8174549, 32702969, 851483, 18885, 1283667,
    14134327, 1283687, 37765
  ]
def positiveCoefficients : Array ℕ := #[
    792281625142643375935439503360, 79228360853656618118642925568, 79227964174872057068444975104, 116246906710275075295192023040, 401311463859677182862261485568, 116266929544162442590898094080,
    8086731480993432292579868672, 308825729681404603295787384832, 308870809391850076928997326848, 8042029559866588230987022336, 356727564115972999442595840, 12123892031931657725059006464,
    133494944165438927648728285184, 12124080926590972510867554304, 356680340451144302990458880
  ]
def positiveScales : Array ℕ := #[
    2, 23, 22, 20, 22, 18,
    16, 22, 24, 19, 14, 20,
    23, 20, 15
  ]
def negativeArguments : Array ℕ := #[
    158419258665, 10768206222543, 118567625367683, 10768373995123, 316796574185, 658886807255,
    25153096327825, 100627035390445, 2621019863155, 658886807255, 2273348647135, 329497369637,
    158419258665, 158418465495, 158418465495, 10768152308529, 118567031725949, 10768320080269,
    316794988055, 2273348647135, 86835643593437, 347393348483369, 9043046111207, 25153096327825,
    86835643593437, 12578717177161, 10768206222543, 10768152308529, 329497369637, 12578717177161,
    50322195440245, 1310724118483, 100627035390445, 347393348483369, 50322195440245, 118567625367683,
    118567031725949, 2621019863155, 9043046111207, 1310724118483, 10768373995123, 10768320080269,
    316796574185, 316794988055, 1, 1, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    89182114286500527451668480, 3030980595705831945255518208, 33373819589006357973904130048, 3031027819488880131926130688, 89170308340738480784015360, 741840594908238455106437120,
    28319868812301715324587212800, 28323992442987863466752081920, 737751504939720401150279680, 741840594908238455106437120, 2559563030030101799753482240, 741962115558375891430014976,
    89182114286500527451668480, 89181667771485972269629440, 89181667771485972269629440, 3030965420259996917273985024, 33373652493713105850460012544, 3031012643806606123507646464,
    89169861884833670711214080, 2559563030030101799753482240, 97768243032470017864198258688, 97782534673793093133941080064, 2545391193545378633237921792, 28319868812301715324587212800,
    97768243032470017864198258688, 28324752995930568459108220928, 3030980595705831945255518208, 3030965420259996917273985024, 741962115558375891430014976, 28324752995930568459108220928,
    28328877579144081863805501440, 737872081448195081105309696, 28323992442987863466752081920, 97782534673793093133941080064, 28328877579144081863805501440, 33373819589006357973904130048,
    33373652493713105850460012544, 737751504939720401150279680, 2545391193545378633237921792, 737872081448195081105309696, 3031027819488880131926130688, 3031012643806606123507646464,
    89170308340738480784015360, 89169861884833670711214080, 158456325028528675187087900672, 633825300114114700748351602688, 633825300114114700748351602688, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    37, 43, 46, 43, 38, 39,
    44, 46, 41, 39, 41, 38,
    37, 37, 37, 43, 46, 43,
    38, 41, 46, 48, 43, 44,
    46, 43, 43, 43, 38, 43,
    45, 40, 46, 48, 45, 46,
    46, 41, 43, 40, 43, 43,
    38, 38, 0, 0, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 23000003611631147, 22999996386900313, 20553107078851971, 22340637120453656, 18553355553039061,
    16707615269677763, 22962707706061018, 24962918282840536, 19699618200976780, 14204953163327534, 20291839566366545,
    23752699855687199, 20291862043906315, 15204762166432983
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    37204956774958683, 43291843177997694, 46752703467571682, 43291865655537464, 38204765778064131, 39261239684050049,
    44515801239206774, 46516011293444607, 41253265425686152, 39261239684050049, 41047956095536454, 38261475992069267,
    37204956774958683, 37204949551687347, 37204949551687347, 43291835954726358, 46752696244300308, 43291858432266127,
    38204758554792795, 41047956095536454, 46303352583581407, 48303563459552769, 43039945958777368, 44515801239206774,
    46303352583581407, 43516050032023912, 43291843177997694, 43291835954726358, 38261475992069267, 43516050032023912,
    45516260098552679, 40253501197373208, 46516011293444607, 48303563459552769, 45516260098552679, 46752703467571682,
    46752696244300308, 41253265425686152, 43039945958777368, 40253501197373208, 43291865655537464, 43291858432266127,
    38204765778064131, 38204758554792795, 0, 0, 0, 0
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
noncomputable def positiveFloor : ℝ := 454576833 / 1000000000000
noncomputable def negativeCeiling : ℝ := 441559449 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 89182114286500527451668480, coefficient := (-89182114286500527451668480) }, { argument := 3030980595705831945255518208, coefficient := (-3030980595705831945255518208) }, { argument := 33373819589006357973904130048, coefficient := (-33373819589006357973904130048) }, { argument := 3031027819488880131926130688, coefficient := (-3031027819488880131926130688) }, { argument := 89170308340738480784015360, coefficient := (-89170308340738480784015360) }, { argument := 741840594908238455106437120, coefficient := (-741840594908238455106437120) }, { argument := 28319868812301715324587212800, coefficient := (-28319868812301715324587212800) }, { argument := 28323992442987863466752081920, coefficient := (-28323992442987863466752081920) }, { argument := 737751504939720401150279680, coefficient := (-737751504939720401150279680) }, { argument := 741840594908238455106437120, coefficient := (-741840594908238455106437120) }, { argument := 2559563030030101799753482240, coefficient := (-2559563030030101799753482240) }, { argument := 741962115558375891430014976, coefficient := (-741962115558375891430014976) }, { argument := 89182114286500527451668480, coefficient := (-89182114286500527451668480) }, { argument := 89181667771485972269629440, coefficient := (-89181667771485972269629440) }, { argument := 89181667771485972269629440, coefficient := (-89181667771485972269629440) }, { argument := 3030965420259996917273985024, coefficient := (-3030965420259996917273985024) }, { argument := 33373652493713105850460012544, coefficient := (-33373652493713105850460012544) }, { argument := 3031012643806606123507646464, coefficient := (-3031012643806606123507646464) }, { argument := 89169861884833670711214080, coefficient := (-89169861884833670711214080) }, { argument := 2559563030030101799753482240, coefficient := (-2559563030030101799753482240) }, { argument := 97768243032470017864198258688, coefficient := (-97768243032470017864198258688) }, { argument := 97782534673793093133941080064, coefficient := (-97782534673793093133941080064) }, { argument := 2545391193545378633237921792, coefficient := (-2545391193545378633237921792) }, { argument := 28319868812301715324587212800, coefficient := (-28319868812301715324587212800) }, { argument := 97768243032470017864198258688, coefficient := (-97768243032470017864198258688) }, { argument := 28324752995930568459108220928, coefficient := (-28324752995930568459108220928) }, { argument := 3030980595705831945255518208, coefficient := (-3030980595705831945255518208) }, { argument := 3030965420259996917273985024, coefficient := (-3030965420259996917273985024) }, { argument := 741962115558375891430014976, coefficient := (-741962115558375891430014976) }, { argument := 28324752995930568459108220928, coefficient := (-28324752995930568459108220928) }, { argument := 28328877579144081863805501440, coefficient := (-28328877579144081863805501440) }, { argument := 737872081448195081105309696, coefficient := (-737872081448195081105309696) }, { argument := 28323992442987863466752081920, coefficient := (-28323992442987863466752081920) }, { argument := 97782534673793093133941080064, coefficient := (-97782534673793093133941080064) }, { argument := 28328877579144081863805501440, coefficient := (-28328877579144081863805501440) }, { argument := 33373819589006357973904130048, coefficient := (-33373819589006357973904130048) }, { argument := 33373652493713105850460012544, coefficient := (-33373652493713105850460012544) }, { argument := 737751504939720401150279680, coefficient := (-737751504939720401150279680) }, { argument := 2545391193545378633237921792, coefficient := (-2545391193545378633237921792) }, { argument := 737872081448195081105309696, coefficient := (-737872081448195081105309696) }, { argument := 3031027819488880131926130688, coefficient := (-3031027819488880131926130688) }, { argument := 3031012643806606123507646464, coefficient := (-3031012643806606123507646464) }, { argument := 89170308340738480784015360, coefficient := (-89170308340738480784015360) }, { argument := 89169861884833670711214080, coefficient := (-89169861884833670711214080) }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 79228360853656618118642925568, coefficient := 79228360853656618118642925568 }, { argument := 79227964174872057068444975104, coefficient := 79227964174872057068444975104 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 116246906710275075295192023040, coefficient := 116246906710275075295192023040 }, { argument := 401311463859677182862261485568, coefficient := 401311463859677182862261485568 }, { argument := 116266929544162442590898094080, coefficient := 116266929544162442590898094080 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 8086731480993432292579868672, coefficient := 8086731480993432292579868672 }, { argument := 308825729681404603295787384832, coefficient := 308825729681404603295787384832 }, { argument := 308870809391850076928997326848, coefficient := 308870809391850076928997326848 }, { argument := 8042029559866588230987022336, coefficient := 8042029559866588230987022336 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 356727564115972999442595840, coefficient := 356727564115972999442595840 }, { argument := 12123892031931657725059006464, coefficient := 12123892031931657725059006464 }, { argument := 133494944165438927648728285184, coefficient := 133494944165438927648728285184 }, { argument := 12124080926590972510867554304, coefficient := 12124080926590972510867554304 }, { argument := 356680340451144302990458880, coefficient := 356680340451144302990458880 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk10
