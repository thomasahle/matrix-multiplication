import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 5, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 29914673409265493906349375881216
def positiveArguments : Array ℕ := #[
    15, 257, 1025, 509, 1025, 5,
    1, 1, 1, 1
  ]
def positiveCoefficients : Array ℕ := #[
    1188422437713965063903159255040, 39768823762042841331134365696, 39652766883359836930362572800, 39381967499766159995228389376, 39652766883359836930362572800, 792281625142643375935439503360,
    39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168
  ]
def positiveScales : Array ℕ := #[
    3, 8, 10, 8, 10, 2,
    0, 0, 0, 0
  ]
def negativeArguments : Array ℕ := #[
    2575, 1658925, 22995397, 91838917, 45753009, 91838917,
    17643365, 4280360507, 17096418875, 8519015759, 17096418875, 126325508929,
    5709683187079, 15874968295, 829465, 1070090191, 4274104975, 2129754067,
    4274104975, 5709683187079, 258067292767729, 717519686545, 22995397, 4280360507,
    1070090191, 5748785, 91838917, 17096418875, 4274104975, 22959473,
    2575, 5748785, 22959473, 11438125, 22959473, 15874968295,
    717519686545, 1994962225, 45753009, 8519015759, 2129754067, 11438125,
    91838917, 17096418875, 4274104975, 22959473, 2575, 1658925,
    17643365, 829465, 2575, 1, 5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    97280749547114691402137600, 31336207270378104744522547200, 106047550833087100525477888, 105883062369103337060564992, 105499255953141222309101568, 105883062369103337060564992,
    333273742084141591702966108160, 19739678703960665431451107328, 19710828972753898094723072000, 19643512933271440975690989568, 19710828972753898094723072000, 35557469683752041577447424,
    1607132942108285650100813824, 35747250648940219109212160, 31336301717707762137426821120, 19739679889163972167289798656, 19710830154498440316741222400, 19643514106945532665461211136,
    19710830154498440316741222400, 1607132942108285650100813824, 72639485221578563858647220224, 1615710696477528546250588160, 106047550833087100525477888, 19739678703960665431451107328,
    19739679889163972167289798656, 106046365629780364686786560, 105883062369103337060564992, 19710828972753898094723072000, 19710830154498440316741222400, 105881880624561115042414592,
    97280749547114691402137600, 106046365629780364686786560, 105881880624561115042414592, 105498082279049532538880000, 105881880624561115042414592, 35747250648940219109212160,
    1615710696477528546250588160, 35938044532512862398054400, 105499255953141222309101568, 19643512933271440975690989568, 19643514106945532665461211136, 105498082279049532538880000,
    105883062369103337060564992, 19710828972753898094723072000, 19710830154498440316741222400, 105881880624561115042414592, 97280749547114691402137600, 31336207270378104744522547200,
    333273742084141591702966108160, 31336301717707762137426821120, 97280749547114691402137600, 158456325028528675187087900672, 792281625142643375935439503360, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    11, 20, 24, 26, 25, 26,
    24, 31, 33, 32, 33, 36,
    42, 33, 19, 29, 31, 30,
    31, 42, 47, 39, 24, 31,
    29, 22, 26, 33, 31, 24,
    11, 22, 24, 23, 24, 33,
    39, 30, 25, 32, 30, 23,
    26, 33, 31, 24, 11, 20,
    24, 19, 11, 0, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3906890595303263, 8005624549193878, 10001408194392808, 8991521844801183, 10001408194392808, 2321928094887362,
    0, 0, 0, 0
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    11330356716957944, 20661817232877547, 24454841769300047, 26452602293508054, 25447363291250383, 26452602293508054,
    24072622406843594, 31995085186461991, 33992975130678611, 32988039632424612, 33992975130678611, 36878355038877763,
    42376547835705762, 33886034662847889, 19661821581153894, 29995085273083841, 31992975217174086, 30988039718623770,
    31992975217174086, 42376547835705762, 47874740638238451, 39384227459230448, 24454841769300047, 31995085186461991,
    29995085273083841, 22454825645434152, 26452602293508054, 33992975130678611, 31992975217174086, 24452586191721171,
    11330356716957944, 22454825645434152, 24452586191721171, 23447347241248938, 24452586191721171, 33886034662847889,
    39384227459230448, 30893714286880126, 25447363291250383, 32988039632424612, 30988039718623770, 23447347241248938,
    26452602293508054, 33992975130678611, 31992975217174086, 24452586191721171, 11330356716957944, 20661817232877547,
    24072622406843594, 19661821581153894, 11330356716957944, 0, 2321928094887363, 0
  ]

abbrev PositiveTerm := Fin 10
abbrev NegativeTerm := Fin 54
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
noncomputable def positiveFloor : ℝ := 95674211 / 1000000000000
noncomputable def negativeCeiling : ℝ := 82737507 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 97280749547114691402137600, coefficient := (-97280749547114691402137600) }, { argument := 31336207270378104744522547200, coefficient := (-31336207270378104744522547200) }, { argument := 106047550833087100525477888, coefficient := (-106047550833087100525477888) }, { argument := 105883062369103337060564992, coefficient := (-105883062369103337060564992) }, { argument := 105499255953141222309101568, coefficient := (-105499255953141222309101568) }, { argument := 105883062369103337060564992, coefficient := (-105883062369103337060564992) }, { argument := 333273742084141591702966108160, coefficient := (-333273742084141591702966108160) }, { argument := 19739678703960665431451107328, coefficient := (-19739678703960665431451107328) }, { argument := 19710828972753898094723072000, coefficient := (-19710828972753898094723072000) }, { argument := 19643512933271440975690989568, coefficient := (-19643512933271440975690989568) }, { argument := 19710828972753898094723072000, coefficient := (-19710828972753898094723072000) }, { argument := 35557469683752041577447424, coefficient := (-35557469683752041577447424) }, { argument := 1607132942108285650100813824, coefficient := (-1607132942108285650100813824) }, { argument := 35747250648940219109212160, coefficient := (-35747250648940219109212160) }, { argument := 31336301717707762137426821120, coefficient := (-31336301717707762137426821120) }, { argument := 19739679889163972167289798656, coefficient := (-19739679889163972167289798656) }, { argument := 19710830154498440316741222400, coefficient := (-19710830154498440316741222400) }, { argument := 19643514106945532665461211136, coefficient := (-19643514106945532665461211136) }, { argument := 19710830154498440316741222400, coefficient := (-19710830154498440316741222400) }, { argument := 1607132942108285650100813824, coefficient := (-1607132942108285650100813824) }, { argument := 72639485221578563858647220224, coefficient := (-72639485221578563858647220224) }, { argument := 1615710696477528546250588160, coefficient := (-1615710696477528546250588160) }, { argument := 106047550833087100525477888, coefficient := (-106047550833087100525477888) }, { argument := 19739678703960665431451107328, coefficient := (-19739678703960665431451107328) }, { argument := 19739679889163972167289798656, coefficient := (-19739679889163972167289798656) }, { argument := 106046365629780364686786560, coefficient := (-106046365629780364686786560) }, { argument := 105883062369103337060564992, coefficient := (-105883062369103337060564992) }, { argument := 19710828972753898094723072000, coefficient := (-19710828972753898094723072000) }, { argument := 19710830154498440316741222400, coefficient := (-19710830154498440316741222400) }, { argument := 105881880624561115042414592, coefficient := (-105881880624561115042414592) }, { argument := 97280749547114691402137600, coefficient := (-97280749547114691402137600) }, { argument := 106046365629780364686786560, coefficient := (-106046365629780364686786560) }, { argument := 105881880624561115042414592, coefficient := (-105881880624561115042414592) }, { argument := 105498082279049532538880000, coefficient := (-105498082279049532538880000) }, { argument := 105881880624561115042414592, coefficient := (-105881880624561115042414592) }, { argument := 35747250648940219109212160, coefficient := (-35747250648940219109212160) }, { argument := 1615710696477528546250588160, coefficient := (-1615710696477528546250588160) }, { argument := 35938044532512862398054400, coefficient := (-35938044532512862398054400) }, { argument := 105499255953141222309101568, coefficient := (-105499255953141222309101568) }, { argument := 19643512933271440975690989568, coefficient := (-19643512933271440975690989568) }, { argument := 19643514106945532665461211136, coefficient := (-19643514106945532665461211136) }, { argument := 105498082279049532538880000, coefficient := (-105498082279049532538880000) }, { argument := 105883062369103337060564992, coefficient := (-105883062369103337060564992) }, { argument := 19710828972753898094723072000, coefficient := (-19710828972753898094723072000) }, { argument := 19710830154498440316741222400, coefficient := (-19710830154498440316741222400) }, { argument := 105881880624561115042414592, coefficient := (-105881880624561115042414592) }, { argument := 97280749547114691402137600, coefficient := (-97280749547114691402137600) }, { argument := 31336207270378104744522547200, coefficient := (-31336207270378104744522547200) }, { argument := 333273742084141591702966108160, coefficient := (-333273742084141591702966108160) }, { argument := 31336301717707762137426821120, coefficient := (-31336301717707762137426821120) }, { argument := 97280749547114691402137600, coefficient := (-97280749547114691402137600) }, { argument := 1188422437713965063903159255040, coefficient := 1188422437713965063903159255040 }, { argument := 39768823762042841331134365696, coefficient := 39768823762042841331134365696 }, { argument := 39652766883359836930362572800, coefficient := 39652766883359836930362572800 }, { argument := 39381967499766159995228389376, coefficient := 39381967499766159995228389376 }, { argument := 39652766883359836930362572800, coefficient := 39652766883359836930362572800 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent3

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-28607408727780132336055900700672)
def positiveArguments : Array ℕ := #[
    2575, 1658925, 17643365, 829465, 2575, 11205,
    2085947, 16687577, 89639, 355423, 16064473, 44665
  ]
def positiveCoefficients : Array ℕ := #[
    194561499094229382804275200, 62672414540756209489045094400, 666547484168283183405932216320, 62672603435415524274853642240, 194561499094229382804275200, 846625863048869993911418880,
    157609699165479805193176481792, 157609708610212770932466909184, 846616418315904254620991488, 3356875324881955821574946816, 151724657720328756109997244416, 3374791983317963255515709440
  ]
def positiveScales : Array ℕ := #[
    11, 20, 24, 19, 11, 13,
    20, 23, 16, 18, 23, 15
  ]
def negativeArguments : Array ℕ := #[
    5, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    792281625142643375935439503360, 316912650057057350374175801344, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    2, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11330356716957942, 20661817232847065, 24072622406843593, 19661821581123409, 11330356716957942, 13451855028397752,
    20992271070183114, 23992271156636352, 16451838933985791, 18439177517965153, 23937370317221351, 15446857141489837
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2321928094887363, 0, 0
  ]

abbrev PositiveTerm := Fin 12
abbrev NegativeTerm := Fin 3
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
noncomputable def positiveFloor : ℝ := 177175763 / 500000000000
noncomputable def negativeCeiling : ℝ := 1383977 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 194561499094229382804275200, coefficient := 194561499094229382804275200 }, { argument := 62672414540756209489045094400, coefficient := 62672414540756209489045094400 }, { argument := 666547484168283183405932216320, coefficient := 666547484168283183405932216320 }, { argument := 62672603435415524274853642240, coefficient := 62672603435415524274853642240 }, { argument := 194561499094229382804275200, coefficient := 194561499094229382804275200 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 846625863048869993911418880, coefficient := 846625863048869993911418880 }, { argument := 157609699165479805193176481792, coefficient := 157609699165479805193176481792 }, { argument := 157609708610212770932466909184, coefficient := 157609708610212770932466909184 }, { argument := 846616418315904254620991488, coefficient := 846616418315904254620991488 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 3356875324881955821574946816, coefficient := 3356875324881955821574946816 }, { argument := 151724657720328756109997244416, coefficient := 151724657720328756109997244416 }, { argument := 3374791983317963255515709440, coefficient := 3374791983317963255515709440 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5
