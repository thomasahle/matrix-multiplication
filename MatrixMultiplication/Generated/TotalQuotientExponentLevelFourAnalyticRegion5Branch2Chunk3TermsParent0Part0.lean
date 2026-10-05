import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 3, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk3

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 11154276036499296430634896982016
def positiveArguments : Array ℕ := #[
    1, 114341, 8159923, 8159939, 3573, 106365
  ]
def positiveCoefficients : Array ℕ := #[
    316912650057057350374175801344, 2159840424071192413516857344, 77068293755994247962155810816, 77068444871721699790802649088, 2159745976741535020612583424, 1004589021900859626309550080
  ]
def positiveScales : Array ℕ := #[
    0, 16, 22, 22, 11, 16
  ]
def negativeArguments : Array ℕ := #[
    9187871055, 7349953821, 940789401107, 18364422351, 706736075, 17097331525,
    1499884530185, 136730986215, 341282665, 655690612665, 524528010363, 67139250769621,
    1310573392953, 17097331525, 25795735007, 4531802274251, 103140521043, 4131844333,
    9187871055, 655690612665, 655691898345, 287108415, 655691898345, 524529038859,
    67139382416453, 1310575962729, 1499884530185, 4531802274251, 49720216719005, 36240887778627,
    362275078493, 7349953821, 524528010363, 524529038859, 229676013, 287108415,
    229676013, 29398383171, 573863103, 136730986215, 103140521043, 36240887778627,
    1649566891021, 33044097623, 940789401107, 67139250769621, 67139382416453, 29398383171,
    341282665, 4131844333, 362275078493, 33044097623, 20592957, 18364422351,
    1310573392953, 1310575962729, 573863103, 1
  ]
def negativeCoefficients : Array ℕ := #[
    10344623164906541489848320, 529619988631135252125843456, 529617349532449662130192384, 10338250707104751012544512, 1591428162009643456921600, 38499767942509917057843200,
    422179963202496091243151360, 38486351160492151579607040, 1537000482922009817251840, 369120999858553278148116480, 18898113216129555714627600384, 18898019046749963899031781376,
    368893615259051089270407168, 38499767942509917057843200, 929389300522186072209227776, 10204711516816784959888949248, 929007224272107202890694656, 37216345196903391177998336,
    10344623164906541489848320, 369120999858553278148116480, 369121723632049392860528640, 10344170806471469794590720, 369121723632049392860528640, 18898150271603174530992832512,
    18898056102038935130674823168, 368894338586690840873140224, 422179963202496091243151360, 10204711516816784959888949248, 111959974744245611612329738240, 10200903043462532483159949312,
    407885477126672997398085632, 529619988631135252125843456, 18898113216129555714627600384, 18898150271603174530992832512, 529596828960123491897573376, 10344170806471469794590720,
    529596828960123491897573376, 529594189976842642353291264, 10337798627329906260836352, 38486351160492151579607040, 929007224272107202890694656, 10200903043462532483159949312,
    928623604465610398002839552, 37204346435434273153482752, 529617349532449662130192384, 18898019046749963899031781376, 18898056102038935130674823168, 529594189976842642353291264,
    1537000482922009817251840, 37216345196903391177998336, 407885477126672997398085632, 37204346435434273153482752, 1483878935546506355146752, 10338250707104751012544512,
    368893615259051089270407168, 368894338586690840873140224, 10337798627329906260836352, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    33, 32, 39, 34, 29, 33,
    40, 36, 28, 39, 38, 45,
    40, 33, 34, 42, 36, 31,
    33, 39, 39, 28, 39, 38,
    45, 40, 40, 42, 45, 45,
    38, 32, 38, 38, 27, 28,
    27, 34, 29, 36, 36, 45,
    40, 34, 39, 45, 45, 34,
    28, 31, 38, 34, 24, 34,
    40, 40, 29, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 16802983287311664, 22960124107027785, 22960126935865476, 11802920198542795, 16698663976462904
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    33097083463682352, 32775088040045327, 39775080851071751, 34096194465991150, 29396596311649367, 33993052143352678,
    40447988576608379, 36992549290841918, 28346391895616910, 39254224284118432, 38932228867793336, 45932221678818865,
    40253335286427230, 33993052143352678, 34586413503173725, 42043222055371550, 36585820282607821, 31944138765198110,
    33097083463682352, 39254224284118432, 39254227112956158, 28097020374913429, 39254227112956158, 38932231696631437,
    45932224507656966, 40253338115264956, 40447988576608379, 42043222055371550, 45498897818316402, 45042683530479873,
    38398294607567085, 32775088040045327, 38932228867793336, 38932231696631437, 27775024951275890, 28097020374913429,
    27775024951275890, 34775017762302315, 29096131377222226, 36992549290841918, 36585820282607821, 45042683530479873,
    40585224419972700, 34943673557036068, 39775080851071751, 45932221678818865, 45932224507656966, 34775017762302315,
    28346391895616910, 31944138765198110, 38398294607567085, 34943673557036068, 24295647669652045, 34096194465991150,
    40253335286427230, 40253338115264956, 29096131377222226, 0
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
noncomputable def positiveFloor : ℝ := 43544761 / 1000000000000
noncomputable def negativeCeiling : ℝ := 1294277 / 7812500000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 10344623164906541489848320, coefficient := (-10344623164906541489848320) }, { argument := 529619988631135252125843456, coefficient := (-529619988631135252125843456) }, { argument := 529617349532449662130192384, coefficient := (-529617349532449662130192384) }, { argument := 10338250707104751012544512, coefficient := (-10338250707104751012544512) }, { argument := 1591428162009643456921600, coefficient := (-1591428162009643456921600) }, { argument := 38499767942509917057843200, coefficient := (-38499767942509917057843200) }, { argument := 422179963202496091243151360, coefficient := (-422179963202496091243151360) }, { argument := 38486351160492151579607040, coefficient := (-38486351160492151579607040) }, { argument := 1537000482922009817251840, coefficient := (-1537000482922009817251840) }, { argument := 369120999858553278148116480, coefficient := (-369120999858553278148116480) }, { argument := 18898113216129555714627600384, coefficient := (-18898113216129555714627600384) }, { argument := 18898019046749963899031781376, coefficient := (-18898019046749963899031781376) }, { argument := 368893615259051089270407168, coefficient := (-368893615259051089270407168) }, { argument := 38499767942509917057843200, coefficient := (-38499767942509917057843200) }, { argument := 929389300522186072209227776, coefficient := (-929389300522186072209227776) }, { argument := 10204711516816784959888949248, coefficient := (-10204711516816784959888949248) }, { argument := 929007224272107202890694656, coefficient := (-929007224272107202890694656) }, { argument := 37216345196903391177998336, coefficient := (-37216345196903391177998336) }, { argument := 10344623164906541489848320, coefficient := (-10344623164906541489848320) }, { argument := 369120999858553278148116480, coefficient := (-369120999858553278148116480) }, { argument := 369121723632049392860528640, coefficient := (-369121723632049392860528640) }, { argument := 10344170806471469794590720, coefficient := (-10344170806471469794590720) }, { argument := 369121723632049392860528640, coefficient := (-369121723632049392860528640) }, { argument := 18898150271603174530992832512, coefficient := (-18898150271603174530992832512) }, { argument := 18898056102038935130674823168, coefficient := (-18898056102038935130674823168) }, { argument := 368894338586690840873140224, coefficient := (-368894338586690840873140224) }, { argument := 422179963202496091243151360, coefficient := (-422179963202496091243151360) }, { argument := 10204711516816784959888949248, coefficient := (-10204711516816784959888949248) }, { argument := 111959974744245611612329738240, coefficient := (-111959974744245611612329738240) }, { argument := 10200903043462532483159949312, coefficient := (-10200903043462532483159949312) }, { argument := 407885477126672997398085632, coefficient := (-407885477126672997398085632) }, { argument := 529619988631135252125843456, coefficient := (-529619988631135252125843456) }, { argument := 18898113216129555714627600384, coefficient := (-18898113216129555714627600384) }, { argument := 18898150271603174530992832512, coefficient := (-18898150271603174530992832512) }, { argument := 529596828960123491897573376, coefficient := (-529596828960123491897573376) }, { argument := 10344170806471469794590720, coefficient := (-10344170806471469794590720) }, { argument := 529596828960123491897573376, coefficient := (-529596828960123491897573376) }, { argument := 529594189976842642353291264, coefficient := (-529594189976842642353291264) }, { argument := 10337798627329906260836352, coefficient := (-10337798627329906260836352) }, { argument := 38486351160492151579607040, coefficient := (-38486351160492151579607040) }, { argument := 929007224272107202890694656, coefficient := (-929007224272107202890694656) }, { argument := 10200903043462532483159949312, coefficient := (-10200903043462532483159949312) }, { argument := 928623604465610398002839552, coefficient := (-928623604465610398002839552) }, { argument := 37204346435434273153482752, coefficient := (-37204346435434273153482752) }, { argument := 529617349532449662130192384, coefficient := (-529617349532449662130192384) }, { argument := 18898019046749963899031781376, coefficient := (-18898019046749963899031781376) }, { argument := 18898056102038935130674823168, coefficient := (-18898056102038935130674823168) }, { argument := 529594189976842642353291264, coefficient := (-529594189976842642353291264) }, { argument := 1537000482922009817251840, coefficient := (-1537000482922009817251840) }, { argument := 37216345196903391177998336, coefficient := (-37216345196903391177998336) }, { argument := 407885477126672997398085632, coefficient := (-407885477126672997398085632) }, { argument := 37204346435434273153482752, coefficient := (-37204346435434273153482752) }, { argument := 1483878935546506355146752, coefficient := (-1483878935546506355146752) }, { argument := 10338250707104751012544512, coefficient := (-10338250707104751012544512) }, { argument := 368893615259051089270407168, coefficient := (-368893615259051089270407168) }, { argument := 368894338586690840873140224, coefficient := (-368894338586690840873140224) }, { argument := 10337798627329906260836352, coefficient := (-10337798627329906260836352) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 2159840424071192413516857344, coefficient := 2159840424071192413516857344 }, { argument := 77068293755994247962155810816, coefficient := 77068293755994247962155810816 }, { argument := 77068444871721699790802649088, coefficient := 77068444871721699790802649088 }, { argument := 2159745976741535020612583424, coefficient := 2159745976741535020612583424 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 1004589021900859626309550080, coefficient := 1004589021900859626309550080 }] }

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


end Parent0

namespace Parent0

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-11033177519592114774924725321728)
def positiveArguments : Array ℕ := #[
    10041, 28205277, 1284761, 25693, 80355, 64281,
    8227927, 160611
  ]
def positiveCoefficients : Array ℕ := #[
    24277648309500983086449426432, 266391309489708196288039747584, 24268449139592353017573146624, 970654096354958355803930624, 1517863034923961364586168320, 77710960610647977979287699456,
    77710573376596382668380176384, 1516928006360353174833856512
  ]
def positiveScales : Array ℕ := #[
    13, 24, 20, 14, 16, 15,
    22, 17
  ]
def negativeArguments : Array ℕ := #[
    1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    316912650057057350374175801344, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13293615336407685, 24749461769712197, 20293068573736175, 14649087733486068, 16294100176328157, 15972104751376100,
    22972097562402693, 17293211178636955
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0
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
noncomputable def positiveFloor : ℝ := 12638707 / 100000000000
noncomputable def negativeCeiling : ℝ := 0 / 1

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 24277648309500983086449426432, coefficient := 24277648309500983086449426432 }, { argument := 266391309489708196288039747584, coefficient := 266391309489708196288039747584 }, { argument := 24268449139592353017573146624, coefficient := 24268449139592353017573146624 }, { argument := 970654096354958355803930624, coefficient := 970654096354958355803930624 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 1517863034923961364586168320, coefficient := 1517863034923961364586168320 }, { argument := 77710960610647977979287699456, coefficient := 77710960610647977979287699456 }, { argument := 77710573376596382668380176384, coefficient := 77710573376596382668380176384 }, { argument := 1516928006360353174833856512, coefficient := 1516928006360353174833856512 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk3
