import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 8, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk8

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
def constantNumerator : ℤ := 11856262319610748827270836649984
def positiveArguments : Array ℕ := #[
    1, 203781, 2046205, 8186411, 50551, 18885
  ]
def positiveCoefficients : Array ℕ := #[
    316912650057057350374175801344, 1924657128491318342584369152, 77303439272642259075926589440, 77318465842790750286996570112, 1909762784604347481580371968, 713455128231945998885191680
  ]
def positiveScales : Array ℕ := #[
    0, 17, 20, 22, 15, 14
  ]
def negativeArguments : Array ℕ := #[
    8155111839, 1676810532033, 838600182543, 32246509221, 356643225, 24242051295,
    266926765395, 24242428995, 713192025, 81887077895, 16837183519065, 8420548954615,
    323793525405, 24242051295, 1647800966889, 18143769137109, 1647826640229, 48477684255,
    8155111839, 81887077895, 327611981809, 2023000469, 327611981809, 67361825608623,
    33688743106433, 1295425863051, 266926765395, 18143769137109, 199779199742929, 18144051823649,
    533782859155, 1676810532033, 16837183519065, 67361825608623, 415958549643, 2023000469,
    415958549643, 208027626853, 7999240791, 24242428995, 1647826640229, 18144051823649,
    1647852313969, 48478439555, 838600182543, 8420548954615, 33688743106433, 208027626853,
    713192025, 48477684255, 533782859155, 48478439555, 1426195225, 32246509221,
    323793525405, 1295425863051, 7999240791, 1
  ]
def negativeCoefficients : Array ℕ := #[
    9181839659821280092225536, 471980205452171371660443648, 472089933701685590586556416, 9076585431980928952958976, 803089147607105981644800, 27294123294714612500398080,
    300532820292033451634196480, 27294548547109426959482880, 802982834508402366873600, 368786613494380779976785920, 18956983355607447633458626560, 18961390567129566817047019520,
    364559100089734307480862720, 27294123294714612500398080, 927629477557755427178938368, 10214033990622549768570667008, 927643930363312596685160448, 27290510093325320123842560,
    9181839659821280092225536, 368786613494380779976785920, 368858299799280528513826816, 9110784158358738644762624, 368858299799280528513826816, 18960668294374429857769586688,
    18965076362589003083306500096, 364629964632661673908371456, 300532820292033451634196480, 10214033990622549768570667008, 112465691189828866834429902848, 10214193128997075600422207488,
    300493035698401993671311360, 471980205452171371660443648, 18956983355607447633458626560, 18960668294374429857769586688, 468327692293446690492383232, 9110784158358738644762624,
    468327692293446690492383232, 468436571388969693734764544, 9006344461398617918275584, 27294548547109426959482880, 927643930363312596685160448, 10214193128997075600422207488,
    927658383394049747559907328, 27290935289425139240796160, 472089933701685590586556416, 18961390567129566817047019520, 18965076362589003083306500096, 468436571388969693734764544,
    802982834508402366873600, 27290510093325320123842560, 300493035698401993671311360, 27290935289425139240796160, 802876535483447587635200, 9076585431980928952958976,
    364559100089734307480862720, 364629964632661673908371456, 9006344461398617918275584, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    32, 40, 39, 34, 28, 34,
    37, 34, 29, 36, 43, 42,
    38, 34, 40, 44, 40, 35,
    32, 36, 38, 30, 38, 45,
    44, 40, 37, 44, 47, 44,
    38, 40, 43, 45, 38, 30,
    38, 37, 32, 34, 40, 44,
    40, 35, 39, 42, 44, 37,
    29, 35, 38, 35, 30, 34,
    38, 40, 32, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 17636660019150534, 20964519257901833, 22964799667821649, 15625452011355991, 14204953163327534
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    32925057522941168, 40608856822227567, 39609192187992458, 34908423946977319, 28409906326655080, 34496792729694325,
    37957653030884741, 34496815207234095, 29409715329760529, 36252916755713455, 43936716070105822, 42937051435918604,
    38236283181472225, 34496792729694325, 40583679132736669, 44044539422068540, 40583701610276441, 35496601732799772,
    32925057522941168, 36252916755713455, 38253197165637093, 30913849513934963, 38253197165637093, 45936996480069541,
    44937331845882538, 40236563591395863, 37957653030884741, 44044539422068540, 47505399711404312, 44044561899608310,
    38957462033952351, 40608856822227567, 43936716070105822, 45936996480069541, 38597648814430871, 30913849513934963,
    38597648814430871, 37597984180195745, 32897215938261431, 34496815207234095, 40583701610276441, 44044561899608310,
    40583724087816212, 35496624210339541, 39609192187992458, 42937051435918604, 44937331845882538, 37597984180195745,
    29409715329760529, 35496601732799772, 38957462033952351, 35496624210339541, 30409524332865977, 34908423946977319,
    38236283181472225, 40236563591395863, 32897215938261431, 0
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
noncomputable def positiveFloor : ℝ := 41770441 / 1000000000000
noncomputable def negativeCeiling : ℝ := 172720379 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 9181839659821280092225536, coefficient := (-9181839659821280092225536) }, { argument := 471980205452171371660443648, coefficient := (-471980205452171371660443648) }, { argument := 472089933701685590586556416, coefficient := (-472089933701685590586556416) }, { argument := 9076585431980928952958976, coefficient := (-9076585431980928952958976) }, { argument := 803089147607105981644800, coefficient := (-803089147607105981644800) }, { argument := 27294123294714612500398080, coefficient := (-27294123294714612500398080) }, { argument := 300532820292033451634196480, coefficient := (-300532820292033451634196480) }, { argument := 27294548547109426959482880, coefficient := (-27294548547109426959482880) }, { argument := 802982834508402366873600, coefficient := (-802982834508402366873600) }, { argument := 368786613494380779976785920, coefficient := (-368786613494380779976785920) }, { argument := 18956983355607447633458626560, coefficient := (-18956983355607447633458626560) }, { argument := 18961390567129566817047019520, coefficient := (-18961390567129566817047019520) }, { argument := 364559100089734307480862720, coefficient := (-364559100089734307480862720) }, { argument := 27294123294714612500398080, coefficient := (-27294123294714612500398080) }, { argument := 927629477557755427178938368, coefficient := (-927629477557755427178938368) }, { argument := 10214033990622549768570667008, coefficient := (-10214033990622549768570667008) }, { argument := 927643930363312596685160448, coefficient := (-927643930363312596685160448) }, { argument := 27290510093325320123842560, coefficient := (-27290510093325320123842560) }, { argument := 9181839659821280092225536, coefficient := (-9181839659821280092225536) }, { argument := 368786613494380779976785920, coefficient := (-368786613494380779976785920) }, { argument := 368858299799280528513826816, coefficient := (-368858299799280528513826816) }, { argument := 9110784158358738644762624, coefficient := (-9110784158358738644762624) }, { argument := 368858299799280528513826816, coefficient := (-368858299799280528513826816) }, { argument := 18960668294374429857769586688, coefficient := (-18960668294374429857769586688) }, { argument := 18965076362589003083306500096, coefficient := (-18965076362589003083306500096) }, { argument := 364629964632661673908371456, coefficient := (-364629964632661673908371456) }, { argument := 300532820292033451634196480, coefficient := (-300532820292033451634196480) }, { argument := 10214033990622549768570667008, coefficient := (-10214033990622549768570667008) }, { argument := 112465691189828866834429902848, coefficient := (-112465691189828866834429902848) }, { argument := 10214193128997075600422207488, coefficient := (-10214193128997075600422207488) }, { argument := 300493035698401993671311360, coefficient := (-300493035698401993671311360) }, { argument := 471980205452171371660443648, coefficient := (-471980205452171371660443648) }, { argument := 18956983355607447633458626560, coefficient := (-18956983355607447633458626560) }, { argument := 18960668294374429857769586688, coefficient := (-18960668294374429857769586688) }, { argument := 468327692293446690492383232, coefficient := (-468327692293446690492383232) }, { argument := 9110784158358738644762624, coefficient := (-9110784158358738644762624) }, { argument := 468327692293446690492383232, coefficient := (-468327692293446690492383232) }, { argument := 468436571388969693734764544, coefficient := (-468436571388969693734764544) }, { argument := 9006344461398617918275584, coefficient := (-9006344461398617918275584) }, { argument := 27294548547109426959482880, coefficient := (-27294548547109426959482880) }, { argument := 927643930363312596685160448, coefficient := (-927643930363312596685160448) }, { argument := 10214193128997075600422207488, coefficient := (-10214193128997075600422207488) }, { argument := 927658383394049747559907328, coefficient := (-927658383394049747559907328) }, { argument := 27290935289425139240796160, coefficient := (-27290935289425139240796160) }, { argument := 472089933701685590586556416, coefficient := (-472089933701685590586556416) }, { argument := 18961390567129566817047019520, coefficient := (-18961390567129566817047019520) }, { argument := 18965076362589003083306500096, coefficient := (-18965076362589003083306500096) }, { argument := 468436571388969693734764544, coefficient := (-468436571388969693734764544) }, { argument := 802982834508402366873600, coefficient := (-802982834508402366873600) }, { argument := 27290510093325320123842560, coefficient := (-27290510093325320123842560) }, { argument := 300493035698401993671311360, coefficient := (-300493035698401993671311360) }, { argument := 27290935289425139240796160, coefficient := (-27290935289425139240796160) }, { argument := 802876535483447587635200, coefficient := (-802876535483447587635200) }, { argument := 9076585431980928952958976, coefficient := (-9076585431980928952958976) }, { argument := 364559100089734307480862720, coefficient := (-364559100089734307480862720) }, { argument := 364629964632661673908371456, coefficient := (-364629964632661673908371456) }, { argument := 9006344461398617918275584, coefficient := (-9006344461398617918275584) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 1924657128491318342584369152, coefficient := 1924657128491318342584369152 }, { argument := 77303439272642259075926589440, coefficient := 77303439272642259075926589440 }, { argument := 77318465842790750286996570112, coefficient := 77318465842790750286996570112 }, { argument := 1909762784604347481580371968, coefficient := 1909762784604347481580371968 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 713455128231945998885191680, coefficient := 713455128231945998885191680 }] }

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
def constantNumerator : ℤ := (-11380893344525162801709572947968)
def positiveArguments : Array ℕ := #[
    1283667, 14134327, 1283687, 37765, 40019, 8228493,
    4115203, 158241
  ]
def positiveCoefficients : Array ℕ := #[
    24247784063863315450118012928, 266989888330877855297456570368, 24248161853181945021735108608, 713360680902288605980917760, 1511875074223682654455201792, 77715919095454991106762080256,
    77733986869618450369349681152, 1494543989231551056520937472
  ]
def positiveScales : Array ℕ := #[
    20, 23, 20, 15, 15, 22,
    21, 17
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
    20291839566366545, 23752699855687199, 20291862043906315, 15204762166432983, 15288397496991357, 22972196802137821,
    21972532167897502, 17271763922750127
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
noncomputable def positiveFloor : ℝ := 8184371 / 62500000000
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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 24247784063863315450118012928, coefficient := 24247784063863315450118012928 }, { argument := 266989888330877855297456570368, coefficient := 266989888330877855297456570368 }, { argument := 24248161853181945021735108608, coefficient := 24248161853181945021735108608 }, { argument := 713360680902288605980917760, coefficient := 713360680902288605980917760 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 1511875074223682654455201792, coefficient := 1511875074223682654455201792 }, { argument := 77715919095454991106762080256, coefficient := 77715919095454991106762080256 }, { argument := 77733986869618450369349681152, coefficient := 77733986869618450369349681152 }, { argument := 1494543989231551056520937472, coefficient := 1494543989231551056520937472 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk8
