import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 5, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk5

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
def constantNumerator : ℤ := 17721334666310344621640680210432
def positiveArguments : Array ℕ := #[
    3, 237277, 8151335, 8151323, 237281, 34905
  ]
def positiveCoefficients : Array ℕ := #[
    475368975085586025561263702016, 2241017903911721614740291584, 76987182389284478935965368320, 76987069052488890064480239616, 2241055682843584571902001152, 1318673616676519729472471040
  ]
def positiveScales : Array ℕ := #[
    1, 17, 22, 22, 17, 15
  ]
def negativeArguments : Array ℕ := #[
    43636426685, 486689057611, 121676357431, 43633104807, 1130973921, 45352627287,
    492552655401, 45399889641, 586289115, 1499071263175, 16719553725905, 4180029042005,
    1498957144485, 45352627287, 1698536740813, 18374614221841, 1700914969833, 23725563249,
    43636426685, 1499071263175, 1499069056315, 43637162305, 1499069056315, 16719529112189,
    4180022888369, 1498954937793, 492552655401, 18374614221841, 24841026964365, 4600183484383,
    257801266929, 486689057611, 16719553725905, 16719529112189, 486697262183, 43637162305,
    486697262183, 121678408643, 43633840371, 45399889641, 1700914969833, 4600183484383,
    13306978375, 23749199001, 121676357431, 4180029042005, 4180022888369, 121678408643,
    586289115, 23725563249, 257801266929, 23749199001, 303543189, 43633104807,
    1498957144485, 1498954937793, 43633840371, 1
  ]
def negativeCoefficients : Array ℕ := #[
    12282562184896623002255360, 547963164625549365046411264, 547981597986050881959755776, 12281627159363937361723392, 1273363432295337195208704, 51062518837501547237081088,
    554564988831072981010612224, 51115731517467310354857984, 1320205719922688938475520, 421951048889796796402892800, 18824543982446686503666974720, 18825177235971569372081684480,
    421918927334186795831132160, 51062518837501547237081088, 1912382358250130886268813312, 20687976440639935981010550784, 1915060006082199311238561792, 53425218903675767202250752,
    12282562184896623002255360, 421951048889796796402892800, 421950427713929692724592640, 12282769243518990895022080, 421950427713929692724592640, 18824516269866135052863143936,
    18825149522458772798412161024, 421918306205607488240222208, 554564988831072981010612224, 20687976440639935981010550784, 223748079560429314836088750080, 20717384626103188705370963968,
    580516844838543086837563392, 547963164625549365046411264, 18824543982446686503666974720, 18824516269866135052863143936, 547972402152399848647688192, 12282769243518990895022080,
    547972402152399848647688192, 547990835823649739849596928, 12281834202223706558693376, 51115731517467310354857984, 1915060006082199311238561792, 20717384626103188705370963968,
    1917737691234471948320768000, 53478441885625677930037248, 547981597986050881959755776, 18825177235971569372081684480, 18825149522458772798412161024, 547990835823649739849596928,
    1320205719922688938475520, 53425218903675767202250752, 580516844838543086837563392, 53478441885625677930037248, 1367036992871252040351744, 12281627159363937361723392,
    421918927334186795831132160, 421918306205607488240222208, 12281834202223706558693376, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    35, 38, 36, 35, 30, 35,
    38, 35, 29, 40, 43, 41,
    40, 35, 40, 44, 40, 34,
    35, 40, 40, 35, 40, 43,
    41, 40, 38, 44, 44, 42,
    37, 38, 43, 43, 38, 35,
    38, 36, 35, 35, 40, 42,
    33, 34, 36, 41, 41, 36,
    29, 34, 37, 34, 28, 35,
    40, 40, 35, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 17856212736693376, 22958604927329878, 22958602803462681, 17856237057346070, 15091146091013867
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    35344813915454947, 38824209383208302, 36824257914337322, 35344704084295379, 30074918516755417, 35400467077667896,
    38841487006603604, 35401969739460845, 29127037031113353, 40447206106714287, 43926601580400854, 41926650111534753,
    40447096275554719, 35400467077667896, 40627429563951473, 44062779194174271, 40629448159928797, 34465723286357959,
    35344813915454947, 40447206106714287, 40447203982847063, 35344838236107696, 40447203982847063, 43926599456533373,
    41926647987667272, 40447094151687495, 38841487006603604, 44062779194174271, 44497790051449045, 42064828544759341,
    37907468402395387, 38824209383208302, 43926601580400854, 43926599456533373, 38824233703861555, 35344838236107696,
    38824233703861555, 36824282234990576, 35344728404948128, 35401969739460845, 40629448159928797, 42064828544759341,
    33631463963540215, 34467159804768981, 36824257914337322, 41926650111534753, 41926647987667272, 36824282234990576,
    29127037031113353, 34465723286357959, 37907468402395387, 34467159804768981, 28177326560993993, 35344704084295379,
    40447096275554719, 40447094151687495, 35344728404948128, 0
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
noncomputable def positiveFloor : ℝ := 103171 / 1953125000
noncomputable def negativeCeiling : ℝ := 249077487 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 12282562184896623002255360, coefficient := (-12282562184896623002255360) }, { argument := 547963164625549365046411264, coefficient := (-547963164625549365046411264) }, { argument := 547981597986050881959755776, coefficient := (-547981597986050881959755776) }, { argument := 12281627159363937361723392, coefficient := (-12281627159363937361723392) }, { argument := 1273363432295337195208704, coefficient := (-1273363432295337195208704) }, { argument := 51062518837501547237081088, coefficient := (-51062518837501547237081088) }, { argument := 554564988831072981010612224, coefficient := (-554564988831072981010612224) }, { argument := 51115731517467310354857984, coefficient := (-51115731517467310354857984) }, { argument := 1320205719922688938475520, coefficient := (-1320205719922688938475520) }, { argument := 421951048889796796402892800, coefficient := (-421951048889796796402892800) }, { argument := 18824543982446686503666974720, coefficient := (-18824543982446686503666974720) }, { argument := 18825177235971569372081684480, coefficient := (-18825177235971569372081684480) }, { argument := 421918927334186795831132160, coefficient := (-421918927334186795831132160) }, { argument := 51062518837501547237081088, coefficient := (-51062518837501547237081088) }, { argument := 1912382358250130886268813312, coefficient := (-1912382358250130886268813312) }, { argument := 20687976440639935981010550784, coefficient := (-20687976440639935981010550784) }, { argument := 1915060006082199311238561792, coefficient := (-1915060006082199311238561792) }, { argument := 53425218903675767202250752, coefficient := (-53425218903675767202250752) }, { argument := 12282562184896623002255360, coefficient := (-12282562184896623002255360) }, { argument := 421951048889796796402892800, coefficient := (-421951048889796796402892800) }, { argument := 421950427713929692724592640, coefficient := (-421950427713929692724592640) }, { argument := 12282769243518990895022080, coefficient := (-12282769243518990895022080) }, { argument := 421950427713929692724592640, coefficient := (-421950427713929692724592640) }, { argument := 18824516269866135052863143936, coefficient := (-18824516269866135052863143936) }, { argument := 18825149522458772798412161024, coefficient := (-18825149522458772798412161024) }, { argument := 421918306205607488240222208, coefficient := (-421918306205607488240222208) }, { argument := 554564988831072981010612224, coefficient := (-554564988831072981010612224) }, { argument := 20687976440639935981010550784, coefficient := (-20687976440639935981010550784) }, { argument := 223748079560429314836088750080, coefficient := (-223748079560429314836088750080) }, { argument := 20717384626103188705370963968, coefficient := (-20717384626103188705370963968) }, { argument := 580516844838543086837563392, coefficient := (-580516844838543086837563392) }, { argument := 547963164625549365046411264, coefficient := (-547963164625549365046411264) }, { argument := 18824543982446686503666974720, coefficient := (-18824543982446686503666974720) }, { argument := 18824516269866135052863143936, coefficient := (-18824516269866135052863143936) }, { argument := 547972402152399848647688192, coefficient := (-547972402152399848647688192) }, { argument := 12282769243518990895022080, coefficient := (-12282769243518990895022080) }, { argument := 547972402152399848647688192, coefficient := (-547972402152399848647688192) }, { argument := 547990835823649739849596928, coefficient := (-547990835823649739849596928) }, { argument := 12281834202223706558693376, coefficient := (-12281834202223706558693376) }, { argument := 51115731517467310354857984, coefficient := (-51115731517467310354857984) }, { argument := 1915060006082199311238561792, coefficient := (-1915060006082199311238561792) }, { argument := 20717384626103188705370963968, coefficient := (-20717384626103188705370963968) }, { argument := 1917737691234471948320768000, coefficient := (-1917737691234471948320768000) }, { argument := 53478441885625677930037248, coefficient := (-53478441885625677930037248) }, { argument := 547981597986050881959755776, coefficient := (-547981597986050881959755776) }, { argument := 18825177235971569372081684480, coefficient := (-18825177235971569372081684480) }, { argument := 18825149522458772798412161024, coefficient := (-18825149522458772798412161024) }, { argument := 547990835823649739849596928, coefficient := (-547990835823649739849596928) }, { argument := 1320205719922688938475520, coefficient := (-1320205719922688938475520) }, { argument := 53425218903675767202250752, coefficient := (-53425218903675767202250752) }, { argument := 580516844838543086837563392, coefficient := (-580516844838543086837563392) }, { argument := 53478441885625677930037248, coefficient := (-53478441885625677930037248) }, { argument := 1367036992871252040351744, coefficient := (-1367036992871252040351744) }, { argument := 12281627159363937361723392, coefficient := (-12281627159363937361723392) }, { argument := 421918927334186795831132160, coefficient := (-421918927334186795831132160) }, { argument := 421918306205607488240222208, coefficient := (-421918306205607488240222208) }, { argument := 12281834202223706558693376, coefficient := (-12281834202223706558693376) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 2241017903911721614740291584, coefficient := 2241017903911721614740291584 }, { argument := 76987182389284478935965368320, coefficient := 76987182389284478935965368320 }, { argument := 76987069052488890064480239616, coefficient := 76987069052488890064480239616 }, { argument := 2241055682843584571902001152, coefficient := 2241055682843584571902001152 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 1318673616676519729472471040, coefficient := 1318673616676519729472471040 }] }

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

namespace Parent1

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-18647328932363215299795763593216)
def positiveArguments : Array ℕ := #[
    1303367, 14097197, 1305213, 18267, 183905, 2051143,
    512803, 183891
  ]
def positiveCoefficients : Array ℕ := #[
    49239813085426886985914515456, 532577044921684111180636880896, 49309552993645905906430377984, 1380215496681276945897357312, 1736933616064284206049525760, 77489991638181541540448436224,
    77492598384480085584606396416, 1736801389802763855983542272
  ]
def positiveScales : Array ℕ := #[
    20, 23, 20, 14, 17, 20,
    18, 17
  ]
def negativeArguments : Array ℕ := #[
    1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    633825300114114700748351602688, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    20313811942201425, 23748904998722517, 20315853831267546, 14156952098325733, 17488601178640939, 20967996644475525,
    18968045175602842, 17488491347481371
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
noncomputable def positiveFloor : ℝ := 214562063 / 1000000000000
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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 49239813085426886985914515456, coefficient := 49239813085426886985914515456 }, { argument := 532577044921684111180636880896, coefficient := 532577044921684111180636880896 }, { argument := 49309552993645905906430377984, coefficient := 49309552993645905906430377984 }, { argument := 1380215496681276945897357312, coefficient := 1380215496681276945897357312 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 1736933616064284206049525760, coefficient := 1736933616064284206049525760 }, { argument := 77489991638181541540448436224, coefficient := 77489991638181541540448436224 }, { argument := 77492598384480085584606396416, coefficient := 77492598384480085584606396416 }, { argument := 1736801389802763855983542272, coefficient := 1736801389802763855983542272 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk5
