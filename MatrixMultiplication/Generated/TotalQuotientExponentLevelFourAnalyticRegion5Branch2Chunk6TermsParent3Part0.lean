import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 6, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk6

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
def constantNumerator : ℤ := 132257352041778545705940418560
def positiveArguments : Array ℕ := #[
    7, 4194313, 4194295, 4549257, 32132645, 9100489,
    1271809, 24529933, 24529921, 1271779, 51985, 164479,
    3510773, 1317071, 12309
  ]
def positiveCoefficients : Array ℕ := #[
    1109194275199700726309615304704, 79228332519457720900771643392, 79227992509070954286316257280, 171866070230080908607384190976, 606968503015795563710570823680, 171903376925295578804572389376,
    12011896388423921219170992128, 463357333704952179302934249472, 463357107031361001559963992064, 12011613046434949040458170368, 490984443223957012867973120, 12427681867774662001656070144,
    132633253953309703486585176064, 12439383891919212982495608832, 465020872301139703483072512
  ]
def positiveScales : Array ℕ := #[
    2, 22, 21, 22, 24, 23,
    20, 24, 24, 20, 15, 17,
    21, 20, 13
  ]
def negativeArguments : Array ℕ := #[
    218041361305, 689876407927, 14725280833949, 5524208017223, 51627798717, 1930172598157,
    37196867476933, 37196850219337, 1930126666327, 1930172598157, 6807686208319, 482712086349,
    218041361305, 218040425575, 218040425575, 689873447305, 14725217640035, 5524184309945,
    51627577155, 6807686208319, 262740622861527, 262740490272495, 6807526473979, 37196867476933,
    262740622861527, 74409626591135, 689876407927, 689873447305, 482712086349, 74409626591135,
    74409592368767, 965401176663, 37196850219337, 262740490272495, 74409592368767, 14725280833949,
    14725217640035, 1930126666327, 6807526473979, 965401176663, 5524208017223, 5524184309945,
    51627798717, 51627577155, 1, 3, 3, 1
  ]
def negativeCoefficients : Array ℕ := #[
    122746374190569210679132160, 3106927133671733492860321792, 33158384638349311492438884352, 3109852645985326168671256576, 116255467531920085736226816, 1086590574227575914295721984,
    41879949627116295129181192192, 41879930196790566401540620288, 1086564716906016858674561024, 1086590574227575914295721984, 3832386633880089150806294528, 1086970986104295544483479552,
    122746374190569210679132160, 122745847421409295754854400, 122745847421409295754854400, 3106913800215597507967713280, 33158242338305540250853703680, 3109839299974280322576547840,
    116254968618649766005309440, 3832386633880089150806294528, 147909821401783127457266663424, 147909746760793738880420413440, 3832296711440826366792040448, 41879949627116295129181192192,
    147909821401783127457266663424, 41888895823576667065019269120, 3106927133671733492860321792, 3106913800215597507967713280, 1086970986104295544483479552, 41888895823576667065019269120,
    41888876558096195498020962304, 1086945094870631294762483712, 41879930196790566401540620288, 147909746760793738880420413440, 41888876558096195498020962304, 33158384638349311492438884352,
    33158242338305540250853703680, 1086564716906016858674561024, 3832296711440826366792040448, 1086945094870631294762483712, 3109852645985326168671256576, 3109839299974280322576547840,
    116255467531920085736226816, 116254968618649766005309440, 158456325028528675187087900672, 950737950171172051122527404032, 950737950171172051122527404032, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    37, 39, 43, 42, 35, 40,
    45, 45, 40, 40, 42, 38,
    37, 37, 37, 39, 43, 42,
    35, 42, 47, 47, 42, 45,
    47, 46, 39, 39, 38, 46,
    46, 39, 45, 47, 46, 43,
    43, 40, 42, 39, 42, 42,
    35, 35, 0, 1, 1, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2807354922011143, 22000003095684394, 21999996902849453, 22117199508054055, 24937536404889945, 23117512637593837,
    20278450592585474, 24548039957597403, 24548039251833358, 20278416561247672, 15665807780735268, 17327543872805543,
    21743357286589869, 20328901689092439, 13587425939613443
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    37665810876453329, 39327546968489939, 43743360382480692, 42328904784776835, 35587429035302064, 40811867000108905,
    45080246363853329, 45080245694510569, 40811832668250199, 40811867000108905, 42630301678015323, 38812371994632865,
    37665810876453329, 37665804685077893, 37665804685077893, 39327540777114508, 43743354191105235, 42328898593401404,
    35587422843926632, 42630301678015323, 47900632608569018, 47900631880529325, 42630267826477982, 45080246363853329,
    47900632608569018, 46080554512622668, 39327546968489939, 39327540777114508, 38812371994632865, 46080554512622668,
    46080553849100296, 39812337629778251, 45080245694510569, 47900631880529325, 46080553849100296, 43743360382480692,
    43743354191105235, 40811832668250199, 42630267826477982, 39812337629778251, 42328904784776835, 42328898593401404,
    35587429035302064, 35587422843926632, 0, 1584962500724866, 1584962500724866, 0
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
noncomputable def positiveFloor : ℝ := 84430541 / 125000000000
noncomputable def negativeCeiling : ℝ := 131157039 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 122746374190569210679132160, coefficient := (-122746374190569210679132160) }, { argument := 3106927133671733492860321792, coefficient := (-3106927133671733492860321792) }, { argument := 33158384638349311492438884352, coefficient := (-33158384638349311492438884352) }, { argument := 3109852645985326168671256576, coefficient := (-3109852645985326168671256576) }, { argument := 116255467531920085736226816, coefficient := (-116255467531920085736226816) }, { argument := 1086590574227575914295721984, coefficient := (-1086590574227575914295721984) }, { argument := 41879949627116295129181192192, coefficient := (-41879949627116295129181192192) }, { argument := 41879930196790566401540620288, coefficient := (-41879930196790566401540620288) }, { argument := 1086564716906016858674561024, coefficient := (-1086564716906016858674561024) }, { argument := 1086590574227575914295721984, coefficient := (-1086590574227575914295721984) }, { argument := 3832386633880089150806294528, coefficient := (-3832386633880089150806294528) }, { argument := 1086970986104295544483479552, coefficient := (-1086970986104295544483479552) }, { argument := 122746374190569210679132160, coefficient := (-122746374190569210679132160) }, { argument := 122745847421409295754854400, coefficient := (-122745847421409295754854400) }, { argument := 122745847421409295754854400, coefficient := (-122745847421409295754854400) }, { argument := 3106913800215597507967713280, coefficient := (-3106913800215597507967713280) }, { argument := 33158242338305540250853703680, coefficient := (-33158242338305540250853703680) }, { argument := 3109839299974280322576547840, coefficient := (-3109839299974280322576547840) }, { argument := 116254968618649766005309440, coefficient := (-116254968618649766005309440) }, { argument := 3832386633880089150806294528, coefficient := (-3832386633880089150806294528) }, { argument := 147909821401783127457266663424, coefficient := (-147909821401783127457266663424) }, { argument := 147909746760793738880420413440, coefficient := (-147909746760793738880420413440) }, { argument := 3832296711440826366792040448, coefficient := (-3832296711440826366792040448) }, { argument := 41879949627116295129181192192, coefficient := (-41879949627116295129181192192) }, { argument := 147909821401783127457266663424, coefficient := (-147909821401783127457266663424) }, { argument := 41888895823576667065019269120, coefficient := (-41888895823576667065019269120) }, { argument := 3106927133671733492860321792, coefficient := (-3106927133671733492860321792) }, { argument := 3106913800215597507967713280, coefficient := (-3106913800215597507967713280) }, { argument := 1086970986104295544483479552, coefficient := (-1086970986104295544483479552) }, { argument := 41888895823576667065019269120, coefficient := (-41888895823576667065019269120) }, { argument := 41888876558096195498020962304, coefficient := (-41888876558096195498020962304) }, { argument := 1086945094870631294762483712, coefficient := (-1086945094870631294762483712) }, { argument := 41879930196790566401540620288, coefficient := (-41879930196790566401540620288) }, { argument := 147909746760793738880420413440, coefficient := (-147909746760793738880420413440) }, { argument := 41888876558096195498020962304, coefficient := (-41888876558096195498020962304) }, { argument := 33158384638349311492438884352, coefficient := (-33158384638349311492438884352) }, { argument := 33158242338305540250853703680, coefficient := (-33158242338305540250853703680) }, { argument := 1086564716906016858674561024, coefficient := (-1086564716906016858674561024) }, { argument := 3832296711440826366792040448, coefficient := (-3832296711440826366792040448) }, { argument := 1086945094870631294762483712, coefficient := (-1086945094870631294762483712) }, { argument := 3109852645985326168671256576, coefficient := (-3109852645985326168671256576) }, { argument := 3109839299974280322576547840, coefficient := (-3109839299974280322576547840) }, { argument := 116255467531920085736226816, coefficient := (-116255467531920085736226816) }, { argument := 116254968618649766005309440, coefficient := (-116254968618649766005309440) }, { argument := 1109194275199700726309615304704, coefficient := 1109194275199700726309615304704 }, { argument := 79228332519457720900771643392, coefficient := 79228332519457720900771643392 }, { argument := 79227992509070954286316257280, coefficient := 79227992509070954286316257280 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 171866070230080908607384190976, coefficient := 171866070230080908607384190976 }, { argument := 606968503015795563710570823680, coefficient := 606968503015795563710570823680 }, { argument := 171903376925295578804572389376, coefficient := 171903376925295578804572389376 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 12011896388423921219170992128, coefficient := 12011896388423921219170992128 }, { argument := 463357333704952179302934249472, coefficient := 463357333704952179302934249472 }, { argument := 463357107031361001559963992064, coefficient := 463357107031361001559963992064 }, { argument := 12011613046434949040458170368, coefficient := 12011613046434949040458170368 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 490984443223957012867973120, coefficient := 490984443223957012867973120 }, { argument := 12427681867774662001656070144, coefficient := 12427681867774662001656070144 }, { argument := 132633253953309703486585176064, coefficient := 132633253953309703486585176064 }, { argument := 12439383891919212982495608832, coefficient := 12439383891919212982495608832 }, { argument := 465020872301139703483072512, coefficient := 465020872301139703483072512 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk6
