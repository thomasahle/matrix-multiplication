import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 4, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk4

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
def constantNumerator : ℤ := 30704367110650835733531305443328
def positiveArguments : Array ℕ := #[
    5, 406927, 8185153, 16370293, 203453, 103713
  ]
def positiveCoefficients : Array ℕ := #[
    792281625142643375935439503360, 3843316851549392235747344384, 154613168737439700519277821952, 154613045955911145908502265856, 3843118512157111710648369152, 1959083180151438056192212992
  ]
def positiveScales : Array ℕ := #[
    2, 18, 22, 23, 17, 16
  ]
def negativeArguments : Array ℕ := #[
    4527977365, 3341259398457, 3340551046145, 36422046395, 3584459871, 122415656025,
    1487851444635, 244834366545, 7493318409, 2905804766995, 134423806635731, 67197237673575,
    731018249555, 122415656025, 4178442175731, 50794026242817, 8356986399741, 256168053609,
    4527977365, 2905804766995, 1452901256755, 72443964215, 1452901256755, 134423699837533,
    134394368577435, 1462035357905, 1487851444635, 50794026242817, 617428423278219, 101589301630587,
    3112485294903, 3341259398457, 134423806635731, 134423699837533, 3341086908823, 72443964215,
    3341086908823, 1670189299659, 18210095335, 244834366545, 8356986399741, 101589301630587,
    2089272112047, 256171375227, 3340551046145, 67197237673575, 134394368577435, 1670189299659,
    7493318409, 256168053609, 3112485294903, 256171375227, 1954434039, 36422046395,
    731018249555, 1462035357905, 18210095335, 1
  ]
def negativeCoefficients : Array ℕ := #[
    20392197173756040356823040, 940480911364944551101857792, 940281527914421411769221120, 20503789321574114645770240, 2017871517420012020170752, 68913887857313101696204800,
    837585901455105019997061120, 68914747621222089511403520, 2109181624658804871266304, 817911329115630809613598720, 37836937842150108695978049536, 37828681818379878190704230400,
    823053379074232563343032320, 68913887857313101696204800, 2352253828201412020584579072, 28594494707474729522014715904, 2352282552238366908110340096, 72104896923607352689557504,
    20392197173756040356823040, 817911329115630809613598720, 817910694815992916800962560, 20391163140244721673175040, 817910694815992916800962560, 37836907781129813905949851648,
    37828651765376835162325647360, 823052736632930969174671360, 837585901455105019997061120, 28594494707474729522014715904, 347581302125467495841900003328, 28594846310521283430498435072,
    876086725895081197062586368, 940480911364944551101857792, 37836937842150108695978049536, 37836907781129813905949851648, 940432359849231571524517888, 20391163140244721673175040,
    940432359849231571524517888, 940232988447807760244932608, 20502744641271801881559040, 68914747621222089511403520, 2352282552238366908110340096, 28594846310521283430498435072,
    2352311276322609591723491328, 72105831875956544385318912, 940281527914421411769221120, 37828681818379878190704230400, 37828651765376835162325647360, 940232988447807760244932608,
    2109181624658804871266304, 72104896923607352689557504, 876086725895081197062586368, 72105831875956544385318912, 2200497102440153361678336, 20503789321574114645770240,
    823053379074232563343032320, 823052736632930969174671360, 20502744641271801881559040, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    32, 41, 41, 35, 31, 36,
    40, 37, 32, 41, 46, 45,
    39, 36, 41, 45, 42, 37,
    32, 41, 40, 36, 40, 46,
    46, 40, 40, 45, 49, 46,
    41, 41, 46, 46, 41, 36,
    41, 40, 34, 37, 42, 46,
    40, 37, 41, 45, 46, 40,
    32, 37, 41, 37, 30, 35,
    39, 40, 34, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 18634410482234617, 22964577952860236, 23964576807185700, 17634336028149161, 16662237215838307
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    32076219600255909, 41603529129211446, 41603223243140537, 35084092932170736, 31739108595088322, 36832997124487027,
    40436367625586605, 37833015123318021, 32802957611005534, 41402074914175905, 46933782000292478, 45933467169692576,
    39411116466647128, 36832997124487027, 41926102316525725, 45529724068789132, 42926119933577567, 37898299618237410,
    32076219600255909, 41402074914175905, 40402073795348882, 36076146443213050, 40402073795348882, 46933780854086931,
    46933466023542632, 40411115340538828, 40436367625586605, 45529724068789132, 49133265227279352, 46529741808317604,
    41501204159758463, 41603529129211446, 46933782000292478, 46933780854086931, 41603454649402040, 36076146443213050,
    41603454649402040, 40603148766025695, 34084019424124767, 37833015123318021, 42926119933577567, 46529741808317604,
    40926137550443289, 37898318324906901, 41603223243140537, 45933467169692576, 46933466023542632, 40603148766025695,
    32802957611005534, 37898299618237410, 41501204159758463, 37898318324906901, 30864103751587234, 35084092932170736,
    39411116466647128, 40411115340538828, 34084019424124767, 0
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
noncomputable def positiveFloor : ℝ := 27888413 / 250000000000
noncomputable def negativeCeiling : ℝ := 452746659 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 20392197173756040356823040, coefficient := (-20392197173756040356823040) }, { argument := 940480911364944551101857792, coefficient := (-940480911364944551101857792) }, { argument := 940281527914421411769221120, coefficient := (-940281527914421411769221120) }, { argument := 20503789321574114645770240, coefficient := (-20503789321574114645770240) }, { argument := 2017871517420012020170752, coefficient := (-2017871517420012020170752) }, { argument := 68913887857313101696204800, coefficient := (-68913887857313101696204800) }, { argument := 837585901455105019997061120, coefficient := (-837585901455105019997061120) }, { argument := 68914747621222089511403520, coefficient := (-68914747621222089511403520) }, { argument := 2109181624658804871266304, coefficient := (-2109181624658804871266304) }, { argument := 817911329115630809613598720, coefficient := (-817911329115630809613598720) }, { argument := 37836937842150108695978049536, coefficient := (-37836937842150108695978049536) }, { argument := 37828681818379878190704230400, coefficient := (-37828681818379878190704230400) }, { argument := 823053379074232563343032320, coefficient := (-823053379074232563343032320) }, { argument := 68913887857313101696204800, coefficient := (-68913887857313101696204800) }, { argument := 2352253828201412020584579072, coefficient := (-2352253828201412020584579072) }, { argument := 28594494707474729522014715904, coefficient := (-28594494707474729522014715904) }, { argument := 2352282552238366908110340096, coefficient := (-2352282552238366908110340096) }, { argument := 72104896923607352689557504, coefficient := (-72104896923607352689557504) }, { argument := 20392197173756040356823040, coefficient := (-20392197173756040356823040) }, { argument := 817911329115630809613598720, coefficient := (-817911329115630809613598720) }, { argument := 817910694815992916800962560, coefficient := (-817910694815992916800962560) }, { argument := 20391163140244721673175040, coefficient := (-20391163140244721673175040) }, { argument := 817910694815992916800962560, coefficient := (-817910694815992916800962560) }, { argument := 37836907781129813905949851648, coefficient := (-37836907781129813905949851648) }, { argument := 37828651765376835162325647360, coefficient := (-37828651765376835162325647360) }, { argument := 823052736632930969174671360, coefficient := (-823052736632930969174671360) }, { argument := 837585901455105019997061120, coefficient := (-837585901455105019997061120) }, { argument := 28594494707474729522014715904, coefficient := (-28594494707474729522014715904) }, { argument := 347581302125467495841900003328, coefficient := (-347581302125467495841900003328) }, { argument := 28594846310521283430498435072, coefficient := (-28594846310521283430498435072) }, { argument := 876086725895081197062586368, coefficient := (-876086725895081197062586368) }, { argument := 940480911364944551101857792, coefficient := (-940480911364944551101857792) }, { argument := 37836937842150108695978049536, coefficient := (-37836937842150108695978049536) }, { argument := 37836907781129813905949851648, coefficient := (-37836907781129813905949851648) }, { argument := 940432359849231571524517888, coefficient := (-940432359849231571524517888) }, { argument := 20391163140244721673175040, coefficient := (-20391163140244721673175040) }, { argument := 940432359849231571524517888, coefficient := (-940432359849231571524517888) }, { argument := 940232988447807760244932608, coefficient := (-940232988447807760244932608) }, { argument := 20502744641271801881559040, coefficient := (-20502744641271801881559040) }, { argument := 68914747621222089511403520, coefficient := (-68914747621222089511403520) }, { argument := 2352282552238366908110340096, coefficient := (-2352282552238366908110340096) }, { argument := 28594846310521283430498435072, coefficient := (-28594846310521283430498435072) }, { argument := 2352311276322609591723491328, coefficient := (-2352311276322609591723491328) }, { argument := 72105831875956544385318912, coefficient := (-72105831875956544385318912) }, { argument := 940281527914421411769221120, coefficient := (-940281527914421411769221120) }, { argument := 37828681818379878190704230400, coefficient := (-37828681818379878190704230400) }, { argument := 37828651765376835162325647360, coefficient := (-37828651765376835162325647360) }, { argument := 940232988447807760244932608, coefficient := (-940232988447807760244932608) }, { argument := 2109181624658804871266304, coefficient := (-2109181624658804871266304) }, { argument := 72104896923607352689557504, coefficient := (-72104896923607352689557504) }, { argument := 876086725895081197062586368, coefficient := (-876086725895081197062586368) }, { argument := 72105831875956544385318912, coefficient := (-72105831875956544385318912) }, { argument := 2200497102440153361678336, coefficient := (-2200497102440153361678336) }, { argument := 20503789321574114645770240, coefficient := (-20503789321574114645770240) }, { argument := 823053379074232563343032320, coefficient := (-823053379074232563343032320) }, { argument := 823052736632930969174671360, coefficient := (-823052736632930969174671360) }, { argument := 20502744641271801881559040, coefficient := (-20502744641271801881559040) }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 3843316851549392235747344384, coefficient := 3843316851549392235747344384 }, { argument := 154613168737439700519277821952, coefficient := 154613168737439700519277821952 }, { argument := 154613045955911145908502265856, coefficient := 154613045955911145908502265856 }, { argument := 3843118512157111710648369152, coefficient := 3843118512157111710648369152 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 1959083180151438056192212992, coefficient := 1959083180151438056192212992 }] }

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
def constantNumerator : ℤ := (-30792605199770853844840207089664)
def positiveArguments : Array ℕ := #[
    3540603, 43038201, 7081293, 216969, 355035, 16422859,
    8209639, 89315
  ]
def positiveCoefficients : Array ℕ := #[
    66880099745390857810190794752, 812968631541627390022945603584, 66880921437158877128457977856, 2049214266843488104740814848, 3353210768491248976889118720, 155109517788988197449108553728,
    155075696200237885050088062976, 3374225299340018898090065920
  ]
def positiveScales : Array ℕ := #[
    21, 25, 22, 17, 18, 23,
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
    21755563655895033, 25359114438606492, 22755581380799164, 17727129403083834, 18437601729582122, 23969201966206902,
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
noncomputable def positiveFloor : ℝ := 373467993 / 1000000000000
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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 66880099745390857810190794752, coefficient := 66880099745390857810190794752 }, { argument := 812968631541627390022945603584, coefficient := 812968631541627390022945603584 }, { argument := 66880921437158877128457977856, coefficient := 66880921437158877128457977856 }, { argument := 2049214266843488104740814848, coefficient := 2049214266843488104740814848 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 3353210768491248976889118720, coefficient := 3353210768491248976889118720 }, { argument := 155109517788988197449108553728, coefficient := 155109517788988197449108553728 }, { argument := 155075696200237885050088062976, coefficient := 155075696200237885050088062976 }, { argument := 3374225299340018898090065920, coefficient := 3374225299340018898090065920 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk4
