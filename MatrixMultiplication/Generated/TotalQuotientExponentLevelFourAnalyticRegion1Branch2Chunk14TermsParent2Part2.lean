import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 14, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-604869445870989457890519384326144)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1819077155, 217613025, 507763725, 6600928425, 6600928425, 217613025,
    81459809025, 3264195375, 1694686805, 6600928425, 507763725, 3264195375,
    507763725, 6600928425, 6600928425, 27469995, 614535831, 51675852137,
    25837919835, 307274149, 8512035, 1358922495, 54240011805, 1358922495,
    34044255, 81514151, 132106031, 16066887721, 2078931751, 62576541,
    4016720959, 62576541, 62576541, 5360723679, 62576541, 2078931751,
    5360723679, 652117093, 62576541, 62576541, 132106031, 76685,
    12242545, 488648755, 12242545, 306705, 15578521, 575294055,
    4602351313, 124629295, 3008053, 10761111, 752013, 12920931,
    62576541, 12920931, 47271987, 3975065549, 1987532295, 23636473,
    12920931, 62576541, 12920931, 303891345
  ]
def negativeCoefficients : Array ℕ := #[
    134224202914466725799835729920, 128456056936984271953644748800, 9366587484988436496619929600, 243531274609699348912118169600, 243531274609699348912118169600, 128456056936984271953644748800,
    3005336498754861195915480268800, 240855106756845509913083904000, 125045815107710098104406507520, 243531274609699348912118169600, 9366587484988436496619929600, 240855106756845509913083904000,
    9366587484988436496619929600, 243531274609699348912118169600, 243531274609699348912118169600, 8107711479537296229500190720, 2834046299645356138743988224, 238312804790523954598246350848,
    238312747296634362864001351680, 2834103793534947872988987392, 1256154649531666265517588480, 200541563850174782298768015360, 2001103232643639739586193653760, 200541563850174782298768015360,
    1256011318330213542301532160, 6014682727530862082275672064, 2436926144450540310779396096, 148190882925156756889763053568, 19174760978702935603237879808, 2308666873689985557580480512,
    148190847092356393708959039488, 2308666873689985557580480512, 2308666873689985557580480512, 98887897756387714716363915264, 2308666873689985557580480512, 19174760978702935603237879808,
    98887897756387714716363915264, 6014718560331225263079686144, 2308666873689985557580480512, 2308666873689985557580480512, 2436926144450540310779396096, 90533668434714685803069440,
    14453446043255840165676974080, 144223656406748810060266209280, 14453446043255840165676974080, 90523338258033408454164480, 4597967838942556764007038976, 169796835195385389462407086080,
    169796793616424247321077743616, 4598009417903698905336381440, 3551282166473871223498473472, 12704477476209962668800344064, 3551280985882250506087170048, 238349107351060030471274496,
    2308666873689985557580480512, 238349107351060030471274496, 109001780755590620720922624, 9165877107327844407624859648, 9165874896024398571692359680, 109003992059036456653422592,
    238349107351060030471274496, 2308666873689985557580480512, 238349107351060030471274496, 2802902933715187389966581760
  ]
def negativeScales : Array ℕ := #[
    30, 27, 28, 32, 32, 27,
    36, 31, 30, 32, 28, 31,
    28, 32, 32, 24, 29, 35,
    34, 28, 23, 30, 35, 30,
    25, 26, 26, 33, 30, 25,
    31, 25, 25, 32, 25, 30,
    32, 29, 25, 25, 26, 16,
    23, 28, 23, 18, 23, 29,
    32, 26, 21, 23, 19, 23,
    25, 23, 25, 31, 30, 24,
    23, 25, 23, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30760559589548284, 27697189669341918, 28919582096789483, 32620021808761460, 32620021808761460, 27697189669341918,
    36245369380953616, 31604080264889018, 30658371527596345, 32620021808761460, 28919582096789483, 31604080264889018,
    28919582096789483, 32620021808761460, 32620021808761460, 24711353312124959, 29194921889630073, 35588771222827226,
    34588770874771403, 28194951157079959, 23021072652285295, 30339816029541345, 35658638441367988, 30339816029541345,
    25020908026845408, 26280547199694283, 26977121106505271, 33903371448528822, 30953195261899076, 25899118582441565,
    31903371099682706, 25899118582441565, 25899118582441565, 32319780626615186, 25899118582441565, 30953195261899076,
    32319780626615186, 29280555794603065, 25899118582441565, 25899118582441565, 26977121106505271, 16226656785935189,
    23545400163192394, 28864222577258193, 23545400163192394, 18226492160495302, 23893054940794657, 29099724320810128,
    32099723967530467, 26893067986882865, 21520398555942497, 23359323696701575, 19520398076331506, 23623206689415947,
    25899118582441565, 23623206689415947, 25494482171489206, 31888331508219841, 30888331160163995, 24494511438939092,
    23623206689415947, 25899118582441565, 23623206689415947, 28178980345761052
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 3795393311 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 134224202914466725799835729920, coefficient := (-134224202914466725799835729920) }, { argument := 128456056936984271953644748800, coefficient := (-128456056936984271953644748800) }, { argument := 9366587484988436496619929600, coefficient := (-9366587484988436496619929600) }, { argument := 243531274609699348912118169600, coefficient := (-243531274609699348912118169600) }, { argument := 243531274609699348912118169600, coefficient := (-243531274609699348912118169600) }, { argument := 128456056936984271953644748800, coefficient := (-128456056936984271953644748800) }, { argument := 3005336498754861195915480268800, coefficient := (-3005336498754861195915480268800) }, { argument := 240855106756845509913083904000, coefficient := (-240855106756845509913083904000) }, { argument := 125045815107710098104406507520, coefficient := (-125045815107710098104406507520) }, { argument := 243531274609699348912118169600, coefficient := (-243531274609699348912118169600) }, { argument := 9366587484988436496619929600, coefficient := (-9366587484988436496619929600) }, { argument := 240855106756845509913083904000, coefficient := (-240855106756845509913083904000) }, { argument := 9366587484988436496619929600, coefficient := (-9366587484988436496619929600) }, { argument := 243531274609699348912118169600, coefficient := (-243531274609699348912118169600) }, { argument := 243531274609699348912118169600, coefficient := (-243531274609699348912118169600) }, { argument := 8107711479537296229500190720, coefficient := (-8107711479537296229500190720) }, { argument := 2834046299645356138743988224, coefficient := (-2834046299645356138743988224) }, { argument := 238312804790523954598246350848, coefficient := (-238312804790523954598246350848) }, { argument := 238312747296634362864001351680, coefficient := (-238312747296634362864001351680) }, { argument := 2834103793534947872988987392, coefficient := (-2834103793534947872988987392) }, { argument := 1256154649531666265517588480, coefficient := (-1256154649531666265517588480) }, { argument := 200541563850174782298768015360, coefficient := (-200541563850174782298768015360) }, { argument := 2001103232643639739586193653760, coefficient := (-2001103232643639739586193653760) }, { argument := 200541563850174782298768015360, coefficient := (-200541563850174782298768015360) }, { argument := 1256011318330213542301532160, coefficient := (-1256011318330213542301532160) }, { argument := 6014682727530862082275672064, coefficient := (-6014682727530862082275672064) }, { argument := 2436926144450540310779396096, coefficient := (-2436926144450540310779396096) }, { argument := 148190882925156756889763053568, coefficient := (-148190882925156756889763053568) }, { argument := 19174760978702935603237879808, coefficient := (-19174760978702935603237879808) }, { argument := 2308666873689985557580480512, coefficient := (-2308666873689985557580480512) }, { argument := 148190847092356393708959039488, coefficient := (-148190847092356393708959039488) }, { argument := 2308666873689985557580480512, coefficient := (-2308666873689985557580480512) }, { argument := 2308666873689985557580480512, coefficient := (-2308666873689985557580480512) }, { argument := 98887897756387714716363915264, coefficient := (-98887897756387714716363915264) }, { argument := 2308666873689985557580480512, coefficient := (-2308666873689985557580480512) }, { argument := 19174760978702935603237879808, coefficient := (-19174760978702935603237879808) }, { argument := 98887897756387714716363915264, coefficient := (-98887897756387714716363915264) }, { argument := 6014718560331225263079686144, coefficient := (-6014718560331225263079686144) }, { argument := 2308666873689985557580480512, coefficient := (-2308666873689985557580480512) }, { argument := 2308666873689985557580480512, coefficient := (-2308666873689985557580480512) }, { argument := 2436926144450540310779396096, coefficient := (-2436926144450540310779396096) }, { argument := 90533668434714685803069440, coefficient := (-90533668434714685803069440) }, { argument := 14453446043255840165676974080, coefficient := (-14453446043255840165676974080) }, { argument := 144223656406748810060266209280, coefficient := (-144223656406748810060266209280) }, { argument := 14453446043255840165676974080, coefficient := (-14453446043255840165676974080) }, { argument := 90523338258033408454164480, coefficient := (-90523338258033408454164480) }, { argument := 4597967838942556764007038976, coefficient := (-4597967838942556764007038976) }, { argument := 169796835195385389462407086080, coefficient := (-169796835195385389462407086080) }, { argument := 169796793616424247321077743616, coefficient := (-169796793616424247321077743616) }, { argument := 4598009417903698905336381440, coefficient := (-4598009417903698905336381440) }, { argument := 3551282166473871223498473472, coefficient := (-3551282166473871223498473472) }, { argument := 12704477476209962668800344064, coefficient := (-12704477476209962668800344064) }, { argument := 3551280985882250506087170048, coefficient := (-3551280985882250506087170048) }, { argument := 238349107351060030471274496, coefficient := (-238349107351060030471274496) }, { argument := 2308666873689985557580480512, coefficient := (-2308666873689985557580480512) }, { argument := 238349107351060030471274496, coefficient := (-238349107351060030471274496) }, { argument := 109001780755590620720922624, coefficient := (-109001780755590620720922624) }, { argument := 9165877107327844407624859648, coefficient := (-9165877107327844407624859648) }, { argument := 9165874896024398571692359680, coefficient := (-9165874896024398571692359680) }, { argument := 109003992059036456653422592, coefficient := (-109003992059036456653422592) }, { argument := 238349107351060030471274496, coefficient := (-238349107351060030471274496) }, { argument := 2308666873689985557580480512, coefficient := (-2308666873689985557580480512) }, { argument := 238349107351060030471274496, coefficient := (-238349107351060030471274496) }, { argument := 2802902933715187389966581760, coefficient := (-2802902933715187389966581760) }] }

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

end TermShard4


end Parent2

namespace Parent2

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-564825695003371216853199677816832)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    25553992815, 12776993325, 151948755, 598143, 95491851, 3811460289,
    95491851, 2392299, 47271987, 3975065549, 1987532295, 23636473,
    598143, 95491851, 3811460289, 95491851, 2392299, 2999591,
    110770905, 886167023, 23996945, 27277521, 132106031, 27277521,
    614535831, 51675852137, 25837919835, 307274149, 598143, 95491851,
    3811460289, 95491851, 2392299, 614535831, 51675852137, 25837919835,
    307274149, 598143, 95491851, 3811460289, 95491851, 2392299,
    62217323, 2297602965, 18380819219, 497743085, 598143, 95491851,
    3811460289, 95491851, 2392299, 31253803, 1154161365, 9233288659,
    250032685, 3008053, 10761111, 752013, 169763067, 6883406709,
    9858375, 92668725, 1094279625, 76895325
  ]
def negativeCoefficients : Array ℕ := #[
    235693982759858856196067819520, 235693925897770248986374963200, 2802959795803794599659438080, 88270326723846818657992704, 14092109892174444161535049728, 140618064996580089808759554048,
    14092109892174444161535049728, 88260254801582573242810368, 109001780755590620720922624, 9165877107327844407624859648, 9165874896024398571692359680, 109003992059036456653422592,
    88270326723846818657992704, 14092109892174444161535049728, 140618064996580089808759554048, 14092109892174444161535049728, 88260254801582573242810368, 221330750011210030565556224,
    8173450141392774958594129920, 8173448139921042961107779584, 221332751482942028051906560, 251590724426118921053011968, 2436926144450540310779396096, 251590724426118921053011968,
    2834046299645356138743988224, 238312804790523954598246350848, 238312747296634362864001351680, 2834103793534947872988987392, 88270326723846818657992704, 14092109892174444161535049728,
    140618064996580089808759554048, 14092109892174444161535049728, 88260254801582573242810368, 2834046299645356138743988224, 238312804790523954598246350848, 238312747296634362864001351680,
    2834103793534947872988987392, 2824650455163098197055766528, 450947516549582213169121591296, 4499778079890562873880305729536, 450947516549582213169121591296, 2824328153650642343769931776,
    4590828137329291924311375872, 169533175513404977366968565760, 169533133999007439483622653952, 4590869651726829807657287680, 88270326723846818657992704, 14092109892174444161535049728,
    140618064996580089808759554048, 14092109892174444161535049728, 88260254801582573242810368, 4612247242169086443398365184, 170324154559346213653284126720, 170324112851257862995987922944,
    4612288950257437100694568960, 3551282166473871223498473472, 12704477476209962668800344064, 3551280985882250506087170048, 195723490632312971845435392, 7936027619761144881934761984,
    90927460303828200456192000, 106839765856998135536025600, 1261618511715616281329664000, 2836936761479439854233190400
  ]
def negativeScales : Array ℕ := #[
    34, 33, 27, 19, 26, 31,
    26, 21, 25, 31, 30, 24,
    19, 26, 31, 26, 21, 21,
    26, 29, 24, 24, 26, 24,
    29, 35, 34, 28, 19, 26,
    31, 26, 21, 29, 35, 34,
    28, 19, 26, 31, 26, 21,
    25, 31, 34, 28, 19, 26,
    31, 26, 21, 24, 30, 33,
    27, 21, 23, 19, 27, 32,
    23, 26, 30, 26
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34572829678956690, 33572829330900867, 27179009613210937, 19190130909910075, 26508874287166488, 31827696700090859,
    26508874287166488, 21189966284470188, 25494482171489206, 31888331508219841, 30888331160163995, 24494511438939092,
    19190130909910075, 26508874287166488, 31827696700090859, 26508874287166488, 21189966284470188, 21516334369213142,
    26723003753205601, 29723003399925939, 24516347415300441, 24701209201481082, 26977121106505271, 24701209201481082,
    29194921889630073, 35588771222827226, 34588770874771403, 28194951157079959, 19190130909910075, 26508874287166488,
    31827696700090859, 26508874287166488, 21189966284470188, 29194921889630073, 35588771222827226, 34588770874771403,
    28194951157079959, 19190130909910075, 26508874287166488, 31827696700090859, 26508874287166488, 21189966284470188,
    25890812989854660, 31097482370023459, 34097482016743798, 28890826035942834, 19190130909910075, 26508874287166488,
    31827696700090859, 26508874287166488, 21189966284470188, 24897528417697754, 30104197797389436, 33104197444109775,
    27897541463786033, 21520398555942497, 23359323696701575, 19520398076331506, 27338947384941835, 32680475608750041,
    23232918429654735, 26465579186445092, 30027334296004841, 26196392553629621
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 3157619747 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 235693982759858856196067819520, coefficient := (-235693982759858856196067819520) }, { argument := 235693925897770248986374963200, coefficient := (-235693925897770248986374963200) }, { argument := 2802959795803794599659438080, coefficient := (-2802959795803794599659438080) }, { argument := 88270326723846818657992704, coefficient := (-88270326723846818657992704) }, { argument := 14092109892174444161535049728, coefficient := (-14092109892174444161535049728) }, { argument := 140618064996580089808759554048, coefficient := (-140618064996580089808759554048) }, { argument := 14092109892174444161535049728, coefficient := (-14092109892174444161535049728) }, { argument := 88260254801582573242810368, coefficient := (-88260254801582573242810368) }, { argument := 109001780755590620720922624, coefficient := (-109001780755590620720922624) }, { argument := 9165877107327844407624859648, coefficient := (-9165877107327844407624859648) }, { argument := 9165874896024398571692359680, coefficient := (-9165874896024398571692359680) }, { argument := 109003992059036456653422592, coefficient := (-109003992059036456653422592) }, { argument := 88270326723846818657992704, coefficient := (-88270326723846818657992704) }, { argument := 14092109892174444161535049728, coefficient := (-14092109892174444161535049728) }, { argument := 140618064996580089808759554048, coefficient := (-140618064996580089808759554048) }, { argument := 14092109892174444161535049728, coefficient := (-14092109892174444161535049728) }, { argument := 88260254801582573242810368, coefficient := (-88260254801582573242810368) }, { argument := 221330750011210030565556224, coefficient := (-221330750011210030565556224) }, { argument := 8173450141392774958594129920, coefficient := (-8173450141392774958594129920) }, { argument := 8173448139921042961107779584, coefficient := (-8173448139921042961107779584) }, { argument := 221332751482942028051906560, coefficient := (-221332751482942028051906560) }, { argument := 251590724426118921053011968, coefficient := (-251590724426118921053011968) }, { argument := 2436926144450540310779396096, coefficient := (-2436926144450540310779396096) }, { argument := 251590724426118921053011968, coefficient := (-251590724426118921053011968) }, { argument := 2834046299645356138743988224, coefficient := (-2834046299645356138743988224) }, { argument := 238312804790523954598246350848, coefficient := (-238312804790523954598246350848) }, { argument := 238312747296634362864001351680, coefficient := (-238312747296634362864001351680) }, { argument := 2834103793534947872988987392, coefficient := (-2834103793534947872988987392) }, { argument := 88270326723846818657992704, coefficient := (-88270326723846818657992704) }, { argument := 14092109892174444161535049728, coefficient := (-14092109892174444161535049728) }, { argument := 140618064996580089808759554048, coefficient := (-140618064996580089808759554048) }, { argument := 14092109892174444161535049728, coefficient := (-14092109892174444161535049728) }, { argument := 88260254801582573242810368, coefficient := (-88260254801582573242810368) }, { argument := 2834046299645356138743988224, coefficient := (-2834046299645356138743988224) }, { argument := 238312804790523954598246350848, coefficient := (-238312804790523954598246350848) }, { argument := 238312747296634362864001351680, coefficient := (-238312747296634362864001351680) }, { argument := 2834103793534947872988987392, coefficient := (-2834103793534947872988987392) }, { argument := 2824650455163098197055766528, coefficient := (-2824650455163098197055766528) }, { argument := 450947516549582213169121591296, coefficient := (-450947516549582213169121591296) }, { argument := 4499778079890562873880305729536, coefficient := (-4499778079890562873880305729536) }, { argument := 450947516549582213169121591296, coefficient := (-450947516549582213169121591296) }, { argument := 2824328153650642343769931776, coefficient := (-2824328153650642343769931776) }, { argument := 4590828137329291924311375872, coefficient := (-4590828137329291924311375872) }, { argument := 169533175513404977366968565760, coefficient := (-169533175513404977366968565760) }, { argument := 169533133999007439483622653952, coefficient := (-169533133999007439483622653952) }, { argument := 4590869651726829807657287680, coefficient := (-4590869651726829807657287680) }, { argument := 88270326723846818657992704, coefficient := (-88270326723846818657992704) }, { argument := 14092109892174444161535049728, coefficient := (-14092109892174444161535049728) }, { argument := 140618064996580089808759554048, coefficient := (-140618064996580089808759554048) }, { argument := 14092109892174444161535049728, coefficient := (-14092109892174444161535049728) }, { argument := 88260254801582573242810368, coefficient := (-88260254801582573242810368) }, { argument := 4612247242169086443398365184, coefficient := (-4612247242169086443398365184) }, { argument := 170324154559346213653284126720, coefficient := (-170324154559346213653284126720) }, { argument := 170324112851257862995987922944, coefficient := (-170324112851257862995987922944) }, { argument := 4612288950257437100694568960, coefficient := (-4612288950257437100694568960) }, { argument := 3551282166473871223498473472, coefficient := (-3551282166473871223498473472) }, { argument := 12704477476209962668800344064, coefficient := (-12704477476209962668800344064) }, { argument := 3551280985882250506087170048, coefficient := (-3551280985882250506087170048) }, { argument := 195723490632312971845435392, coefficient := (-195723490632312971845435392) }, { argument := 7936027619761144881934761984, coefficient := (-7936027619761144881934761984) }, { argument := 90927460303828200456192000, coefficient := (-90927460303828200456192000) }, { argument := 106839765856998135536025600, coefficient := (-106839765856998135536025600) }, { argument := 1261618511715616281329664000, coefficient := (-1261618511715616281329664000) }, { argument := 2836936761479439854233190400, coefficient := (-2836936761479439854233190400) }] }

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

end TermShard5


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14
