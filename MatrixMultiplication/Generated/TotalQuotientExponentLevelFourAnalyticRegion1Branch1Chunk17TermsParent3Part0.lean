import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 17, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17

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
def constantNumerator : ℤ := (-18897060492436921104936520371929088)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    13282883, 516657597, 1007, 2597, 2173, 60791,
    516440563, 2173, 1961, 1007, 1007, 1961,
    60791, 1961, 13282829, 2597, 35350089553463, 3672569497556501,
    305812500925, 275953146917839317, 96774640379, 11611437721, 305810502077, 607781840199,
    96774640379, 9379897537717, 600035551457, 29380595599845907, 305810502077, 11611437721,
    600035551457, 11611437721, 305810502077, 305824494013, 35350089553463, 2686612538110653,
    8745071917, 25655182645591751, 91503313473, 4052594303, 102620722073158641, 4052594303,
    7891894169, 149092811463, 7891894169, 91503313473, 149092811463, 1343310438385435,
    7891894169, 7891894169, 8745071917, 201, 5829, 5159,
    335, 201, 335, 10251, 335, 201,
    164217, 10519, 5829, 10251
  ]
def negativeCoefficients : Array ℕ := #[
    62726641475079001625033965568, 2439846519192772560350726848512, 38956425611261810525731815424, 50233285656627071467391025152, 672510926341782834338949234688, 1175868952003086754553010323456,
    2438821605105529429771417550848, 672510926341782834338949234688, 37931256516228604985580978176, 38956425611261810525731815424, 38956425611261810525731815424, 37931256516228604985580978176,
    1175868952003086754553010323456, 37931256516228604985580978176, 62726386467288926664192425984, 50233285656627071467391025152, 79601325070244815068750413824, 8269891310343853811795910197248,
    705155617388067565218666905600, 77673905601931055300475409661952, 446294255974172831533934575616, 26774152495888036504002363392, 705151008358380284444938338304, 700724753674949311088478388224,
    446294255974172831533934575616, 10814285582242742822321407393792, 691793890803403591222172844032, 8269902462211828823127324884992, 705151008358380284444938338304, 26774152495888036504002363392,
    691793890803403591222172844032, 26774152495888036504002363392, 705151008358380284444938338304, 705183271566191249861038309376, 79601325070244815068750413824, 3024856806381009833611568873472,
    80659051779541788925871783936, 115540671002809025547338038378496, 843969102766425059736560861184, 74757169942014340955686043648, 115540661422292122341160972713984, 74757169942014340955686043648,
    72789875996171858298957463552, 2750276936287790754106554974208, 72789875996171858298957463552, 843969102766425059736560861184, 2750276936287790754106554974208, 3024866194877771346206397562880,
    72789875996171858298957463552, 72789875996171858298957463552, 80659051779541788925871783936, 30374261217817558014492672, 440426787658354591210143744, 779606037923983989038645248,
    25311884348181298345410560, 485988179485080928231882752, 25311884348181298345410560, 774543661054347729369563136, 809980299141801547053137920, 485988179485080928231882752,
    12407885707478472448920256512, 794793168532892768045891584, 440426787658354591210143744, 774543661054347729369563136
  ]
def negativeScales : Array ℕ := #[
    23, 28, 9, 11, 11, 15,
    28, 11, 10, 9, 9, 10,
    15, 10, 23, 11, 45, 51,
    38, 57, 36, 33, 38, 39,
    36, 43, 39, 54, 38, 33,
    39, 33, 38, 38, 45, 51,
    33, 54, 36, 31, 56, 31,
    32, 37, 32, 36, 37, 50,
    32, 32, 33, 7, 12, 12,
    8, 7, 8, 13, 8, 7,
    17, 13, 12, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    23663064976467477, 28944633252712566, 9975847984030745, 11342630298678409, 11085472459181283, 15891570134331068,
    28944027087794972, 11085472459181283, 10937373828601297, 9975847984030745, 9975847984030745, 10937373828601297,
    15891570134331068, 10937373828601297, 23663059111348389, 11342630298678409, 45006779103398485, 51705711215149946,
    38153856425783064, 57937200959316028, 36493909990250669, 33434827565740260, 38153846996026227, 39144762613247320,
    36493909990250669, 43092709302046257, 39126257025134217, 54705713160608865, 38153846996026227, 33434827565740260,
    39126257025134217, 33434827565740260, 38153846996026227, 38153913003029790, 45006779103398485, 51254709694920936,
    33025823102498270, 54510099814666952, 36413104935379743, 31916198617146559, 56510099695040116, 31916198617146559,
    32877724466422546, 37117419743255623, 32877724466422546, 36413104935379743, 37117419743255623, 50254714172725198,
    32877724466422546, 32877724466422546, 33025823102498270, 7651051691200812, 12509032686306867, 12332875731152675,
    8388017285345139, 7651051691200812, 8388017285345139, 13323477033150425, 8388017285345139, 7651051691200812,
    17325243959324613, 13360709939349401, 12509032686306867, 13323477033150425
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
noncomputable def negativeCeiling : ℝ := 237427962081 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 62726641475079001625033965568, coefficient := (-62726641475079001625033965568) }, { argument := 2439846519192772560350726848512, coefficient := (-2439846519192772560350726848512) }, { argument := 38956425611261810525731815424, coefficient := (-38956425611261810525731815424) }, { argument := 50233285656627071467391025152, coefficient := (-50233285656627071467391025152) }, { argument := 672510926341782834338949234688, coefficient := (-672510926341782834338949234688) }, { argument := 1175868952003086754553010323456, coefficient := (-1175868952003086754553010323456) }, { argument := 2438821605105529429771417550848, coefficient := (-2438821605105529429771417550848) }, { argument := 672510926341782834338949234688, coefficient := (-672510926341782834338949234688) }, { argument := 37931256516228604985580978176, coefficient := (-37931256516228604985580978176) }, { argument := 38956425611261810525731815424, coefficient := (-38956425611261810525731815424) }, { argument := 38956425611261810525731815424, coefficient := (-38956425611261810525731815424) }, { argument := 37931256516228604985580978176, coefficient := (-37931256516228604985580978176) }, { argument := 1175868952003086754553010323456, coefficient := (-1175868952003086754553010323456) }, { argument := 37931256516228604985580978176, coefficient := (-37931256516228604985580978176) }, { argument := 62726386467288926664192425984, coefficient := (-62726386467288926664192425984) }, { argument := 50233285656627071467391025152, coefficient := (-50233285656627071467391025152) }, { argument := 79601325070244815068750413824, coefficient := (-79601325070244815068750413824) }, { argument := 8269891310343853811795910197248, coefficient := (-8269891310343853811795910197248) }, { argument := 705155617388067565218666905600, coefficient := (-705155617388067565218666905600) }, { argument := 77673905601931055300475409661952, coefficient := (-77673905601931055300475409661952) }, { argument := 446294255974172831533934575616, coefficient := (-446294255974172831533934575616) }, { argument := 26774152495888036504002363392, coefficient := (-26774152495888036504002363392) }, { argument := 705151008358380284444938338304, coefficient := (-705151008358380284444938338304) }, { argument := 700724753674949311088478388224, coefficient := (-700724753674949311088478388224) }, { argument := 446294255974172831533934575616, coefficient := (-446294255974172831533934575616) }, { argument := 10814285582242742822321407393792, coefficient := (-10814285582242742822321407393792) }, { argument := 691793890803403591222172844032, coefficient := (-691793890803403591222172844032) }, { argument := 8269902462211828823127324884992, coefficient := (-8269902462211828823127324884992) }, { argument := 705151008358380284444938338304, coefficient := (-705151008358380284444938338304) }, { argument := 26774152495888036504002363392, coefficient := (-26774152495888036504002363392) }, { argument := 691793890803403591222172844032, coefficient := (-691793890803403591222172844032) }, { argument := 26774152495888036504002363392, coefficient := (-26774152495888036504002363392) }, { argument := 705151008358380284444938338304, coefficient := (-705151008358380284444938338304) }, { argument := 705183271566191249861038309376, coefficient := (-705183271566191249861038309376) }, { argument := 79601325070244815068750413824, coefficient := (-79601325070244815068750413824) }, { argument := 3024856806381009833611568873472, coefficient := (-3024856806381009833611568873472) }, { argument := 80659051779541788925871783936, coefficient := (-80659051779541788925871783936) }, { argument := 115540671002809025547338038378496, coefficient := (-115540671002809025547338038378496) }, { argument := 843969102766425059736560861184, coefficient := (-843969102766425059736560861184) }, { argument := 74757169942014340955686043648, coefficient := (-74757169942014340955686043648) }, { argument := 115540661422292122341160972713984, coefficient := (-115540661422292122341160972713984) }, { argument := 74757169942014340955686043648, coefficient := (-74757169942014340955686043648) }, { argument := 72789875996171858298957463552, coefficient := (-72789875996171858298957463552) }, { argument := 2750276936287790754106554974208, coefficient := (-2750276936287790754106554974208) }, { argument := 72789875996171858298957463552, coefficient := (-72789875996171858298957463552) }, { argument := 843969102766425059736560861184, coefficient := (-843969102766425059736560861184) }, { argument := 2750276936287790754106554974208, coefficient := (-2750276936287790754106554974208) }, { argument := 3024866194877771346206397562880, coefficient := (-3024866194877771346206397562880) }, { argument := 72789875996171858298957463552, coefficient := (-72789875996171858298957463552) }, { argument := 72789875996171858298957463552, coefficient := (-72789875996171858298957463552) }, { argument := 80659051779541788925871783936, coefficient := (-80659051779541788925871783936) }, { argument := 30374261217817558014492672, coefficient := (-30374261217817558014492672) }, { argument := 440426787658354591210143744, coefficient := (-440426787658354591210143744) }, { argument := 779606037923983989038645248, coefficient := (-779606037923983989038645248) }, { argument := 25311884348181298345410560, coefficient := (-25311884348181298345410560) }, { argument := 485988179485080928231882752, coefficient := (-485988179485080928231882752) }, { argument := 25311884348181298345410560, coefficient := (-25311884348181298345410560) }, { argument := 774543661054347729369563136, coefficient := (-774543661054347729369563136) }, { argument := 809980299141801547053137920, coefficient := (-809980299141801547053137920) }, { argument := 485988179485080928231882752, coefficient := (-485988179485080928231882752) }, { argument := 12407885707478472448920256512, coefficient := (-12407885707478472448920256512) }, { argument := 794793168532892768045891584, coefficient := (-794793168532892768045891584) }, { argument := 440426787658354591210143744, coefficient := (-440426787658354591210143744) }, { argument := 774543661054347729369563136, coefficient := (-774543661054347729369563136) }] }

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
def constantNumerator : ℤ := (-51048008956013079445508146723815424)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    335, 10519, 335, 10251, 335, 201,
    222100585, 2219885045, 4439769005, 222100585, 2688039583965103, 7164535,
    5936329, 9791492166239537, 39916695, 83995993832153, 159871481, 159871481,
    114427859, 5936329, 184026199, 1839333323, 3678665747, 184026199,
    71315445633, 255622715211, 17834042445, 17746050137599, 201, 17746049647105,
    201, 35350088526281, 3672569252112875, 305812573763, 275953127517036075, 96774663429,
    11611440487, 305810574915, 607781984953, 96774663429, 9379899771723, 600035694367,
    29380593636300269, 305810574915, 11611440487, 600035694367, 11611440487, 305810574915,
    305824566851, 35350088526281, 9785589269279937, 31345790639, 747828607306160687, 327984004491,
    14526098101, 373914271760176113, 14526098101, 28287664723, 534407503821, 28287664723,
    327984004491, 534407503821, 19571239976965229, 28287664723
  ]
def negativeCoefficients : Array ℕ := #[
    25311884348181298345410560, 794793168532892768045891584, 25311884348181298345410560, 774543661054347729369563136, 809980299141801547053137920, 30374261217817558014492672,
    4097032650116174534001295360, 163798605192680845224055930880, 163798565163246205274328924160, 4097032650116174534001295360, 3026463517175595241379328950272, 4229194993668309196388433920,
    219011883600680297670115328, 11024240117819377376868945625088, 5890664455466573523541032960, 3026274612184789849102146863104, 5898216589383838361391726592, 5898216589383838361391726592,
    4221642859751044358537740288, 219011883600680297670115328, 212167762238159038367924224, 8482427768906686627674324992, 8482425695953821344563462144, 212167762238159038367924224,
    82221110880906154556478455808, 294712925432753669066704551936, 82245004195647088030415585280, 79921104786988995667352879104, 30374261217817558014492672, 79921102578000400039888814080,
    30374261217817558014492672, 79601322757236578847910002688, 8269890757653942514764218368000, 705155785341060670325706981376, 77673900141090414590505988915200, 446294362273535556285225762816,
    26774158873849799989079834624, 705151176311373389551978414080, 700724920564948788948005552128, 446294362273535556285225762816, 10814288157876301643045192859648, 691794055567415814586674184192,
    8269901909522866096767147966464, 705151176311373389551978414080, 26774158873849799989079834624, 691794055567415814586674184192, 26774158873849799989079834624, 705151176311373389551978414080,
    705183439519184354968078385152, 79601322757236578847910002688, 11017594046682462128423659634688, 289113888852856794524850061312, 420990079650127781558470882361344, 3025118495557940606125870153728,
    267959214058745321754739081216, 420990043741909879497792015040512, 267959214058745321754739081216, 260907655794041497498035421184, 9858078454055946310871716724736, 260907655794041497498035421184,
    3025118495557940606125870153728, 9858078454055946310871716724736, 11017628633429895005359411560448, 260907655794041497498035421184
  ]
def negativeScales : Array ℕ := #[
    8, 13, 8, 13, 8, 7,
    27, 31, 32, 27, 51, 22,
    22, 53, 25, 46, 27, 27,
    26, 22, 27, 30, 31, 27,
    36, 37, 34, 44, 7, 44,
    7, 45, 51, 38, 57, 36,
    33, 38, 39, 36, 43, 39,
    54, 38, 33, 39, 33, 38,
    38, 45, 53, 34, 59, 38,
    33, 58, 33, 34, 38, 34,
    38, 38, 54, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    8388017285345139, 13360709939349401, 8388017285345139, 13323477033150425, 8388017285345139, 7651051691200812,
    27726637952097270, 31047837823668657, 32047837471099880, 27726637952097270, 51255475806653920, 22772441641941018,
    22501139619759487, 53120450158194877, 25250488938381244, 46255385754090040, 27252337362773613, 27252337362773613,
    26769863097819845, 22501139619759487, 27455335930146138, 30776535802248583, 31776535449679803, 27455335930146138,
    36053495520982825, 37895225090885785, 34053914704799669, 44012563183165839, 7651051691200812, 44012563143290303,
    7651051691200812, 45006779061477505, 51705711118732352, 38153856769402140, 57937200857887768, 36493910333874955,
    33434827909409502, 38153847339647549, 39144762956850631, 36493910333874955, 43092709645652249, 39126257368739730,
    54705713064191566, 38153847339647549, 33434827909409502, 39126257368739730, 33434827909409502, 38153847339647549,
    38153913346635391, 45006779061477505, 53119580153086442, 34867552670805463, 59375485273943350, 38254834501274419,
    33757928177485621, 58375485150889120, 33757928177485621, 34719454029517463, 38959149321305875, 34719454029517463,
    38254834501274419, 38959149321305875, 54119584682029011, 34719454029517463
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
noncomputable def negativeCeiling : ℝ := 70813660809 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 25311884348181298345410560, coefficient := (-25311884348181298345410560) }, { argument := 794793168532892768045891584, coefficient := (-794793168532892768045891584) }, { argument := 25311884348181298345410560, coefficient := (-25311884348181298345410560) }, { argument := 774543661054347729369563136, coefficient := (-774543661054347729369563136) }, { argument := 809980299141801547053137920, coefficient := (-809980299141801547053137920) }, { argument := 30374261217817558014492672, coefficient := (-30374261217817558014492672) }, { argument := 4097032650116174534001295360, coefficient := (-4097032650116174534001295360) }, { argument := 163798605192680845224055930880, coefficient := (-163798605192680845224055930880) }, { argument := 163798565163246205274328924160, coefficient := (-163798565163246205274328924160) }, { argument := 4097032650116174534001295360, coefficient := (-4097032650116174534001295360) }, { argument := 3026463517175595241379328950272, coefficient := (-3026463517175595241379328950272) }, { argument := 4229194993668309196388433920, coefficient := (-4229194993668309196388433920) }, { argument := 219011883600680297670115328, coefficient := (-219011883600680297670115328) }, { argument := 11024240117819377376868945625088, coefficient := (-11024240117819377376868945625088) }, { argument := 5890664455466573523541032960, coefficient := (-5890664455466573523541032960) }, { argument := 3026274612184789849102146863104, coefficient := (-3026274612184789849102146863104) }, { argument := 5898216589383838361391726592, coefficient := (-5898216589383838361391726592) }, { argument := 5898216589383838361391726592, coefficient := (-5898216589383838361391726592) }, { argument := 4221642859751044358537740288, coefficient := (-4221642859751044358537740288) }, { argument := 219011883600680297670115328, coefficient := (-219011883600680297670115328) }, { argument := 212167762238159038367924224, coefficient := (-212167762238159038367924224) }, { argument := 8482427768906686627674324992, coefficient := (-8482427768906686627674324992) }, { argument := 8482425695953821344563462144, coefficient := (-8482425695953821344563462144) }, { argument := 212167762238159038367924224, coefficient := (-212167762238159038367924224) }, { argument := 82221110880906154556478455808, coefficient := (-82221110880906154556478455808) }, { argument := 294712925432753669066704551936, coefficient := (-294712925432753669066704551936) }, { argument := 82245004195647088030415585280, coefficient := (-82245004195647088030415585280) }, { argument := 79921104786988995667352879104, coefficient := (-79921104786988995667352879104) }, { argument := 30374261217817558014492672, coefficient := (-30374261217817558014492672) }, { argument := 79921102578000400039888814080, coefficient := (-79921102578000400039888814080) }, { argument := 30374261217817558014492672, coefficient := (-30374261217817558014492672) }, { argument := 79601322757236578847910002688, coefficient := (-79601322757236578847910002688) }, { argument := 8269890757653942514764218368000, coefficient := (-8269890757653942514764218368000) }, { argument := 705155785341060670325706981376, coefficient := (-705155785341060670325706981376) }, { argument := 77673900141090414590505988915200, coefficient := (-77673900141090414590505988915200) }, { argument := 446294362273535556285225762816, coefficient := (-446294362273535556285225762816) }, { argument := 26774158873849799989079834624, coefficient := (-26774158873849799989079834624) }, { argument := 705151176311373389551978414080, coefficient := (-705151176311373389551978414080) }, { argument := 700724920564948788948005552128, coefficient := (-700724920564948788948005552128) }, { argument := 446294362273535556285225762816, coefficient := (-446294362273535556285225762816) }, { argument := 10814288157876301643045192859648, coefficient := (-10814288157876301643045192859648) }, { argument := 691794055567415814586674184192, coefficient := (-691794055567415814586674184192) }, { argument := 8269901909522866096767147966464, coefficient := (-8269901909522866096767147966464) }, { argument := 705151176311373389551978414080, coefficient := (-705151176311373389551978414080) }, { argument := 26774158873849799989079834624, coefficient := (-26774158873849799989079834624) }, { argument := 691794055567415814586674184192, coefficient := (-691794055567415814586674184192) }, { argument := 26774158873849799989079834624, coefficient := (-26774158873849799989079834624) }, { argument := 705151176311373389551978414080, coefficient := (-705151176311373389551978414080) }, { argument := 705183439519184354968078385152, coefficient := (-705183439519184354968078385152) }, { argument := 79601322757236578847910002688, coefficient := (-79601322757236578847910002688) }, { argument := 11017594046682462128423659634688, coefficient := (-11017594046682462128423659634688) }, { argument := 289113888852856794524850061312, coefficient := (-289113888852856794524850061312) }, { argument := 420990079650127781558470882361344, coefficient := (-420990079650127781558470882361344) }, { argument := 3025118495557940606125870153728, coefficient := (-3025118495557940606125870153728) }, { argument := 267959214058745321754739081216, coefficient := (-267959214058745321754739081216) }, { argument := 420990043741909879497792015040512, coefficient := (-420990043741909879497792015040512) }, { argument := 267959214058745321754739081216, coefficient := (-267959214058745321754739081216) }, { argument := 260907655794041497498035421184, coefficient := (-260907655794041497498035421184) }, { argument := 9858078454055946310871716724736, coefficient := (-9858078454055946310871716724736) }, { argument := 260907655794041497498035421184, coefficient := (-260907655794041497498035421184) }, { argument := 3025118495557940606125870153728, coefficient := (-3025118495557940606125870153728) }, { argument := 9858078454055946310871716724736, coefficient := (-9858078454055946310871716724736) }, { argument := 11017628633429895005359411560448, coefficient := (-11017628633429895005359411560448) }, { argument := 260907655794041497498035421184, coefficient := (-260907655794041497498035421184) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17
