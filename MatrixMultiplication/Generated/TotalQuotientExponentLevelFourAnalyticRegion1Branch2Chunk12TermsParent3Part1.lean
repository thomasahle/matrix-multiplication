import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 12, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-6050682358237815098420933446074368)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    23021609185533, 31395, 52325, 1601145, 52325, 1643005,
    52325, 1601145, 910455, 1643005, 25649715, 31395,
    52325, 1601145, 52325, 31395, 52325, 805805,
    910455, 31395, 324333576511321, 6365, 12004463184831655, 100165,
    3015, 6001983253028351, 3015, 3015, 258285, 3015,
    100165, 258285, 162415141814273, 3015, 3015, 6365,
    945, 1575, 48195, 1575, 49455, 1575,
    48195, 27405, 49455, 772065, 945, 1575,
    48195, 1575, 945, 1575, 24255, 27405,
    945, 14646565513, 194769, 244845222299, 3065049, 92259,
    244845342237, 92259, 92259, 7903521
  ]
def negativeCoefficients : Array ℕ := #[
    414720442197742426851976937472, 593034782918770045935943680, 15814260877833867891625164800, 15122386964428636171366563840, 494195652432308371613286400, 15517743486374482868657192960,
    494195652432308371613286400, 15122386964428636171366563840, 8599004352322165666071183360, 15517743486374482868657192960, 242254708822317563764832993280, 9488556526700320734975098880,
    15814260877833867891625164800, 15122386964428636171366563840, 494195652432308371613286400, 9488556526700320734975098880, 494195652432308371613286400, 15221226094915097845689221120,
    8599004352322165666071183360, 593034782918770045935943680, 1460668574320125509640405385216, 1923703210461778674251202560, 54063295925990679107920073850880, 15136506840212416410555514880,
    1822455673069053480869560320, 54061059083644877942678137864192, 1822455673069053480869560320, 1822455673069053480869560320, 78061851329791124097246167040, 1822455673069053480869560320,
    15136506840212416410555514880, 78061851329791124097246167040, 1462905544308172292915583778816, 1822455673069053480869560320, 1822455673069053480869560320, 1923703210461778674251202560,
    71402181220989035631083520, 1904058165893040950162227200, 1820755621135220408592629760, 59501817684157529692569600, 1868357075282546432346685440, 59501817684157529692569600,
    1820755621135220408592629760, 1035331627704341016650711040, 1868357075282546432346685440, 29167791028774021055297617920, 1142434899535824570097336320, 1904058165893040950162227200,
    1820755621135220408592629760, 59501817684157529692569600, 1142434899535824570097336320, 59501817684157529692569600, 1832655984672051914531143680, 1035331627704341016650711040,
    71402181220989035631083520, 33772680697141431084699877376, 1839541195004075857252712448, 1129149288355044001744783671296, 14474284665953123192593711104, 1742723237372282391081517056,
    1129149841471441679888834101248, 1742723237372282391081517056, 1742723237372282391081517056, 74646645334112762417991647232
  ]
def negativeScales : Array ℕ := #[
    44, 14, 15, 20, 15, 20,
    15, 20, 19, 20, 24, 14,
    15, 20, 15, 14, 15, 19,
    19, 14, 48, 12, 53, 16,
    11, 52, 11, 11, 17, 11,
    16, 17, 47, 11, 11, 12,
    9, 10, 15, 10, 15, 10,
    15, 14, 15, 19, 9, 10,
    15, 10, 9, 10, 14, 14,
    9, 33, 17, 37, 21, 16,
    37, 16, 16, 22
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    44388053913350300, 14938247200400131, 15675212786070387, 20610672533843301, 15675212786070387, 20647905440054897,
    15675212786070387, 20610672533843301, 19796228187589900, 20647905440054897, 24612439460017861, 14938247200400131,
    15675212786070387, 20610672533843301, 15675212786070387, 14938247200400131, 15675212786070387, 19620071231847735,
    19796228187589900, 14938247200400131, 48204471714408855, 12635944798803559, 53414420408821771, 16612018959551099,
    11557942286789136, 52414360716787359, 11557942286789136, 11557942286789136, 17978604352023330, 11557942286789136,
    16612018959551099, 17978604352023330, 47206679468347853, 11557942286789136, 11557942286789136, 12635944798803559,
    9884170522387776, 10621136113284685, 15556595861081553, 10621136113284685, 15593828767283669, 10621136113284685,
    15556595861081553, 14742151514425259, 15593828767283669, 19558362787255829, 9884170522387776, 10621136113284685,
    15556595861081553, 10621136113284685, 9884170522387776, 10621136113284685, 14565994559084324, 14742151514425259,
    9884170522387776, 33769843354599189, 17571404546596521, 37833079089810405, 21547478707349761, 16493402034592954,
    37833079796517761, 16493402034592954, 16493402034592954, 22914064088673542
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
noncomputable def negativeCeiling : ℝ := 71996818607 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 414720442197742426851976937472, coefficient := (-414720442197742426851976937472) }, { argument := 593034782918770045935943680, coefficient := (-593034782918770045935943680) }, { argument := 15814260877833867891625164800, coefficient := (-15814260877833867891625164800) }, { argument := 15122386964428636171366563840, coefficient := (-15122386964428636171366563840) }, { argument := 494195652432308371613286400, coefficient := (-494195652432308371613286400) }, { argument := 15517743486374482868657192960, coefficient := (-15517743486374482868657192960) }, { argument := 494195652432308371613286400, coefficient := (-494195652432308371613286400) }, { argument := 15122386964428636171366563840, coefficient := (-15122386964428636171366563840) }, { argument := 8599004352322165666071183360, coefficient := (-8599004352322165666071183360) }, { argument := 15517743486374482868657192960, coefficient := (-15517743486374482868657192960) }, { argument := 242254708822317563764832993280, coefficient := (-242254708822317563764832993280) }, { argument := 9488556526700320734975098880, coefficient := (-9488556526700320734975098880) }, { argument := 15814260877833867891625164800, coefficient := (-15814260877833867891625164800) }, { argument := 15122386964428636171366563840, coefficient := (-15122386964428636171366563840) }, { argument := 494195652432308371613286400, coefficient := (-494195652432308371613286400) }, { argument := 9488556526700320734975098880, coefficient := (-9488556526700320734975098880) }, { argument := 494195652432308371613286400, coefficient := (-494195652432308371613286400) }, { argument := 15221226094915097845689221120, coefficient := (-15221226094915097845689221120) }, { argument := 8599004352322165666071183360, coefficient := (-8599004352322165666071183360) }, { argument := 593034782918770045935943680, coefficient := (-593034782918770045935943680) }, { argument := 1460668574320125509640405385216, coefficient := (-1460668574320125509640405385216) }, { argument := 1923703210461778674251202560, coefficient := (-1923703210461778674251202560) }, { argument := 54063295925990679107920073850880, coefficient := (-54063295925990679107920073850880) }, { argument := 15136506840212416410555514880, coefficient := (-15136506840212416410555514880) }, { argument := 1822455673069053480869560320, coefficient := (-1822455673069053480869560320) }, { argument := 54061059083644877942678137864192, coefficient := (-54061059083644877942678137864192) }, { argument := 1822455673069053480869560320, coefficient := (-1822455673069053480869560320) }, { argument := 1822455673069053480869560320, coefficient := (-1822455673069053480869560320) }, { argument := 78061851329791124097246167040, coefficient := (-78061851329791124097246167040) }, { argument := 1822455673069053480869560320, coefficient := (-1822455673069053480869560320) }, { argument := 15136506840212416410555514880, coefficient := (-15136506840212416410555514880) }, { argument := 78061851329791124097246167040, coefficient := (-78061851329791124097246167040) }, { argument := 1462905544308172292915583778816, coefficient := (-1462905544308172292915583778816) }, { argument := 1822455673069053480869560320, coefficient := (-1822455673069053480869560320) }, { argument := 1822455673069053480869560320, coefficient := (-1822455673069053480869560320) }, { argument := 1923703210461778674251202560, coefficient := (-1923703210461778674251202560) }, { argument := 71402181220989035631083520, coefficient := (-71402181220989035631083520) }, { argument := 1904058165893040950162227200, coefficient := (-1904058165893040950162227200) }, { argument := 1820755621135220408592629760, coefficient := (-1820755621135220408592629760) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 1868357075282546432346685440, coefficient := (-1868357075282546432346685440) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 1820755621135220408592629760, coefficient := (-1820755621135220408592629760) }, { argument := 1035331627704341016650711040, coefficient := (-1035331627704341016650711040) }, { argument := 1868357075282546432346685440, coefficient := (-1868357075282546432346685440) }, { argument := 29167791028774021055297617920, coefficient := (-29167791028774021055297617920) }, { argument := 1142434899535824570097336320, coefficient := (-1142434899535824570097336320) }, { argument := 1904058165893040950162227200, coefficient := (-1904058165893040950162227200) }, { argument := 1820755621135220408592629760, coefficient := (-1820755621135220408592629760) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 1142434899535824570097336320, coefficient := (-1142434899535824570097336320) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 1832655984672051914531143680, coefficient := (-1832655984672051914531143680) }, { argument := 1035331627704341016650711040, coefficient := (-1035331627704341016650711040) }, { argument := 71402181220989035631083520, coefficient := (-71402181220989035631083520) }, { argument := 33772680697141431084699877376, coefficient := (-33772680697141431084699877376) }, { argument := 1839541195004075857252712448, coefficient := (-1839541195004075857252712448) }, { argument := 1129149288355044001744783671296, coefficient := (-1129149288355044001744783671296) }, { argument := 14474284665953123192593711104, coefficient := (-14474284665953123192593711104) }, { argument := 1742723237372282391081517056, coefficient := (-1742723237372282391081517056) }, { argument := 1129149841471441679888834101248, coefficient := (-1129149841471441679888834101248) }, { argument := 1742723237372282391081517056, coefficient := (-1742723237372282391081517056) }, { argument := 1742723237372282391081517056, coefficient := (-1742723237372282391081517056) }, { argument := 74646645334112762417991647232, coefficient := (-74646645334112762417991647232) }] }

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

end TermShard2


end Parent3

namespace Parent3

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-91825094621379037361709455025111040)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    92259, 3065049, 7903521, 14646445575, 92259, 92259,
    194769, 420090873702995, 735288298157485, 420090869688915, 836928460492155, 52775010683777669,
    1444932045, 3288992463, 50260507947, 41412808377, 26387506607595333, 50260507947,
    1444932045, 2826829647, 2774188737, 2826829647, 41412808377, 2774188737,
    418462964539579, 3288992463, 725643994246309, 96036897213227853, 245601130299, 1968428450422954973,
    8106653027, 18888716903, 245601130299, 245463934779, 8106653027, 3032049950787,
    121393612365, 12004613546753985, 245601130299, 18888716903, 121393612365, 18888716903,
    245603209019, 245463934779, 1473329142360111, 6634937919440733, 6365, 246047707134006435,
    100165, 3015, 1968298807237873137, 3015, 3015, 258285,
    3015, 100165, 258285, 53162353222095375, 3015, 3015,
    6365, 945, 1575, 48195
  ]
def negativeCoefficients : Array ℕ := #[
    1742723237372282391081517056, 14474284665953123192593711104, 74646645334112762417991647232, 33772404138942592012674662400, 1742723237372282391081517056, 1742723237372282391081517056,
    1839541195004075857252712448, 236490137783819297390791229440, 827861026397983901643062640640, 236490135524093148361371156480, 235574418925514508832792903680, 14854844903120940963601647140864,
    53308583276033546305079869440, 60671202225320631716133470208, 927142727112954072765774692352, 1527862955008188049255997374464, 14854845615650355339228553936896, 927142727112954072765774692352,
    53308583276033546305079869440, 52145803038183713775185559552, 51174749643606535902427348992, 52145803038183713775185559552, 1527862955008188049255997374464, 51174749643606535902427348992,
    235573706396100133205886107648, 60671202225320631716133470208, 408501252761414444477377937408, 54063966812913948063340362203136, 1132635298709861411680520503296, 554063352239393929738031137292288,
    598165414733727390906636566528, 43554415823799085690211270656, 1132635298709861411680520503296, 1132002596048486536614789513216, 598165414733727390906636566528, 13982862365217857469456159080448,
    1119658449740129148235331665920, 54063973095888055207381759426560, 1132635298709861411680520503296, 43554415823799085690211270656, 1119658449740129148235331665920, 43554415823799085690211270656,
    1132644885113821637060304306176, 1132002596048486536614789513216, 414705286032943022075403042816, 14940551970809829573403852406784, 60115725326930583570350080, 554050181082038155491960296570880,
    473015838756638012829859840, 56951739783407921277173760, 554026860926892324684557684047872, 56951739783407921277173760, 56951739783407921277173760, 2439432854055972628038942720,
    56951739783407921277173760, 473015838756638012829859840, 2439432854055972628038942720, 14963872135072963639237410816000, 56951739783407921277173760, 56951739783407921277173760,
    60115725326930583570350080, 71402181220989035631083520, 1904058165893040950162227200, 1820755621135220408592629760
  ]
def negativeScales : Array ℕ := #[
    16, 21, 22, 33, 16, 16,
    17, 48, 49, 48, 49, 55,
    30, 31, 35, 35, 54, 35,
    30, 31, 31, 31, 35, 31,
    48, 31, 49, 56, 37, 60,
    32, 34, 37, 37, 32, 41,
    36, 53, 37, 34, 36, 34,
    37, 37, 50, 52, 12, 57,
    16, 11, 60, 11, 11, 17,
    11, 16, 17, 55, 11, 11,
    12, 9, 10, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    16493402034592954, 21547478707349761, 22914064088673542, 33769831540589454, 16493402034592954, 16493402034592954,
    17571404546596521, 48577694772649832, 49385303353571341, 48577694758864497, 49572097636859341, 55550704483830925,
    30428354498513735, 31614998556116109, 35548706200453895, 35269357990127386, 54550704553031420, 35548706200453895,
    30428354498513735, 31396537798763604, 31369418796179625, 31396537798763604, 35269357990127386, 31369418796179625,
    48572093273209790, 31614998556116109, 49366255254461651, 56414438311526652, 37837526245379668, 60771749981866956,
    32916459255411447, 34136805652688313, 37837526245379668, 37836720114702675, 32916459255411447, 41463430659690111,
    36820901554873553, 53414438479187584, 37837526245379668, 34136805652688313, 36820901554873553, 34136805652688313,
    37837538456017379, 37836720114702675, 50388001188379146, 52559004390228824, 12635944798803559, 57771715685807980,
    16612018959551099, 11557942286789136, 60771654961018698, 11557942286789136, 11557942286789136, 17978604352023330,
    11557942286789136, 16612018959551099, 17978604352023330, 55561254484866173, 11557942286789136, 11557942286789136,
    12635944798803559, 9884170522387776, 10621136113284685, 15556595861081553
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
noncomputable def negativeCeiling : ℝ := 330480104309 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1742723237372282391081517056, coefficient := (-1742723237372282391081517056) }, { argument := 14474284665953123192593711104, coefficient := (-14474284665953123192593711104) }, { argument := 74646645334112762417991647232, coefficient := (-74646645334112762417991647232) }, { argument := 33772404138942592012674662400, coefficient := (-33772404138942592012674662400) }, { argument := 1742723237372282391081517056, coefficient := (-1742723237372282391081517056) }, { argument := 1742723237372282391081517056, coefficient := (-1742723237372282391081517056) }, { argument := 1839541195004075857252712448, coefficient := (-1839541195004075857252712448) }, { argument := 236490137783819297390791229440, coefficient := (-236490137783819297390791229440) }, { argument := 827861026397983901643062640640, coefficient := (-827861026397983901643062640640) }, { argument := 236490135524093148361371156480, coefficient := (-236490135524093148361371156480) }, { argument := 235574418925514508832792903680, coefficient := (-235574418925514508832792903680) }, { argument := 14854844903120940963601647140864, coefficient := (-14854844903120940963601647140864) }, { argument := 53308583276033546305079869440, coefficient := (-53308583276033546305079869440) }, { argument := 60671202225320631716133470208, coefficient := (-60671202225320631716133470208) }, { argument := 927142727112954072765774692352, coefficient := (-927142727112954072765774692352) }, { argument := 1527862955008188049255997374464, coefficient := (-1527862955008188049255997374464) }, { argument := 14854845615650355339228553936896, coefficient := (-14854845615650355339228553936896) }, { argument := 927142727112954072765774692352, coefficient := (-927142727112954072765774692352) }, { argument := 53308583276033546305079869440, coefficient := (-53308583276033546305079869440) }, { argument := 52145803038183713775185559552, coefficient := (-52145803038183713775185559552) }, { argument := 51174749643606535902427348992, coefficient := (-51174749643606535902427348992) }, { argument := 52145803038183713775185559552, coefficient := (-52145803038183713775185559552) }, { argument := 1527862955008188049255997374464, coefficient := (-1527862955008188049255997374464) }, { argument := 51174749643606535902427348992, coefficient := (-51174749643606535902427348992) }, { argument := 235573706396100133205886107648, coefficient := (-235573706396100133205886107648) }, { argument := 60671202225320631716133470208, coefficient := (-60671202225320631716133470208) }, { argument := 408501252761414444477377937408, coefficient := (-408501252761414444477377937408) }, { argument := 54063966812913948063340362203136, coefficient := (-54063966812913948063340362203136) }, { argument := 1132635298709861411680520503296, coefficient := (-1132635298709861411680520503296) }, { argument := 554063352239393929738031137292288, coefficient := (-554063352239393929738031137292288) }, { argument := 598165414733727390906636566528, coefficient := (-598165414733727390906636566528) }, { argument := 43554415823799085690211270656, coefficient := (-43554415823799085690211270656) }, { argument := 1132635298709861411680520503296, coefficient := (-1132635298709861411680520503296) }, { argument := 1132002596048486536614789513216, coefficient := (-1132002596048486536614789513216) }, { argument := 598165414733727390906636566528, coefficient := (-598165414733727390906636566528) }, { argument := 13982862365217857469456159080448, coefficient := (-13982862365217857469456159080448) }, { argument := 1119658449740129148235331665920, coefficient := (-1119658449740129148235331665920) }, { argument := 54063973095888055207381759426560, coefficient := (-54063973095888055207381759426560) }, { argument := 1132635298709861411680520503296, coefficient := (-1132635298709861411680520503296) }, { argument := 43554415823799085690211270656, coefficient := (-43554415823799085690211270656) }, { argument := 1119658449740129148235331665920, coefficient := (-1119658449740129148235331665920) }, { argument := 43554415823799085690211270656, coefficient := (-43554415823799085690211270656) }, { argument := 1132644885113821637060304306176, coefficient := (-1132644885113821637060304306176) }, { argument := 1132002596048486536614789513216, coefficient := (-1132002596048486536614789513216) }, { argument := 414705286032943022075403042816, coefficient := (-414705286032943022075403042816) }, { argument := 14940551970809829573403852406784, coefficient := (-14940551970809829573403852406784) }, { argument := 60115725326930583570350080, coefficient := (-60115725326930583570350080) }, { argument := 554050181082038155491960296570880, coefficient := (-554050181082038155491960296570880) }, { argument := 473015838756638012829859840, coefficient := (-473015838756638012829859840) }, { argument := 56951739783407921277173760, coefficient := (-56951739783407921277173760) }, { argument := 554026860926892324684557684047872, coefficient := (-554026860926892324684557684047872) }, { argument := 56951739783407921277173760, coefficient := (-56951739783407921277173760) }, { argument := 56951739783407921277173760, coefficient := (-56951739783407921277173760) }, { argument := 2439432854055972628038942720, coefficient := (-2439432854055972628038942720) }, { argument := 56951739783407921277173760, coefficient := (-56951739783407921277173760) }, { argument := 473015838756638012829859840, coefficient := (-473015838756638012829859840) }, { argument := 2439432854055972628038942720, coefficient := (-2439432854055972628038942720) }, { argument := 14963872135072963639237410816000, coefficient := (-14963872135072963639237410816000) }, { argument := 56951739783407921277173760, coefficient := (-56951739783407921277173760) }, { argument := 56951739783407921277173760, coefficient := (-56951739783407921277173760) }, { argument := 60115725326930583570350080, coefficient := (-60115725326930583570350080) }, { argument := 71402181220989035631083520, coefficient := (-71402181220989035631083520) }, { argument := 1904058165893040950162227200, coefficient := (-1904058165893040950162227200) }, { argument := 1820755621135220408592629760, coefficient := (-1820755621135220408592629760) }] }

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

end TermShard3


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12
