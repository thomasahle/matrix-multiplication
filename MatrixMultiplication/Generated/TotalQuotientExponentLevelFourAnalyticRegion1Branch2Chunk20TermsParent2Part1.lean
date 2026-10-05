import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 20, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk20

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-873300760475121616494278681296896)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    133231365, 281266215, 12438307, 1985740799, 79258828061, 1985740799,
    49747551, 938208479, 34646790945, 277174259687, 7505735705, 8442636657,
    653751903, 36727635, 33804016799, 1985740799, 2110658487, 1985740799,
    1985740799, 653751903, 36727635, 28240389, 1042879995, 8343037917,
    225925155, 35311534167, 126324682029, 8827880607, 401295879, 26667513,
    401295879, 26667513, 486888825, 2110658487, 8827880607, 27452739,
    291029031, 679067739, 8827880607, 8827880607, 291029031, 108941867271,
    4365435465, 2110658487, 8827880607, 679067739, 4365435465, 679067739,
    8827880607, 8827880607, 145974573, 3880688041, 2250129169, 3397399387,
    35409927449, 1065850659, 54358383609, 1065850659, 1065850659, 91307873121,
    1065850659, 35409927449, 91307873121, 31045510911
  ]
def negativeCoefficients : Array ℕ := #[
    78645916567871493610804346880, 83015134154975465478071255040, 229446265939230031832154112, 36630452315876519919887581184, 365516829205854015496487174144, 36630452315876519919887581184,
    229420085397703419551023104, 17306891699897302309419352064, 639120485537732505489238917120, 639120329033249941128189313024, 17307048204379866670468956160, 38934789429749442611068796928,
    24119188084683183276473450496, 1355010566555235015532216320, 155893511638632844268505399296, 36630452315876519919887581184, 38934776936692018691274964992, 36630452315876519919887581184,
    36630452315876519919887581184, 24119188084683183276473450496, 1355010566555235015532216320, 2083772913700009642605674496, 76950961469425987282985287680, 76950942626076915988678311936,
    2083791757049080936912650240, 81422854203587449790329257984, 291284884947712405798920388608, 81422827135296364630775955456, 1850650594436828826609647616, 122982196848330606485962752,
    1850650594436828826609647616, 122982196848330606485962752, 2245378386781039244397772800, 38934776936692018691274964992, 81422827135296364630775955456, 16205236814571042634274439168,
    42948304423013467057991712768, 3131647197511398639645229056, 81422827135296364630775955456, 81422827135296364630775955456, 42948304423013467057991712768, 1004811372230085906377597779968,
    80528070793150250733734461440, 38934776936692018691274964992, 81422827135296364630775955456, 3131647197511398639645229056, 80528070793150250733734461440, 3131647197511398639645229056,
    81422827135296364630775955456, 81422827135296364630775955456, 2692755589400032323167059968, 71586059122232279463683424256, 83015113826663496250145374208, 125341914016333426952486518784,
    653197869320325931020880707584, 78645897309470680658032459776, 125341898836968897298739232768, 78645897309470680658032459776, 78645897309470680658032459776, 3368665934755660821519057027072,
    78645897309470680658032459776, 653197869320325931020880707584, 3368665934755660821519057027072, 71586074301596809117430710272
  ]
def negativeScales : Array ℕ := #[
    26, 28, 23, 30, 36, 30,
    25, 29, 35, 38, 32, 32,
    29, 25, 34, 30, 30, 30,
    30, 29, 25, 24, 29, 32,
    27, 35, 36, 33, 28, 24,
    28, 24, 28, 30, 33, 24,
    28, 29, 33, 33, 28, 36,
    32, 30, 33, 29, 32, 29,
    33, 33, 27, 31, 31, 31,
    35, 29, 35, 29, 29, 36,
    29, 35, 36, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    26989358537168946, 28067361029209065, 23568286795267393, 30887030175976171, 36205852584321290, 30887030175976171,
    25568122169827494, 29805333298977177, 35012002682126927, 38012002328847266, 32805346345064666, 32975046496450796,
    29284167999991430, 25130362663912394, 34976475651561316, 30887030175976171, 30975046033531134, 30887030175976171,
    30887030175976171, 29284167999991430, 25130362663912394, 24751256625732562, 29957926021280624, 32957925668000893,
    27751269671819927, 35039420451563919, 36878345595270461, 33039419971952928, 28580091099927759, 24668579950331610,
    28580091099927759, 24668579950331610, 28859017149619032, 30975046033531134, 33039419971952928, 24710446760513799,
    28116587832475388, 29338980253811836, 33039419971952928, 33039419971952928, 28116587832475388, 36664767544185719,
    32023478428083907, 30975046033531134, 33039419971952928, 29338980253811836, 32023478428083907, 29338980253811836,
    33039419971952928, 33039419971952928, 27121141850111579, 31853665318909905, 31067360675929404, 31661783680643960,
    35043434836683923, 29989358183889172, 35661783505928300, 29989358183889172, 29989358183889172, 36410020212400863,
    29989358183889172, 35043434836683923, 36410020212400863, 34853665624824110
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
noncomputable def negativeCeiling : ℝ := 5801568291 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 78645916567871493610804346880, coefficient := (-78645916567871493610804346880) }, { argument := 83015134154975465478071255040, coefficient := (-83015134154975465478071255040) }, { argument := 229446265939230031832154112, coefficient := (-229446265939230031832154112) }, { argument := 36630452315876519919887581184, coefficient := (-36630452315876519919887581184) }, { argument := 365516829205854015496487174144, coefficient := (-365516829205854015496487174144) }, { argument := 36630452315876519919887581184, coefficient := (-36630452315876519919887581184) }, { argument := 229420085397703419551023104, coefficient := (-229420085397703419551023104) }, { argument := 17306891699897302309419352064, coefficient := (-17306891699897302309419352064) }, { argument := 639120485537732505489238917120, coefficient := (-639120485537732505489238917120) }, { argument := 639120329033249941128189313024, coefficient := (-639120329033249941128189313024) }, { argument := 17307048204379866670468956160, coefficient := (-17307048204379866670468956160) }, { argument := 38934789429749442611068796928, coefficient := (-38934789429749442611068796928) }, { argument := 24119188084683183276473450496, coefficient := (-24119188084683183276473450496) }, { argument := 1355010566555235015532216320, coefficient := (-1355010566555235015532216320) }, { argument := 155893511638632844268505399296, coefficient := (-155893511638632844268505399296) }, { argument := 36630452315876519919887581184, coefficient := (-36630452315876519919887581184) }, { argument := 38934776936692018691274964992, coefficient := (-38934776936692018691274964992) }, { argument := 36630452315876519919887581184, coefficient := (-36630452315876519919887581184) }, { argument := 36630452315876519919887581184, coefficient := (-36630452315876519919887581184) }, { argument := 24119188084683183276473450496, coefficient := (-24119188084683183276473450496) }, { argument := 1355010566555235015532216320, coefficient := (-1355010566555235015532216320) }, { argument := 2083772913700009642605674496, coefficient := (-2083772913700009642605674496) }, { argument := 76950961469425987282985287680, coefficient := (-76950961469425987282985287680) }, { argument := 76950942626076915988678311936, coefficient := (-76950942626076915988678311936) }, { argument := 2083791757049080936912650240, coefficient := (-2083791757049080936912650240) }, { argument := 81422854203587449790329257984, coefficient := (-81422854203587449790329257984) }, { argument := 291284884947712405798920388608, coefficient := (-291284884947712405798920388608) }, { argument := 81422827135296364630775955456, coefficient := (-81422827135296364630775955456) }, { argument := 1850650594436828826609647616, coefficient := (-1850650594436828826609647616) }, { argument := 122982196848330606485962752, coefficient := (-122982196848330606485962752) }, { argument := 1850650594436828826609647616, coefficient := (-1850650594436828826609647616) }, { argument := 122982196848330606485962752, coefficient := (-122982196848330606485962752) }, { argument := 2245378386781039244397772800, coefficient := (-2245378386781039244397772800) }, { argument := 38934776936692018691274964992, coefficient := (-38934776936692018691274964992) }, { argument := 81422827135296364630775955456, coefficient := (-81422827135296364630775955456) }, { argument := 16205236814571042634274439168, coefficient := (-16205236814571042634274439168) }, { argument := 42948304423013467057991712768, coefficient := (-42948304423013467057991712768) }, { argument := 3131647197511398639645229056, coefficient := (-3131647197511398639645229056) }, { argument := 81422827135296364630775955456, coefficient := (-81422827135296364630775955456) }, { argument := 81422827135296364630775955456, coefficient := (-81422827135296364630775955456) }, { argument := 42948304423013467057991712768, coefficient := (-42948304423013467057991712768) }, { argument := 1004811372230085906377597779968, coefficient := (-1004811372230085906377597779968) }, { argument := 80528070793150250733734461440, coefficient := (-80528070793150250733734461440) }, { argument := 38934776936692018691274964992, coefficient := (-38934776936692018691274964992) }, { argument := 81422827135296364630775955456, coefficient := (-81422827135296364630775955456) }, { argument := 3131647197511398639645229056, coefficient := (-3131647197511398639645229056) }, { argument := 80528070793150250733734461440, coefficient := (-80528070793150250733734461440) }, { argument := 3131647197511398639645229056, coefficient := (-3131647197511398639645229056) }, { argument := 81422827135296364630775955456, coefficient := (-81422827135296364630775955456) }, { argument := 81422827135296364630775955456, coefficient := (-81422827135296364630775955456) }, { argument := 2692755589400032323167059968, coefficient := (-2692755589400032323167059968) }, { argument := 71586059122232279463683424256, coefficient := (-71586059122232279463683424256) }, { argument := 83015113826663496250145374208, coefficient := (-83015113826663496250145374208) }, { argument := 125341914016333426952486518784, coefficient := (-125341914016333426952486518784) }, { argument := 653197869320325931020880707584, coefficient := (-653197869320325931020880707584) }, { argument := 78645897309470680658032459776, coefficient := (-78645897309470680658032459776) }, { argument := 125341898836968897298739232768, coefficient := (-125341898836968897298739232768) }, { argument := 78645897309470680658032459776, coefficient := (-78645897309470680658032459776) }, { argument := 78645897309470680658032459776, coefficient := (-78645897309470680658032459776) }, { argument := 3368665934755660821519057027072, coefficient := (-3368665934755660821519057027072) }, { argument := 78645897309470680658032459776, coefficient := (-78645897309470680658032459776) }, { argument := 653197869320325931020880707584, coefficient := (-653197869320325931020880707584) }, { argument := 3368665934755660821519057027072, coefficient := (-3368665934755660821519057027072) }, { argument := 71586074301596809117430710272, coefficient := (-71586074301596809117430710272) }] }

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


end Parent2

namespace Parent2

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-723759208640136071459086501150720)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1065850659, 1065850659, 2250129169, 7027901571, 26093843517, 1465946265,
    97007813407, 79258828061, 27452739, 79258828061, 79258828061, 26093843517,
    1465946265, 28240389, 1042879995, 8343037917, 225925155, 1164116511,
    4164549957, 291029031, 2295641593, 2242450951, 2295641593, 2242450951,
    2716271859, 9717283233, 679067739, 5, 5, 26667513,
    2242450951, 1121225205, 13334027, 12438307, 1985740799, 79258828061,
    1985740799, 49747551, 28240389, 1042879995, 8343037917, 225925155,
    12438307, 1985740799, 79258828061, 1985740799, 49747551, 2419259991,
    89340052905, 714720248223, 19354254945, 35311534167, 126324682029, 8827880607,
    28240389, 1042879995, 8343037917, 225925155, 35311534167, 126324682029,
    8827880607, 47, 47, 4094979
  ]
def negativeCoefficients : Array ℕ := #[
    78645897309470680658032459776, 78645897309470680658032459776, 83015113826663496250145374208, 16205237706932287199973998592, 240673226628762076788069236736, 13520967788132700943149957120,
    223684788383637404684820414464, 365516829205854015496487174144, 16205236814571042634274439168, 365516829205854015496487174144, 365516829205854015496487174144, 240673226628762076788069236736,
    13520967788132700943149957120, 2083772913700009642605674496, 76950961469425987282985287680, 76950942626076915988678311936, 2083791757049080936912650240, 42948318700793380109184663552,
    153644774477914236025804161024, 42948304423013467057991712768, 10586778237758476122767491072, 10341479697735899529770696704, 10586778237758476122767491072, 10341479697735899529770696704,
    3131648238599517299628048384, 11203264805681246376881553408, 3131647197511398639645229056, 1547425049106725343623905280, 1547425049106725343623905280, 122982196848330606485962752,
    10341479697735899529770696704, 10341477202813763560553840640, 122984691770466575702818816, 229446265939230031832154112, 36630452315876519919887581184, 365516829205854015496487174144,
    36630452315876519919887581184, 229420085397703419551023104, 2083772913700009642605674496, 76950961469425987282985287680, 76950942626076915988678311936, 2083791757049080936912650240,
    229446265939230031832154112, 36630452315876519919887581184, 365516829205854015496487174144, 36630452315876519919887581184, 229420085397703419551023104, 89254939803483746358276390912,
    3296066182940413121954536488960, 3296065375816961234848387694592, 89255746926935633464425185280, 81422854203587449790329257984, 291284884947712405798920388608, 81422827135296364630775955456,
    2083772913700009642605674496, 76950961469425987282985287680, 76950942626076915988678311936, 2083791757049080936912650240, 81422854203587449790329257984, 291284884947712405798920388608,
    81422827135296364630775955456, 1818224432700402278758088704, 1818224432700402278758088704, 151078059200430131933872128
  ]
def negativeScales : Array ℕ := #[
    29, 29, 31, 32, 34, 30,
    36, 36, 24, 36, 36, 34,
    30, 24, 29, 32, 27, 30,
    31, 28, 31, 31, 31, 31,
    31, 33, 29, 2, 2, 24,
    31, 30, 23, 23, 30, 36,
    30, 25, 24, 29, 32, 27,
    23, 30, 36, 30, 25, 31,
    36, 39, 34, 35, 36, 33,
    24, 29, 32, 27, 35, 36,
    33, 5, 5, 21
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    29989358183889172, 29989358183889172, 31067360675929404, 32710446839957569, 34602990411797712, 30449185075712581,
    36497381901426812, 36205852584321290, 24710446760513799, 36205852584321290, 36205852584321290, 34602990411797712,
    30449185075712581, 24751256625732562, 29957926021280624, 32957925668000893, 27751269671819927, 30116588312086379,
    31955513464283695, 28116587832475388, 31096250272845094, 31062429283490687, 31096250272845094, 31062429283490687,
    31338980733422828, 33177905874182432, 29338980253811836, 2321928094887363, 2321928094887363, 24668579950331610,
    31062429283490687, 30062428935434864, 23668609217781520, 23568286795267393, 30887030175976171, 36205852584321290,
    30887030175976171, 25568122169827494, 24751256625732562, 29957926021280624, 32957925668000893, 27751269671819927,
    23568286795267393, 30887030175976171, 36205852584321290, 30887030175976171, 25568122169827494, 31171918673974148,
    36378588057843859, 39378587704564198, 34171931720061447, 35039420451563919, 36878345595270461, 33039419971952928,
    24751256625732562, 29957926021280624, 32957925668000893, 27751269671819927, 35039420451563919, 36878345595270461,
    33039419971952928, 5554588851679165, 5554588851679165, 21965424636229379
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
noncomputable def negativeCeiling : ℝ := 5025300037 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 78645897309470680658032459776, coefficient := (-78645897309470680658032459776) }, { argument := 78645897309470680658032459776, coefficient := (-78645897309470680658032459776) }, { argument := 83015113826663496250145374208, coefficient := (-83015113826663496250145374208) }, { argument := 16205237706932287199973998592, coefficient := (-16205237706932287199973998592) }, { argument := 240673226628762076788069236736, coefficient := (-240673226628762076788069236736) }, { argument := 13520967788132700943149957120, coefficient := (-13520967788132700943149957120) }, { argument := 223684788383637404684820414464, coefficient := (-223684788383637404684820414464) }, { argument := 365516829205854015496487174144, coefficient := (-365516829205854015496487174144) }, { argument := 16205236814571042634274439168, coefficient := (-16205236814571042634274439168) }, { argument := 365516829205854015496487174144, coefficient := (-365516829205854015496487174144) }, { argument := 365516829205854015496487174144, coefficient := (-365516829205854015496487174144) }, { argument := 240673226628762076788069236736, coefficient := (-240673226628762076788069236736) }, { argument := 13520967788132700943149957120, coefficient := (-13520967788132700943149957120) }, { argument := 2083772913700009642605674496, coefficient := (-2083772913700009642605674496) }, { argument := 76950961469425987282985287680, coefficient := (-76950961469425987282985287680) }, { argument := 76950942626076915988678311936, coefficient := (-76950942626076915988678311936) }, { argument := 2083791757049080936912650240, coefficient := (-2083791757049080936912650240) }, { argument := 42948318700793380109184663552, coefficient := (-42948318700793380109184663552) }, { argument := 153644774477914236025804161024, coefficient := (-153644774477914236025804161024) }, { argument := 42948304423013467057991712768, coefficient := (-42948304423013467057991712768) }, { argument := 10586778237758476122767491072, coefficient := (-10586778237758476122767491072) }, { argument := 10341479697735899529770696704, coefficient := (-10341479697735899529770696704) }, { argument := 10586778237758476122767491072, coefficient := (-10586778237758476122767491072) }, { argument := 10341479697735899529770696704, coefficient := (-10341479697735899529770696704) }, { argument := 3131648238599517299628048384, coefficient := (-3131648238599517299628048384) }, { argument := 11203264805681246376881553408, coefficient := (-11203264805681246376881553408) }, { argument := 3131647197511398639645229056, coefficient := (-3131647197511398639645229056) }, { argument := 1547425049106725343623905280, coefficient := (-1547425049106725343623905280) }, { argument := 1547425049106725343623905280, coefficient := (-1547425049106725343623905280) }, { argument := 122982196848330606485962752, coefficient := (-122982196848330606485962752) }, { argument := 10341479697735899529770696704, coefficient := (-10341479697735899529770696704) }, { argument := 10341477202813763560553840640, coefficient := (-10341477202813763560553840640) }, { argument := 122984691770466575702818816, coefficient := (-122984691770466575702818816) }, { argument := 229446265939230031832154112, coefficient := (-229446265939230031832154112) }, { argument := 36630452315876519919887581184, coefficient := (-36630452315876519919887581184) }, { argument := 365516829205854015496487174144, coefficient := (-365516829205854015496487174144) }, { argument := 36630452315876519919887581184, coefficient := (-36630452315876519919887581184) }, { argument := 229420085397703419551023104, coefficient := (-229420085397703419551023104) }, { argument := 2083772913700009642605674496, coefficient := (-2083772913700009642605674496) }, { argument := 76950961469425987282985287680, coefficient := (-76950961469425987282985287680) }, { argument := 76950942626076915988678311936, coefficient := (-76950942626076915988678311936) }, { argument := 2083791757049080936912650240, coefficient := (-2083791757049080936912650240) }, { argument := 229446265939230031832154112, coefficient := (-229446265939230031832154112) }, { argument := 36630452315876519919887581184, coefficient := (-36630452315876519919887581184) }, { argument := 365516829205854015496487174144, coefficient := (-365516829205854015496487174144) }, { argument := 36630452315876519919887581184, coefficient := (-36630452315876519919887581184) }, { argument := 229420085397703419551023104, coefficient := (-229420085397703419551023104) }, { argument := 89254939803483746358276390912, coefficient := (-89254939803483746358276390912) }, { argument := 3296066182940413121954536488960, coefficient := (-3296066182940413121954536488960) }, { argument := 3296065375816961234848387694592, coefficient := (-3296065375816961234848387694592) }, { argument := 89255746926935633464425185280, coefficient := (-89255746926935633464425185280) }, { argument := 81422854203587449790329257984, coefficient := (-81422854203587449790329257984) }, { argument := 291284884947712405798920388608, coefficient := (-291284884947712405798920388608) }, { argument := 81422827135296364630775955456, coefficient := (-81422827135296364630775955456) }, { argument := 2083772913700009642605674496, coefficient := (-2083772913700009642605674496) }, { argument := 76950961469425987282985287680, coefficient := (-76950961469425987282985287680) }, { argument := 76950942626076915988678311936, coefficient := (-76950942626076915988678311936) }, { argument := 2083791757049080936912650240, coefficient := (-2083791757049080936912650240) }, { argument := 81422854203587449790329257984, coefficient := (-81422854203587449790329257984) }, { argument := 291284884947712405798920388608, coefficient := (-291284884947712405798920388608) }, { argument := 81422827135296364630775955456, coefficient := (-81422827135296364630775955456) }, { argument := 1818224432700402278758088704, coefficient := (-1818224432700402278758088704) }, { argument := 1818224432700402278758088704, coefficient := (-1818224432700402278758088704) }, { argument := 151078059200430131933872128, coefficient := (-151078059200430131933872128) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk20
