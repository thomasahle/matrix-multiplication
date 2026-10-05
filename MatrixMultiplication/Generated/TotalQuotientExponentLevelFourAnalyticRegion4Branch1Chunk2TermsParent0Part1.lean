import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 4, branch 1,
parent chunk 2, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk2

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 162426103154625303152029136322560
def positiveArguments : Array ℕ := #[
    5, 17, 17, 137, 19, 61,
    19, 17, 137, 61, 2405, 61,
    17, 17, 19, 61
  ]
def positiveCoefficients : Array ℕ := #[
    1584563250285286751870879006720, 657655645870358271040159744, 5261245166962866168321277952, 5299930793190534301911875584, 735026898325694538221355008, 4719646399775512298052911104,
    735026898325694538221355008, 5261245166962866168321277952, 5299930793190534301911875584, 4719646399775512298052911104, 93038931077541861285387304960, 4719646399775512298052911104,
    5261245166962866168321277952, 5261245166962866168321277952, 735026898325694538221355008, 4719646399775512298052911104
  ]
def positiveScales : Array ℕ := #[
    2, 4, 4, 7, 4, 5,
    4, 4, 7, 5, 11, 5,
    4, 4, 4, 5
  ]
def negativeArguments : Array ℕ := #[
    588914755, 14937131, 1232856875685, 4162807, 4652549, 14937131,
    4652549, 33547327, 33547327, 78683077311, 616043964755, 22172779253913,
    44344758503811, 1232856875685, 13244641961319, 42746760306873, 413075430351, 4162841,
    17305439, 17305439, 4162807, 4652587, 19341373, 19341373,
    4652549, 14937253, 62095987, 62095987, 14937131, 4652587,
    19341373, 19341373, 4652549, 33547601, 139461479, 139461479,
    33547327, 33547601, 139461479, 139461479, 33547327, 39326218029,
    1399819523415, 2799607016505, 78683077311, 221783399065, 715800534855, 6917006385
  ]
def negativeCoefficients : Array ℕ := #[
    678972485419772658193530880, 34442679094059153554931712, 694036720742014988813598720, 38395117678623318716973056, 5364023793337081291341824, 34442679094059153554931712,
    5364023793337081291341824, 38677434720377901942833152, 38677434720377901942833152, 22147317353636470525526016, 693603842528615242787717120, 24964330096422712778227187712,
    24963879734199731665640620032, 694036720742014988813598720, 7456070575206485462014230528, 24064286723666144005378277376, 7441305416818683494881296384, 38395431273272571779350528,
    1276916017264768596832157696, 1276916017264768596832157696, 38395117678623318716973056, 5364067604354256351526912, 178392678882577965733904384, 178392678882577965733904384,
    5364023793337081291341824, 34442960406906277625593856, 1145468780193395358922964992, 1145468780193395358922964992, 34442679094059153554931712, 5364067604354256351526912,
    178392678882577965733904384, 178392678882577965733904384, 5364023793337081291341824, 38677750620870164218904576, 1286305105627009542397100032, 1286305105627009542397100032,
    38677434720377901942833152, 38677750620870164218904576, 1286305105627009542397100032, 1286305105627009542397100032, 38677434720377901942833152, 22138692607661910207234048,
    788028335504717412544020480, 788019319769734002801377280, 22147317353636470525526016, 124852954173262001371873280, 402959877755572466755829760, 124605709512021366370467840
  ]
def negativeScales : Array ℕ := #[
    29, 23, 40, 21, 22, 23,
    22, 24, 24, 36, 39, 44,
    45, 40, 43, 45, 38, 21,
    24, 24, 21, 22, 24, 24,
    22, 23, 25, 25, 23, 22,
    24, 24, 22, 24, 27, 27,
    24, 24, 27, 27, 24, 35,
    40, 41, 36, 37, 39, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 4087462841250339, 4087462841250339, 7098032082960526, 4247927513443585, 5930737337099561,
    4247927513443585, 4087462841250339, 7098032082960526, 5930737337099561, 11231821178657404, 5930737337099561,
    4087462841250339, 4087462841250339, 4247927513443585, 5930737337099561
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    29133483579166266, 23832399739304867, 40165142463348883, 21989125261645347, 22149589913952447, 23832399739304867,
    22149589913952447, 24999694507030712, 24999694507030712, 36195334331687075, 39164242358107557, 44333854850133980,
    45333828823350808, 40165142463348883, 43590474077805436, 45280880318649655, 38587614295280917, 21989137044907655,
    24044722204102048, 24044722204102048, 21989125261645347, 22149601697210973, 24205186876295294, 24205186876295294,
    22149589913952447, 23832411522563677, 25887996703930951, 25887996703930951, 23832399739304867, 22149601697210973,
    24205186876295294, 24205186876295294, 22149589913952447, 24999706290293667, 27055291445812235, 27055291445812235,
    24999694507030712, 24999706290293667, 27055291445812235, 27055291445812235, 24999694507030712, 35194772398994805,
    40348377973348463, 41348361467558036, 36195334331687075, 37690360424724289, 39380766665515241, 32687500642196297
  ]

abbrev PositiveTerm := Fin 16
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
noncomputable def positiveFloor : ℝ := 3014993 / 50000000000
noncomputable def negativeCeiling : ℝ := 53250879 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 678972485419772658193530880, coefficient := (-678972485419772658193530880) }, { argument := 34442679094059153554931712, coefficient := (-34442679094059153554931712) }, { argument := 694036720742014988813598720, coefficient := (-694036720742014988813598720) }, { argument := 38395117678623318716973056, coefficient := (-38395117678623318716973056) }, { argument := 5364023793337081291341824, coefficient := (-5364023793337081291341824) }, { argument := 34442679094059153554931712, coefficient := (-34442679094059153554931712) }, { argument := 5364023793337081291341824, coefficient := (-5364023793337081291341824) }, { argument := 38677434720377901942833152, coefficient := (-38677434720377901942833152) }, { argument := 38677434720377901942833152, coefficient := (-38677434720377901942833152) }, { argument := 22147317353636470525526016, coefficient := (-22147317353636470525526016) }, { argument := 693603842528615242787717120, coefficient := (-693603842528615242787717120) }, { argument := 24964330096422712778227187712, coefficient := (-24964330096422712778227187712) }, { argument := 24963879734199731665640620032, coefficient := (-24963879734199731665640620032) }, { argument := 694036720742014988813598720, coefficient := (-694036720742014988813598720) }, { argument := 7456070575206485462014230528, coefficient := (-7456070575206485462014230528) }, { argument := 24064286723666144005378277376, coefficient := (-24064286723666144005378277376) }, { argument := 7441305416818683494881296384, coefficient := (-7441305416818683494881296384) }, { argument := 38395431273272571779350528, coefficient := (-38395431273272571779350528) }, { argument := 1276916017264768596832157696, coefficient := (-1276916017264768596832157696) }, { argument := 1276916017264768596832157696, coefficient := (-1276916017264768596832157696) }, { argument := 38395117678623318716973056, coefficient := (-38395117678623318716973056) }, { argument := 5364067604354256351526912, coefficient := (-5364067604354256351526912) }, { argument := 178392678882577965733904384, coefficient := (-178392678882577965733904384) }, { argument := 178392678882577965733904384, coefficient := (-178392678882577965733904384) }, { argument := 5364023793337081291341824, coefficient := (-5364023793337081291341824) }, { argument := 34442960406906277625593856, coefficient := (-34442960406906277625593856) }, { argument := 1145468780193395358922964992, coefficient := (-1145468780193395358922964992) }, { argument := 1145468780193395358922964992, coefficient := (-1145468780193395358922964992) }, { argument := 34442679094059153554931712, coefficient := (-34442679094059153554931712) }, { argument := 5364067604354256351526912, coefficient := (-5364067604354256351526912) }, { argument := 178392678882577965733904384, coefficient := (-178392678882577965733904384) }, { argument := 178392678882577965733904384, coefficient := (-178392678882577965733904384) }, { argument := 5364023793337081291341824, coefficient := (-5364023793337081291341824) }, { argument := 38677750620870164218904576, coefficient := (-38677750620870164218904576) }, { argument := 1286305105627009542397100032, coefficient := (-1286305105627009542397100032) }, { argument := 1286305105627009542397100032, coefficient := (-1286305105627009542397100032) }, { argument := 38677434720377901942833152, coefficient := (-38677434720377901942833152) }, { argument := 38677750620870164218904576, coefficient := (-38677750620870164218904576) }, { argument := 1286305105627009542397100032, coefficient := (-1286305105627009542397100032) }, { argument := 1286305105627009542397100032, coefficient := (-1286305105627009542397100032) }, { argument := 38677434720377901942833152, coefficient := (-38677434720377901942833152) }, { argument := 22138692607661910207234048, coefficient := (-22138692607661910207234048) }, { argument := 788028335504717412544020480, coefficient := (-788028335504717412544020480) }, { argument := 788019319769734002801377280, coefficient := (-788019319769734002801377280) }, { argument := 22147317353636470525526016, coefficient := (-22147317353636470525526016) }, { argument := 124852954173262001371873280, coefficient := (-124852954173262001371873280) }, { argument := 402959877755572466755829760, coefficient := (-402959877755572466755829760) }, { argument := 124605709512021366370467840, coefficient := (-124605709512021366370467840) }, { argument := 1584563250285286751870879006720, coefficient := 1584563250285286751870879006720 }, { argument := 657655645870358271040159744, coefficient := 657655645870358271040159744 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 5299930793190534301911875584, coefficient := 5299930793190534301911875584 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 4719646399775512298052911104, coefficient := 4719646399775512298052911104 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 5299930793190534301911875584, coefficient := 5299930793190534301911875584 }, { argument := 4719646399775512298052911104, coefficient := 4719646399775512298052911104 }, { argument := 93038931077541861285387304960, coefficient := 93038931077541861285387304960 }, { argument := 4719646399775512298052911104, coefficient := 4719646399775512298052911104 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 4719646399775512298052911104, coefficient := 4719646399775512298052911104 }] }

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


end Parent0

namespace Parent0

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-89835644999007063436377821544448)
def positiveArguments : Array ℕ := #[
    19, 137, 137, 9, 1605323, 5181141,
    50067, 1025805, 73445887, 73444627, 513205, 33681,
    5154751, 113059889, 5154749, 269391, 140893, 8247715,
    8250453, 138155
  ]
def positiveCoefficients : Array ℕ := #[
    735026898325694538221355008, 5299930793190534301911875584, 5299930793190534301911875584, 696341272098026404630757376, 30323694117518989853544415232, 97868986405686865888536428544,
    30263644505322819445007056896, 19376908599840385633741701120, 693676790146862796190414536704, 693664889783325964684476022784, 19388336726728930175158845440, 2544864408152520327079919616,
    97370493399755146139778678784, 1067820460741124978659702079488, 97370455620823283182616969216, 2544326058373473187525558272, 1330696761741905846186541056, 77897465752522431747357409280,
    77923325431382625924547608576, 1304837082881711668996341760
  ]
def positiveScales : Array ℕ := #[
    4, 7, 7, 3, 20, 22,
    15, 19, 26, 26, 18, 15,
    22, 26, 22, 18, 17, 22,
    22, 17
  ]
def negativeArguments : Array ℕ := #[
    1, 1, 9, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    158456325028528675187087900672, 158456325028528675187087900672, 1426106925256758076683791106048, 1267650600228229401496703205376, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 0, 3, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    4247927513443585, 7098032082960526, 7098032082960526, 3169925001442312, 20614432174219585, 22304838415068661,
    15611572391695441, 19968325076909706, 26130178365737164, 26130153615388049, 18969175699785339, 15039647352681300,
    22297471309285867, 26752511944780897, 22297470749532226, 18039342127492933, 17104240410313222, 22975563049544053,
    22976041902589359, 17075928250446576
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0, 3169925001442313, 0, 0
  ]

abbrev PositiveTerm := Fin 20
abbrev NegativeTerm := Fin 5
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
noncomputable def positiveFloor : ℝ := 926681581 / 1000000000000
noncomputable def negativeCeiling : ℝ := 5441537 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 5299930793190534301911875584, coefficient := 5299930793190534301911875584 }, { argument := 5299930793190534301911875584, coefficient := 5299930793190534301911875584 }, { argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 30323694117518989853544415232, coefficient := 30323694117518989853544415232 }, { argument := 97868986405686865888536428544, coefficient := 97868986405686865888536428544 }, { argument := 30263644505322819445007056896, coefficient := 30263644505322819445007056896 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 19376908599840385633741701120, coefficient := 19376908599840385633741701120 }, { argument := 693676790146862796190414536704, coefficient := 693676790146862796190414536704 }, { argument := 693664889783325964684476022784, coefficient := 693664889783325964684476022784 }, { argument := 19388336726728930175158845440, coefficient := 19388336726728930175158845440 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 2544864408152520327079919616, coefficient := 2544864408152520327079919616 }, { argument := 97370493399755146139778678784, coefficient := 97370493399755146139778678784 }, { argument := 1067820460741124978659702079488, coefficient := 1067820460741124978659702079488 }, { argument := 97370455620823283182616969216, coefficient := 97370455620823283182616969216 }, { argument := 2544326058373473187525558272, coefficient := 2544326058373473187525558272 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 1330696761741905846186541056, coefficient := 1330696761741905846186541056 }, { argument := 77897465752522431747357409280, coefficient := 77897465752522431747357409280 }, { argument := 77923325431382625924547608576, coefficient := 77923325431382625924547608576 }, { argument := 1304837082881711668996341760, coefficient := 1304837082881711668996341760 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk2
