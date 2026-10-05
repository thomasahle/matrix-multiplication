import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 17, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-117749496569823821855620835575857152)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    559133151, 123, 21864448389, 1287, 57, 10932225575,
    57, 111, 2097, 111, 1287, 2097,
    279568423, 111, 111, 123, 136625895046962833, 35,
    29, 500616017372451879, 195, 17076636613083561, 781, 781,
    559, 29, 136227802339155853, 136227798230163571, 35, 35,
    138687647, 29, 29, 123, 136625890856214895, 35,
    29, 500616000113535961, 195, 17076636089843287, 781, 781,
    559, 29, 62395050999892819, 62395048880813229, 21692670209, 195,
    195, 1287, 57, 136214994937218523, 136214990833023525, 21692672953,
    57, 781, 781, 111, 781, 781,
    2097, 111, 559, 559
  ]
def negativeCoefficients : Array ℕ := #[
    2640431651743692250585912836096, 2379166013001590215821754368, 103251938238646810389597067935744, 24894200477504443965549576192, 2205080694977083614664065024, 103251951277100669592687502950400,
    2205080694977083614664065024, 2147052255635581414278168576, 81123758199420076139483234304, 2147052255635581414278168576, 24894200477504443965549576192, 81123758199420076139483234304,
    2640449100887846453924977442816, 2147052255635581414278168576, 2147052255635581414278168576, 2379166013001590215821754368, 76913541252832788724122854096896, 5415987671873538702683668480,
    280470790150593968531832832, 281821763661784504289034133045248, 7543697114395286050166538240, 76906334287424494198032754016256, 7553368520952203083564187648, 7553368520952203083564187648,
    5406316265316621669286019072, 280470790150593968531832832, 76689434981515485365139339739136, 76689432668358471604708837425152, 5415987671873538702683668480, 5415987671873538702683668480,
    2619735583123427609649241653248, 280470790150593968531832832, 280470790150593968531832832, 2379166013001590215821754368, 76913538893651432226563544842240, 5415987671873538702683668480,
    280470790150593968531832832, 281821753945878592148593895800832, 7543697114395286050166538240, 76906331930959791186396527460352, 7553368520952203083564187648, 7553368520952203083564187648,
    5406316265316621669286019072, 280470790150593968531832832, 281002328432880393503634802868224, 281002318889394341611211361091584, 102440738718926461557542657982464, 7543697114395286050166538240,
    7543697114395286050166538240, 24894200477504443965549576192, 2205080694977083614664065024, 76682225055191417420568829362176, 76682222744735034464487132364800, 102440751677100090551849124364288,
    2205080694977083614664065024, 7553368520952203083564187648, 7553368520952203083564187648, 2147052255635581414278168576, 7553368520952203083564187648, 7553368520952203083564187648,
    81123758199420076139483234304, 2147052255635581414278168576, 5406316265316621669286019072, 5406316265316621669286019072
  ]
def negativeScales : Array ℕ := #[
    29, 6, 34, 10, 5, 33,
    5, 6, 11, 6, 10, 11,
    28, 6, 6, 6, 56, 5,
    4, 58, 7, 53, 9, 9,
    9, 4, 56, 56, 5, 5,
    27, 4, 4, 6, 56, 5,
    4, 58, 7, 53, 9, 9,
    9, 4, 55, 55, 34, 7,
    7, 10, 5, 56, 56, 34,
    5, 9, 9, 6, 9, 9,
    11, 6, 9, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    29058616643979234, 6942514514520450, 34347867900471676, 10329796338220703, 5832890015409720, 33347868082652387,
    5832890015409720, 6794415866926375, 11034111146096593, 6794415866926375, 10329796338220703, 11034111146096593,
    28058626177916817, 6794415866926375, 6794415866926375, 6942514514520450, 56923008566781804, 5129283016944967,
    4857980997143165, 58796482064948588, 7607330313756529, 53922873376782288, 9609178738149255, 9609178738149255,
    9126704472843191, 4857980997143165, 56918798788047798, 56918798744532279, 5129283016944967, 5129283016944967,
    27047264050686097, 4857980997143165, 4857980997143165, 6942514514520450, 56923008522529782, 5129283016944967,
    4857980997143165, 58796482015211160, 7607330313756529, 53922873332577081, 9609178738149255, 9609178738149255,
    9126704472843191, 4857980997143165, 55792281121858259, 55792281072861012, 34336488598019261, 7607330313756529,
    7607330313756529, 10329796338220703, 5832890015409720, 56918663147264256, 56918663103795455, 34336488780512006,
    5832890015409720, 9609178738149255, 9609178738149255, 6794415866926375, 9609178738149255, 9609178738149255,
    11034111146096593, 6794415866926375, 9126704472843191, 9126704472843191
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
noncomputable def negativeCeiling : ℝ := 681638424023 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2640431651743692250585912836096, coefficient := (-2640431651743692250585912836096) }, { argument := 2379166013001590215821754368, coefficient := (-2379166013001590215821754368) }, { argument := 103251938238646810389597067935744, coefficient := (-103251938238646810389597067935744) }, { argument := 24894200477504443965549576192, coefficient := (-24894200477504443965549576192) }, { argument := 2205080694977083614664065024, coefficient := (-2205080694977083614664065024) }, { argument := 103251951277100669592687502950400, coefficient := (-103251951277100669592687502950400) }, { argument := 2205080694977083614664065024, coefficient := (-2205080694977083614664065024) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 81123758199420076139483234304, coefficient := (-81123758199420076139483234304) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 24894200477504443965549576192, coefficient := (-24894200477504443965549576192) }, { argument := 81123758199420076139483234304, coefficient := (-81123758199420076139483234304) }, { argument := 2640449100887846453924977442816, coefficient := (-2640449100887846453924977442816) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 2379166013001590215821754368, coefficient := (-2379166013001590215821754368) }, { argument := 76913541252832788724122854096896, coefficient := (-76913541252832788724122854096896) }, { argument := 5415987671873538702683668480, coefficient := (-5415987671873538702683668480) }, { argument := 280470790150593968531832832, coefficient := (-280470790150593968531832832) }, { argument := 281821763661784504289034133045248, coefficient := (-281821763661784504289034133045248) }, { argument := 7543697114395286050166538240, coefficient := (-7543697114395286050166538240) }, { argument := 76906334287424494198032754016256, coefficient := (-76906334287424494198032754016256) }, { argument := 7553368520952203083564187648, coefficient := (-7553368520952203083564187648) }, { argument := 7553368520952203083564187648, coefficient := (-7553368520952203083564187648) }, { argument := 5406316265316621669286019072, coefficient := (-5406316265316621669286019072) }, { argument := 280470790150593968531832832, coefficient := (-280470790150593968531832832) }, { argument := 76689434981515485365139339739136, coefficient := (-76689434981515485365139339739136) }, { argument := 76689432668358471604708837425152, coefficient := (-76689432668358471604708837425152) }, { argument := 5415987671873538702683668480, coefficient := (-5415987671873538702683668480) }, { argument := 5415987671873538702683668480, coefficient := (-5415987671873538702683668480) }, { argument := 2619735583123427609649241653248, coefficient := (-2619735583123427609649241653248) }, { argument := 280470790150593968531832832, coefficient := (-280470790150593968531832832) }, { argument := 280470790150593968531832832, coefficient := (-280470790150593968531832832) }, { argument := 2379166013001590215821754368, coefficient := (-2379166013001590215821754368) }, { argument := 76913538893651432226563544842240, coefficient := (-76913538893651432226563544842240) }, { argument := 5415987671873538702683668480, coefficient := (-5415987671873538702683668480) }, { argument := 280470790150593968531832832, coefficient := (-280470790150593968531832832) }, { argument := 281821753945878592148593895800832, coefficient := (-281821753945878592148593895800832) }, { argument := 7543697114395286050166538240, coefficient := (-7543697114395286050166538240) }, { argument := 76906331930959791186396527460352, coefficient := (-76906331930959791186396527460352) }, { argument := 7553368520952203083564187648, coefficient := (-7553368520952203083564187648) }, { argument := 7553368520952203083564187648, coefficient := (-7553368520952203083564187648) }, { argument := 5406316265316621669286019072, coefficient := (-5406316265316621669286019072) }, { argument := 280470790150593968531832832, coefficient := (-280470790150593968531832832) }, { argument := 281002328432880393503634802868224, coefficient := (-281002328432880393503634802868224) }, { argument := 281002318889394341611211361091584, coefficient := (-281002318889394341611211361091584) }, { argument := 102440738718926461557542657982464, coefficient := (-102440738718926461557542657982464) }, { argument := 7543697114395286050166538240, coefficient := (-7543697114395286050166538240) }, { argument := 7543697114395286050166538240, coefficient := (-7543697114395286050166538240) }, { argument := 24894200477504443965549576192, coefficient := (-24894200477504443965549576192) }, { argument := 2205080694977083614664065024, coefficient := (-2205080694977083614664065024) }, { argument := 76682225055191417420568829362176, coefficient := (-76682225055191417420568829362176) }, { argument := 76682222744735034464487132364800, coefficient := (-76682222744735034464487132364800) }, { argument := 102440751677100090551849124364288, coefficient := (-102440751677100090551849124364288) }, { argument := 2205080694977083614664065024, coefficient := (-2205080694977083614664065024) }, { argument := 7553368520952203083564187648, coefficient := (-7553368520952203083564187648) }, { argument := 7553368520952203083564187648, coefficient := (-7553368520952203083564187648) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 7553368520952203083564187648, coefficient := (-7553368520952203083564187648) }, { argument := 7553368520952203083564187648, coefficient := (-7553368520952203083564187648) }, { argument := 81123758199420076139483234304, coefficient := (-81123758199420076139483234304) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 5406316265316621669286019072, coefficient := (-5406316265316621669286019072) }, { argument := 5406316265316621669286019072, coefficient := (-5406316265316621669286019072) }] }

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
def constantNumerator : ℤ := 114274308026315775320260323861069824
def positiveArguments : Array ℕ := #[
    27295, 27, 123, 3, 1287, 57,
    3, 57, 111, 2097, 111, 1287,
    2097, 27, 111, 111, 123, 7,
    35, 29, 521, 195, 7, 781,
    781, 559, 29, 5331, 46061847285, 46061845771,
    16263290117, 119180501323, 32523527339, 1112999003, 21778166083, 43556337671,
    139125795
  ]
def positiveCoefficients : Array ℕ := #[
    2162532695826845094615782124421120, 4178047632588158427784544256, 4758332026003180431643508736, 3713820117856140824697372672, 49788400955008887931099152384, 4410161389954167229328130048,
    3713820117856140824697372672, 4410161389954167229328130048, 4294104511271162828556337152, 162247516398840152278966468608, 4294104511271162828556337152, 49788400955008887931099152384,
    162247516398840152278966468608, 4178047632588158427784544256, 4294104511271162828556337152, 4294104511271162828556337152, 4758332026003180431643508736, 1083197534374707740536733696,
    21663950687494154810734673920, 1121883160602375874127331328, 20155211264615097600701366272, 30174788457581144200666152960, 1083197534374707740536733696, 30213474083808812334256750592,
    30213474083808812334256750592, 21625265061266486677144076288, 1121883160602375874127331328, 422365334363543183711182799241216, 870083695030976665581585369661440, 870083666432325245323013955518464,
    307204864598823803212794039369728, 1125628009718673216454873491439616, 307176030820776362561744706469888, 5255989187234531701807369945088, 205688963137455415806315028545536, 205688989134082904003711929942016,
    5256023929684746173787207106560
  ]
def positiveScales : Array ℕ := #[
    14, 4, 6, 1, 10, 5,
    1, 5, 6, 11, 6, 10,
    11, 4, 6, 6, 6, 2,
    5, 4, 9, 7, 2, 9,
    9, 9, 4, 12, 35, 35,
    33, 36, 34, 30, 34, 35,
    27
  ]
def negativeArguments : Array ℕ := #[
    1287, 2097, 277377125, 29, 29, 111,
    111, 123, 3, 1, 5331, 5491,
    10981, 5325
  ]
def negativeCoefficients : Array ℕ := #[
    24894200477504443965549576192, 81123758199420076139483234304, 2619752876429487878290014208000, 280470790150593968531832832, 280470790150593968531832832, 2147052255635581414278168576,
    2147052255635581414278168576, 2379166013001590215821754368, 475368975085586025561263702016, 158456325028528675187087900672, 422365334363543183711182799241216, 1740167361463301910904599325179904,
    1740008905138273382229412237279232, 421889965388457597685621535539200
  ]
def negativeScales : Array ℕ := #[
    10, 11, 28, 4, 4, 6,
    6, 6, 1, 0, 12, 12,
    13, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    14736349076623456, 4754887502147955, 6942514504772358, 1584962500720924, 10329796338220701, 5832890014087662,
    1584962500720924, 5832890014087662, 6794415866314396, 11034111146096592, 6794415866314396, 10329796338220701,
    11034111146096592, 4754887502147955, 6794415866314396, 6794415866314396, 6942514504772358, 2807354922011143,
    5129283016944966, 4857980995002857, 9025139562278508, 7607330313749179, 2807354922011143, 9609178738141526,
    9609178738141526, 9126704472843189, 4857980995002857, 12380190466749833, 35422853219654127, 35422853172234398,
    33920900097366880, 36794357264880585, 34920764681865986, 30051805154332261, 34342163420175572, 35342163602514978,
    27051814690614241
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    10329796338220703, 11034111146096593, 28047273574122244, 4857980997143165, 4857980997143165, 6794415866926375,
    6794415866926375, 6942514514520450, 1584962500724866, 0, 12380190466749838, 12422853195944281,
    13422721820900627, 12378565810000566
  ]

abbrev PositiveTerm := Fin 37
abbrev NegativeTerm := Fin 14
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
noncomputable def positiveFloor : ℝ := 2117829444839 / 1000000000000
noncomputable def negativeCeiling : ℝ := 668060394721 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 24894200477504443965549576192, coefficient := (-24894200477504443965549576192) }, { argument := 81123758199420076139483234304, coefficient := (-81123758199420076139483234304) }, { argument := 2619752876429487878290014208000, coefficient := (-2619752876429487878290014208000) }, { argument := 280470790150593968531832832, coefficient := (-280470790150593968531832832) }, { argument := 280470790150593968531832832, coefficient := (-280470790150593968531832832) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 2379166013001590215821754368, coefficient := (-2379166013001590215821754368) }, { argument := 2162532695826845094615782124421120, coefficient := 2162532695826845094615782124421120 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4758332026003180431643508736, coefficient := 4758332026003180431643508736 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 49788400955008887931099152384, coefficient := 49788400955008887931099152384 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 162247516398840152278966468608, coefficient := 162247516398840152278966468608 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 49788400955008887931099152384, coefficient := 49788400955008887931099152384 }, { argument := 162247516398840152278966468608, coefficient := 162247516398840152278966468608 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4758332026003180431643508736, coefficient := 4758332026003180431643508736 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 1083197534374707740536733696, coefficient := 1083197534374707740536733696 }, { argument := 21663950687494154810734673920, coefficient := 21663950687494154810734673920 }, { argument := 1121883160602375874127331328, coefficient := 1121883160602375874127331328 }, { argument := 20155211264615097600701366272, coefficient := 20155211264615097600701366272 }, { argument := 30174788457581144200666152960, coefficient := 30174788457581144200666152960 }, { argument := 1083197534374707740536733696, coefficient := 1083197534374707740536733696 }, { argument := 30213474083808812334256750592, coefficient := 30213474083808812334256750592 }, { argument := 30213474083808812334256750592, coefficient := 30213474083808812334256750592 }, { argument := 21625265061266486677144076288, coefficient := 21625265061266486677144076288 }, { argument := 1121883160602375874127331328, coefficient := 1121883160602375874127331328 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 422365334363543183711182799241216, coefficient := 422365334363543183711182799241216 }, { argument := 422365334363543183711182799241216, coefficient := (-422365334363543183711182799241216) }, { argument := 870083695030976665581585369661440, coefficient := 870083695030976665581585369661440 }, { argument := 870083666432325245323013955518464, coefficient := 870083666432325245323013955518464 }, { argument := 1740167361463301910904599325179904, coefficient := (-1740167361463301910904599325179904) }, { argument := 307204864598823803212794039369728, coefficient := 307204864598823803212794039369728 }, { argument := 1125628009718673216454873491439616, coefficient := 1125628009718673216454873491439616 }, { argument := 307176030820776362561744706469888, coefficient := 307176030820776362561744706469888 }, { argument := 1740008905138273382229412237279232, coefficient := (-1740008905138273382229412237279232) }, { argument := 5255989187234531701807369945088, coefficient := 5255989187234531701807369945088 }, { argument := 205688963137455415806315028545536, coefficient := 205688963137455415806315028545536 }, { argument := 205688989134082904003711929942016, coefficient := 205688989134082904003711929942016 }, { argument := 5256023929684746173787207106560, coefficient := 5256023929684746173787207106560 }, { argument := 421889965388457597685621535539200, coefficient := (-421889965388457597685621535539200) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17
