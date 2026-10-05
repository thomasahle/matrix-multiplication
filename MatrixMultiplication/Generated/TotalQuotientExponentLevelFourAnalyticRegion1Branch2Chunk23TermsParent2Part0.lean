import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 23, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk23

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-399055643521710926488082969526272)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    864085, 57, 28683435, 897, 27, 14341021,
    27, 27, 2313, 27, 897, 2313,
    432739, 27, 27, 57, 4627828651, 1869,
    105, 8995533397, 5677, 4627827627, 5677, 5677,
    1869, 105, 4627828651, 1610098773, 4627828651, 1610098773,
    1610098773, 2928138155, 1610098773, 1869, 1869, 202429,
    105, 105, 57, 4627828651, 1869, 105,
    8995533397, 5677, 4627827627, 5677, 5677, 1869,
    105, 8995533397, 2928138155, 8995533397, 2928138155, 6660163,
    5677, 5677, 897, 27, 4627827627, 1610098773,
    4627827627, 1610098773, 53278827, 27
  ]
def negativeCoefficients : Array ℕ := #[
    16322104169401669537906032640, 2205080694977083614664065024, 541814768230280327840441303040, 17350503363109157915383037952, 2089023816294079213892272128, 541788455204237778177310588928,
    2089023816294079213892272128, 2089023816294079213892272128, 89479853464596392995052322816, 2089023816294079213892272128, 17350503363109157915383037952, 89479853464596392995052322816,
    16348417195444219201036746752, 2089023816294079213892272128, 2089023816294079213892272128, 2205080694977083614664065024, 85368370741977518820888150016, 36151717709755870840413487104,
    2030995376952577013506375680, 331876604761932202479246639104, 54904575023617998598455689216, 85368351852511587342307295232, 54904575023617998598455689216, 54904575023617998598455689216,
    36151717709755870840413487104, 2030995376952577013506375680, 85368370741977518820888150016, 29701079998924770615301767168, 85368370741977518820888150016, 29701079998924770615301767168,
    29701079998924770615301767168, 108029230315498140949503016960, 29701079998924770615301767168, 36151717709755870840413487104, 36151717709755870840413487104, 15295102796173110575412281344,
    2030995376952577013506375680, 2030995376952577013506375680, 2205080694977083614664065024, 85368370741977518820888150016, 36151717709755870840413487104, 2030995376952577013506375680,
    331876604761932202479246639104, 54904575023617998598455689216, 85368351852511587342307295232, 54904575023617998598455689216, 54904575023617998598455689216, 36151717709755870840413487104,
    2030995376952577013506375680, 331876604761932202479246639104, 108029230315498140949503016960, 331876604761932202479246639104, 108029230315498140949503016960, 503227688346376718006163079168,
    54904575023617998598455689216, 54904575023617998598455689216, 17350503363109157915383037952, 2089023816294079213892272128, 85368351852511587342307295232, 29701079998924770615301767168,
    85368351852511587342307295232, 29701079998924770615301767168, 503204293742820581783774429184, 2089023816294079213892272128
  ]
def negativeScales : Array ℕ := #[
    19, 5, 24, 9, 4, 23,
    4, 4, 11, 4, 9, 11,
    18, 4, 4, 5, 32, 10,
    6, 33, 12, 32, 12, 12,
    10, 6, 32, 30, 32, 30,
    30, 31, 30, 10, 10, 17,
    6, 6, 5, 32, 10, 6,
    33, 12, 32, 12, 12, 10,
    6, 33, 31, 33, 31, 22,
    12, 12, 9, 4, 32, 30,
    32, 30, 25, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19720813711765428, 5832890015409720, 24773714469682898, 9808964175693987, 4754887502413606, 23773644404050627,
    4754887502413606, 4754887502413606, 11175549550636191, 4754887502413606, 9808964175693987, 11175549550636191,
    18723137622061855, 4754887502413606, 4754887502413606, 5832890015409720, 32107688302500599, 10868050856180197,
    6714245517766967, 33066561683699969, 12470913026274977, 32107687983275321, 12470913026274977, 12470913026274977,
    10868050856180197, 6714245517766967, 32107688302500599, 30584502048507646, 32107688302500599, 30584502048507646,
    30584502048507646, 31447336478247351, 30584502048507646, 10868050856180197, 10868050856180197, 17627056459931249,
    6714245517766967, 6714245517766967, 5832890015409720, 32107688302500599, 10868050856180197, 6714245517766967,
    33066561683699969, 12470913026274977, 32107687983275321, 12470913026274977, 12470913026274977, 10868050856180197,
    6714245517766967, 33066561683699969, 31447336478247351, 33066561683699969, 31447336478247351, 22667126055424331,
    12470913026274977, 12470913026274977, 9808964175693987, 4754887502413606, 32107687983275321, 30584502048507646,
    32107687983275321, 30584502048507646, 25667058984267674, 4754887502413606
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
noncomputable def negativeCeiling : ℝ := 1727734839 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 16322104169401669537906032640, coefficient := (-16322104169401669537906032640) }, { argument := 2205080694977083614664065024, coefficient := (-2205080694977083614664065024) }, { argument := 541814768230280327840441303040, coefficient := (-541814768230280327840441303040) }, { argument := 17350503363109157915383037952, coefficient := (-17350503363109157915383037952) }, { argument := 2089023816294079213892272128, coefficient := (-2089023816294079213892272128) }, { argument := 541788455204237778177310588928, coefficient := (-541788455204237778177310588928) }, { argument := 2089023816294079213892272128, coefficient := (-2089023816294079213892272128) }, { argument := 2089023816294079213892272128, coefficient := (-2089023816294079213892272128) }, { argument := 89479853464596392995052322816, coefficient := (-89479853464596392995052322816) }, { argument := 2089023816294079213892272128, coefficient := (-2089023816294079213892272128) }, { argument := 17350503363109157915383037952, coefficient := (-17350503363109157915383037952) }, { argument := 89479853464596392995052322816, coefficient := (-89479853464596392995052322816) }, { argument := 16348417195444219201036746752, coefficient := (-16348417195444219201036746752) }, { argument := 2089023816294079213892272128, coefficient := (-2089023816294079213892272128) }, { argument := 2089023816294079213892272128, coefficient := (-2089023816294079213892272128) }, { argument := 2205080694977083614664065024, coefficient := (-2205080694977083614664065024) }, { argument := 85368370741977518820888150016, coefficient := (-85368370741977518820888150016) }, { argument := 36151717709755870840413487104, coefficient := (-36151717709755870840413487104) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 331876604761932202479246639104, coefficient := (-331876604761932202479246639104) }, { argument := 54904575023617998598455689216, coefficient := (-54904575023617998598455689216) }, { argument := 85368351852511587342307295232, coefficient := (-85368351852511587342307295232) }, { argument := 54904575023617998598455689216, coefficient := (-54904575023617998598455689216) }, { argument := 54904575023617998598455689216, coefficient := (-54904575023617998598455689216) }, { argument := 36151717709755870840413487104, coefficient := (-36151717709755870840413487104) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 85368370741977518820888150016, coefficient := (-85368370741977518820888150016) }, { argument := 29701079998924770615301767168, coefficient := (-29701079998924770615301767168) }, { argument := 85368370741977518820888150016, coefficient := (-85368370741977518820888150016) }, { argument := 29701079998924770615301767168, coefficient := (-29701079998924770615301767168) }, { argument := 29701079998924770615301767168, coefficient := (-29701079998924770615301767168) }, { argument := 108029230315498140949503016960, coefficient := (-108029230315498140949503016960) }, { argument := 29701079998924770615301767168, coefficient := (-29701079998924770615301767168) }, { argument := 36151717709755870840413487104, coefficient := (-36151717709755870840413487104) }, { argument := 36151717709755870840413487104, coefficient := (-36151717709755870840413487104) }, { argument := 15295102796173110575412281344, coefficient := (-15295102796173110575412281344) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 2205080694977083614664065024, coefficient := (-2205080694977083614664065024) }, { argument := 85368370741977518820888150016, coefficient := (-85368370741977518820888150016) }, { argument := 36151717709755870840413487104, coefficient := (-36151717709755870840413487104) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 331876604761932202479246639104, coefficient := (-331876604761932202479246639104) }, { argument := 54904575023617998598455689216, coefficient := (-54904575023617998598455689216) }, { argument := 85368351852511587342307295232, coefficient := (-85368351852511587342307295232) }, { argument := 54904575023617998598455689216, coefficient := (-54904575023617998598455689216) }, { argument := 54904575023617998598455689216, coefficient := (-54904575023617998598455689216) }, { argument := 36151717709755870840413487104, coefficient := (-36151717709755870840413487104) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 331876604761932202479246639104, coefficient := (-331876604761932202479246639104) }, { argument := 108029230315498140949503016960, coefficient := (-108029230315498140949503016960) }, { argument := 331876604761932202479246639104, coefficient := (-331876604761932202479246639104) }, { argument := 108029230315498140949503016960, coefficient := (-108029230315498140949503016960) }, { argument := 503227688346376718006163079168, coefficient := (-503227688346376718006163079168) }, { argument := 54904575023617998598455689216, coefficient := (-54904575023617998598455689216) }, { argument := 54904575023617998598455689216, coefficient := (-54904575023617998598455689216) }, { argument := 17350503363109157915383037952, coefficient := (-17350503363109157915383037952) }, { argument := 2089023816294079213892272128, coefficient := (-2089023816294079213892272128) }, { argument := 85368351852511587342307295232, coefficient := (-85368351852511587342307295232) }, { argument := 29701079998924770615301767168, coefficient := (-29701079998924770615301767168) }, { argument := 85368351852511587342307295232, coefficient := (-85368351852511587342307295232) }, { argument := 29701079998924770615301767168, coefficient := (-29701079998924770615301767168) }, { argument := 503204293742820581783774429184, coefficient := (-503204293742820581783774429184) }, { argument := 2089023816294079213892272128, coefficient := (-2089023816294079213892272128) }] }

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


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 705281416609763760012926929338368
def positiveArguments : Array ℕ := #[
    79, 3, 57, 87, 897, 27,
    87, 27, 27, 2313, 27, 897,
    2313, 3, 27, 27, 57, 105,
    1869, 105, 3325, 5677, 105, 5677,
    5677, 1869, 105, 483, 541, 483,
    541, 17, 1, 15, 15, 2992103,
    21586021, 5984205
  ]
def positiveCoefficients : Array ℕ := #[
    6259024838626882669889972076544, 3713820117856140824697372672, 4410161389954167229328130048, 3365649481807127622381993984, 34701006726218315830766075904, 4178047632588158427784544256,
    3365649481807127622381993984, 4178047632588158427784544256, 4178047632588158427784544256, 178959706929192785990104645632, 4178047632588158427784544256, 34701006726218315830766075904,
    178959706929192785990104645632, 3713820117856140824697372672, 4178047632588158427784544256, 4178047632588158427784544256, 4410161389954167229328130048, 8123981507810308054025502720,
    144606870839023483361653948416, 8123981507810308054025502720, 128629707206996544188737126400, 219618300094471994393822756864, 8123981507810308054025502720, 219618300094471994393822756864,
    219618300094471994393822756864, 144606870839023483361653948416, 8123981507810308054025502720, 298962519487419336388138500096, 334862780626695364360213102592, 298962519487419336388138500096,
    334862780626695364360213102592, 1346878762742493739090247155712, 1267650600228229401496703205376, 1188422437713965063903159255040, 1188422437713965063903159255040, 452153821455798849690734166016,
    1630993633102724829526261497856, 452153745897935123776410746880
  ]
def positiveScales : Array ℕ := #[
    6, 1, 5, 6, 9, 4,
    6, 4, 4, 11, 4, 9,
    11, 1, 4, 4, 5, 6,
    10, 6, 11, 12, 6, 12,
    12, 10, 6, 8, 9, 8,
    9, 4, 0, 3, 3, 21,
    24, 22
  ]
def negativeArguments : Array ℕ := #[
    1610098773, 2928138155, 1610098773, 5677, 5677, 27,
    5677, 5677, 2313, 27, 1869, 1869,
    897, 2313, 1621909, 105, 105, 27,
    27, 57, 3, 7, 1, 17,
    1, 15
  ]
def negativeCoefficients : Array ℕ := #[
    29701079998924770615301767168, 108029230315498140949503016960, 29701079998924770615301767168, 54904575023617998598455689216, 54904575023617998598455689216, 2089023816294079213892272128,
    54904575023617998598455689216, 54904575023617998598455689216, 89479853464596392995052322816, 2089023816294079213892272128, 36151717709755870840413487104, 36151717709755870840413487104,
    17350503363109157915383037952, 89479853464596392995052322816, 15318497399729246797800931328, 2030995376952577013506375680, 2030995376952577013506375680, 2089023816294079213892272128,
    2089023816294079213892272128, 2205080694977083614664065024, 475368975085586025561263702016, 1109194275199700726309615304704, 1267650600228229401496703205376, 1346878762742493739090247155712,
    1267650600228229401496703205376, 2376844875427930127806318510080
  ]
def negativeScales : Array ℕ := #[
    30, 31, 30, 12, 12, 4,
    12, 12, 11, 4, 10, 10,
    9, 11, 20, 6, 6, 4,
    4, 5, 1, 2, 0, 4,
    0, 3
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6303780748177102, 1584962500720924, 5832890014087662, 6442943495848725, 9808964174871270, 4754887502147955,
    6442943495848725, 4754887502147955, 4754887502147955, 11175549550636190, 4754887502147955, 9808964174871270,
    11175549550636190, 1584962500720924, 4754887502147955, 4754887502147955, 5832890014087662, 6714245517659862,
    10868050853594526, 6714245517659862, 11699138625271509, 12470913026274870, 6714245517659862, 12470913026274870,
    12470913026274870, 10868050853594526, 6714245517659862, 8915879378478017, 9079484783826815, 8915879378478017,
    9079484783826815, 4087462841250339, 0, 3906890595303263, 3906890595303263, 21512728408664511,
    24363593996844147, 22512728167580705
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    30584502048507646, 31447336478247351, 30584502048507646, 12470913026274977, 12470913026274977, 4754887502413606,
    12470913026274977, 12470913026274977, 11175549550636191, 4754887502413606, 10868050856180197, 10868050856180197,
    9808964175693987, 11175549550636191, 20629261446270581, 6714245517766967, 6714245517766967, 4754887502413606,
    4754887502413606, 5832890015409720, 1584962500724866, 2807354922807594, 0, 4087462841250340,
    0, 3906890600547867
  ]

abbrev PositiveTerm := Fin 38
abbrev NegativeTerm := Fin 26
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
noncomputable def positiveFloor : ℝ := 107800237 / 62500000000
noncomputable def negativeCeiling : ℝ := 360671661 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 29701079998924770615301767168, coefficient := (-29701079998924770615301767168) }, { argument := 108029230315498140949503016960, coefficient := (-108029230315498140949503016960) }, { argument := 29701079998924770615301767168, coefficient := (-29701079998924770615301767168) }, { argument := 54904575023617998598455689216, coefficient := (-54904575023617998598455689216) }, { argument := 54904575023617998598455689216, coefficient := (-54904575023617998598455689216) }, { argument := 2089023816294079213892272128, coefficient := (-2089023816294079213892272128) }, { argument := 54904575023617998598455689216, coefficient := (-54904575023617998598455689216) }, { argument := 54904575023617998598455689216, coefficient := (-54904575023617998598455689216) }, { argument := 89479853464596392995052322816, coefficient := (-89479853464596392995052322816) }, { argument := 2089023816294079213892272128, coefficient := (-2089023816294079213892272128) }, { argument := 36151717709755870840413487104, coefficient := (-36151717709755870840413487104) }, { argument := 36151717709755870840413487104, coefficient := (-36151717709755870840413487104) }, { argument := 17350503363109157915383037952, coefficient := (-17350503363109157915383037952) }, { argument := 89479853464596392995052322816, coefficient := (-89479853464596392995052322816) }, { argument := 15318497399729246797800931328, coefficient := (-15318497399729246797800931328) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 2089023816294079213892272128, coefficient := (-2089023816294079213892272128) }, { argument := 2089023816294079213892272128, coefficient := (-2089023816294079213892272128) }, { argument := 2205080694977083614664065024, coefficient := (-2205080694977083614664065024) }, { argument := 6259024838626882669889972076544, coefficient := 6259024838626882669889972076544 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 34701006726218315830766075904, coefficient := 34701006726218315830766075904 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 178959706929192785990104645632, coefficient := 178959706929192785990104645632 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 34701006726218315830766075904, coefficient := 34701006726218315830766075904 }, { argument := 178959706929192785990104645632, coefficient := 178959706929192785990104645632 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 8123981507810308054025502720, coefficient := 8123981507810308054025502720 }, { argument := 144606870839023483361653948416, coefficient := 144606870839023483361653948416 }, { argument := 8123981507810308054025502720, coefficient := 8123981507810308054025502720 }, { argument := 128629707206996544188737126400, coefficient := 128629707206996544188737126400 }, { argument := 219618300094471994393822756864, coefficient := 219618300094471994393822756864 }, { argument := 8123981507810308054025502720, coefficient := 8123981507810308054025502720 }, { argument := 219618300094471994393822756864, coefficient := 219618300094471994393822756864 }, { argument := 219618300094471994393822756864, coefficient := 219618300094471994393822756864 }, { argument := 144606870839023483361653948416, coefficient := 144606870839023483361653948416 }, { argument := 8123981507810308054025502720, coefficient := 8123981507810308054025502720 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 298962519487419336388138500096, coefficient := 298962519487419336388138500096 }, { argument := 334862780626695364360213102592, coefficient := 334862780626695364360213102592 }, { argument := 298962519487419336388138500096, coefficient := 298962519487419336388138500096 }, { argument := 334862780626695364360213102592, coefficient := 334862780626695364360213102592 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 1346878762742493739090247155712, coefficient := 1346878762742493739090247155712 }, { argument := 1346878762742493739090247155712, coefficient := (-1346878762742493739090247155712) }, { argument := 1267650600228229401496703205376, coefficient := 1267650600228229401496703205376 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 1188422437713965063903159255040, coefficient := 1188422437713965063903159255040 }, { argument := 1188422437713965063903159255040, coefficient := 1188422437713965063903159255040 }, { argument := 2376844875427930127806318510080, coefficient := (-2376844875427930127806318510080) }, { argument := 452153821455798849690734166016, coefficient := 452153821455798849690734166016 }, { argument := 1630993633102724829526261497856, coefficient := 1630993633102724829526261497856 }, { argument := 452153745897935123776410746880, coefficient := 452153745897935123776410746880 }] }

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


end Parent2

namespace Parent2

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-304196529973517924190411997315072)
def positiveArguments : Array ℕ := #[
    1477193, 55145911, 110286559, 2959649
  ]
def positiveCoefficients : Array ℕ := #[
    27903386847718639288620941312, 1041676807094849918224222388224, 1041627099465251232338703024128, 27953094477317325174140305408
  ]
def positiveScales : Array ℕ := #[
    20, 25, 26, 21
  ]
def negativeArguments : Array ℕ := #[
    1, 27
  ]
def negativeCoefficients : Array ℕ := #[
    2535301200456458802993406410752, 2139160387885137115025686659072
  ]
def negativeScales : Array ℕ := #[
    0, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    20494426900472596, 25716750579963083, 26716681734557962, 21496994658696754
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 4754887502413606
  ]

abbrev PositiveTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 671549307 / 1000000000000
noncomputable def negativeCeiling : ℝ := 122434581 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2535301200456458802993406410752, coefficient := (-2535301200456458802993406410752) }, { argument := 27903386847718639288620941312, coefficient := 27903386847718639288620941312 }, { argument := 1041676807094849918224222388224, coefficient := 1041676807094849918224222388224 }, { argument := 1041627099465251232338703024128, coefficient := 1041627099465251232338703024128 }, { argument := 27953094477317325174140305408, coefficient := 27953094477317325174140305408 }, { argument := 2139160387885137115025686659072, coefficient := (-2139160387885137115025686659072) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk23
