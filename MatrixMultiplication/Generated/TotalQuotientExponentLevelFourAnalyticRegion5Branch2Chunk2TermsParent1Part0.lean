import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 2, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk2

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
def constantNumerator : ℤ := 1731957737975127141992626126848
def positiveArguments : Array ℕ := #[
    17, 3014459, 2687073, 3014465, 1987539, 73509897,
    73509933, 1987575, 101353, 2603653, 439805, 2601377,
    100529
  ]
def positiveCoefficients : Array ℕ := #[
    1346878762742493739090247155712, 113883041164677982729862643712, 406058991111167557545656057856, 113883267838269160472832901120, 18771775113992503556768268288, 694281347503999768170671898624,
    694281687514386534785127284736, 18772115124379270171223654400, 1914504040553148605374922752, 49181614640892001478300925952, 531691620095611984181649735680, 49138622216431956228275437568,
    1898939120625610254750580736
  ]
def positiveScales : Array ℕ := #[
    4, 21, 21, 21, 20, 26,
    26, 20, 16, 21, 18, 21,
    16
  ]
def negativeArguments : Array ℕ := #[
    152808884503, 3923708503351, 42425886385565, 1960132253617, 151561485491, 438819878685,
    16233857229267, 16233864711795, 438829291677, 152808884503, 544577388465, 19103039207,
    544577388465, 13993792179013, 75633146555385, 13981592096567, 540161740257, 16233857229267,
    600411559282521, 600411853789269, 16234149805695, 3923708503351, 13993792179013, 980880925665,
    19103039207, 980880925665, 42426331955825, 3920075309415, 37893786971, 16233864711795,
    600411853789269, 600412148295185, 16234157290279, 42425886385565, 75633146555385, 42426331955825,
    438829291677, 16234149805695, 16234157290279, 438838703549, 1960132253617, 13981592096567,
    3920075309415, 151561485491, 540161740257, 37893786971, 1, 9,
    1
  ]
def negativeCoefficients : Array ℕ := #[
    172047508826652990213455872, 4417703038400502538933633024, 47767301529223383346640322560, 4413825443493205880147542016, 170643062395246608996368384, 123516815133033266266767360,
    4569424585532043365713969152, 4569426691676437902545387520, 123519464654737243858010112, 172047508826652990213455872, 613139630941342961667932160, 172064880508578350806073344,
    613139630941342961667932160, 15755609310725777013826650112, 170310705321844999553789460480, 15741873239036353281479671808, 608168053035305962064314368, 4569424585532043365713969152,
    169000829665856252767975243776, 169000912562136287199010750464, 4569506938475300752635985920, 4417703038400502538933633024, 15755609310725777013826650112, 4417494971319721186390179840,
    172064880508578350806073344, 4417494971319721186390179840, 47767803196737609190395084800, 4413612425686418952510504960, 170658444882252556314607616, 4569426691676437902545387520,
    169000912562136287199010750464, 169000995458182134449422991360, 4569509045198407841584513024, 47767301529223383346640322560, 170310705321844999553789460480, 47767803196737609190395084800,
    123519464654737243858010112, 4569506938475300752635985920, 4569509045198407841584513024, 123522113861189247533318144, 4413825443493205880147542016, 15741873239036353281479671808,
    4413612425686418952510504960, 170643062395246608996368384, 608168053035305962064314368, 170658444882252556314607616, 633825300114114700748351602688, 1426106925256758076683791106048,
    633825300114114700748351602688
  ]
def negativeScales : Array ℕ := #[
    37, 41, 45, 40, 37, 38,
    43, 43, 38, 37, 38, 34,
    38, 43, 46, 43, 38, 43,
    49, 49, 43, 41, 43, 39,
    34, 39, 45, 41, 35, 43,
    49, 49, 43, 45, 46, 45,
    38, 43, 43, 38, 40, 43,
    41, 37, 38, 35, 0, 3,
    0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    4087462841250339, 21523467676573782, 21357604085058355, 21523470548121092, 20922551738528975, 26131435164386307,
    26131435870917140, 20922577869614076, 16629029266951434, 21312105756484683, 18746504480240692, 21310844063805739,
    16617252215850361
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    37152937469698752, 41835355006080850, 45270010035217623, 40834088138753229, 37141112228994700, 38674837925582423,
    43884071067525090, 43884071732493621, 38674868872063889, 37152937469698752, 38986346143894327, 34153083131640394,
    38986346143894327, 43669852205115689, 46104083873945056, 43668593884629316, 38974600516604169, 43884071067525090,
    49092945080796461, 49092945788449927, 43884097068418005, 41835355006080850, 43669852205115689, 39835287055741093,
    34153083131640394, 39835287055741093, 45270025186783888, 41834018510454347, 35141242273763105, 43884071732493621,
    49092945788449927, 49092946496101046, 43884097733557264, 45270010035217623, 46104083873945056, 45270025186783888,
    38674868872063889, 43884097068418005, 43884097733557264, 38674899814199519, 40834088138753229, 43668593884629316,
    41834018510454347, 37141112228994700, 38974600516604169, 35141242273763105, 0, 3169925001442313,
    0
  ]

abbrev PositiveTerm := Fin 13
abbrev NegativeTerm := Fin 49
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
noncomputable def positiveFloor : ℝ := 821852629 / 1000000000000
noncomputable def negativeCeiling : ℝ := 163779789 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 172047508826652990213455872, coefficient := (-172047508826652990213455872) }, { argument := 4417703038400502538933633024, coefficient := (-4417703038400502538933633024) }, { argument := 47767301529223383346640322560, coefficient := (-47767301529223383346640322560) }, { argument := 4413825443493205880147542016, coefficient := (-4413825443493205880147542016) }, { argument := 170643062395246608996368384, coefficient := (-170643062395246608996368384) }, { argument := 123516815133033266266767360, coefficient := (-123516815133033266266767360) }, { argument := 4569424585532043365713969152, coefficient := (-4569424585532043365713969152) }, { argument := 4569426691676437902545387520, coefficient := (-4569426691676437902545387520) }, { argument := 123519464654737243858010112, coefficient := (-123519464654737243858010112) }, { argument := 172047508826652990213455872, coefficient := (-172047508826652990213455872) }, { argument := 613139630941342961667932160, coefficient := (-613139630941342961667932160) }, { argument := 172064880508578350806073344, coefficient := (-172064880508578350806073344) }, { argument := 613139630941342961667932160, coefficient := (-613139630941342961667932160) }, { argument := 15755609310725777013826650112, coefficient := (-15755609310725777013826650112) }, { argument := 170310705321844999553789460480, coefficient := (-170310705321844999553789460480) }, { argument := 15741873239036353281479671808, coefficient := (-15741873239036353281479671808) }, { argument := 608168053035305962064314368, coefficient := (-608168053035305962064314368) }, { argument := 4569424585532043365713969152, coefficient := (-4569424585532043365713969152) }, { argument := 169000829665856252767975243776, coefficient := (-169000829665856252767975243776) }, { argument := 169000912562136287199010750464, coefficient := (-169000912562136287199010750464) }, { argument := 4569506938475300752635985920, coefficient := (-4569506938475300752635985920) }, { argument := 4417703038400502538933633024, coefficient := (-4417703038400502538933633024) }, { argument := 15755609310725777013826650112, coefficient := (-15755609310725777013826650112) }, { argument := 4417494971319721186390179840, coefficient := (-4417494971319721186390179840) }, { argument := 172064880508578350806073344, coefficient := (-172064880508578350806073344) }, { argument := 4417494971319721186390179840, coefficient := (-4417494971319721186390179840) }, { argument := 47767803196737609190395084800, coefficient := (-47767803196737609190395084800) }, { argument := 4413612425686418952510504960, coefficient := (-4413612425686418952510504960) }, { argument := 170658444882252556314607616, coefficient := (-170658444882252556314607616) }, { argument := 4569426691676437902545387520, coefficient := (-4569426691676437902545387520) }, { argument := 169000912562136287199010750464, coefficient := (-169000912562136287199010750464) }, { argument := 169000995458182134449422991360, coefficient := (-169000995458182134449422991360) }, { argument := 4569509045198407841584513024, coefficient := (-4569509045198407841584513024) }, { argument := 47767301529223383346640322560, coefficient := (-47767301529223383346640322560) }, { argument := 170310705321844999553789460480, coefficient := (-170310705321844999553789460480) }, { argument := 47767803196737609190395084800, coefficient := (-47767803196737609190395084800) }, { argument := 123519464654737243858010112, coefficient := (-123519464654737243858010112) }, { argument := 4569506938475300752635985920, coefficient := (-4569506938475300752635985920) }, { argument := 4569509045198407841584513024, coefficient := (-4569509045198407841584513024) }, { argument := 123522113861189247533318144, coefficient := (-123522113861189247533318144) }, { argument := 4413825443493205880147542016, coefficient := (-4413825443493205880147542016) }, { argument := 15741873239036353281479671808, coefficient := (-15741873239036353281479671808) }, { argument := 4413612425686418952510504960, coefficient := (-4413612425686418952510504960) }, { argument := 170643062395246608996368384, coefficient := (-170643062395246608996368384) }, { argument := 608168053035305962064314368, coefficient := (-608168053035305962064314368) }, { argument := 170658444882252556314607616, coefficient := (-170658444882252556314607616) }, { argument := 1346878762742493739090247155712, coefficient := 1346878762742493739090247155712 }, { argument := 113883041164677982729862643712, coefficient := 113883041164677982729862643712 }, { argument := 406058991111167557545656057856, coefficient := 406058991111167557545656057856 }, { argument := 113883267838269160472832901120, coefficient := 113883267838269160472832901120 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 18771775113992503556768268288, coefficient := 18771775113992503556768268288 }, { argument := 694281347503999768170671898624, coefficient := 694281347503999768170671898624 }, { argument := 694281687514386534785127284736, coefficient := 694281687514386534785127284736 }, { argument := 18772115124379270171223654400, coefficient := 18772115124379270171223654400 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 1914504040553148605374922752, coefficient := 1914504040553148605374922752 }, { argument := 49181614640892001478300925952, coefficient := 49181614640892001478300925952 }, { argument := 531691620095611984181649735680, coefficient := 531691620095611984181649735680 }, { argument := 49138622216431956228275437568, coefficient := 49138622216431956228275437568 }, { argument := 1898939120625610254750580736, coefficient := 1898939120625610254750580736 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk2
