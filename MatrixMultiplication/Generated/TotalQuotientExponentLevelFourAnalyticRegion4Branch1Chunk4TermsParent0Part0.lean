import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 4, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk4

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 40375953104884447154685966548992
def positiveArguments : Array ℕ := #[
    13, 233425, 16310367, 2038797, 466839, 281629
  ]
def positiveCoefficients : Array ℕ := #[
    1029966112685436388716071354368, 4409273585055387736027955200, 154047060888206253190350372864, 154047145890802944843964219392, 4409169692992764603833253888, 2659910700408190623775981568
  ]
def positiveScales : Array ℕ := #[
    3, 17, 23, 20, 18, 18
  ]
def negativeArguments : Array ℕ := #[
    70034081841, 15024136351, 3847274010131, 17239072943, 9143029565, 180524416289,
    1992283389609, 45131309361, 9141448615, 613669255051, 134366279580323, 67202099947297,
    2417393703151, 180524416289, 1843421463457, 81531851041837, 3686857814227, 22561707217,
    70034081841, 613669255051, 306834807611, 70032359371, 306834807611, 16795794204595,
    16800534246031, 302174390915, 1992283389609, 81531851041837, 450791833110763, 81532175726503,
    1991943834541, 15024136351, 134366279580323, 16795794204595, 3846088353989, 70032359371,
    3846088353989, 3847183435571, 68954591293, 45131309361, 3686857814227, 81532175726503,
    3686872701505, 180494478701, 3847274010131, 67202099947297, 16800534246031, 3847183435571,
    9141448615, 22561707217, 1991943834541, 180494478701, 9139867925, 17239072943,
    2417393703151, 302174390915, 68954591293, 1
  ]
def negativeCoefficients : Array ℕ := #[
    19712841555147651280797696, 1082603117950833975976001536, 1082911362401135340799655936, 19409470620576899957522432, 2573534033873214258544640, 101626211741302087292551168,
    1121555841382440137819947008, 101626674010471088970006528, 2573089036008783546941440, 690930157094103367574093824, 37820745415568909278682021888, 37831419035145199760036593664,
    680435836294914188882477056, 101626211741302087292551168, 4151016107955859804531982336, 45898351746355487409799430144, 4151032869580179641517211648, 101608896215323430336069632,
    19712841555147651280797696, 690930157094103367574093824, 690930562610598714988822528, 19712356722944516477157376, 690930562610598714988822528, 37820766260602789127845314560,
    37831439885025234283227250688, 680436237162850295920721920, 1121555841382440137819947008, 45898351746355487409799430144, 507546482904823766871401562112, 45898534527573088724043431936,
    1121364688872725567391137792, 1082603117950833975976001536, 37820745415568909278682021888, 37820766260602789127845314560, 1082577629866179044556406784, 19712356722944516477157376,
    1082577629866179044556406784, 1082885867928968762885144576, 19408991978289977997918208, 101626674010471088970006528, 4151032869580179641517211648, 45898534527573088724043431936,
    4151049631165092981762949120, 101609358377531940863475712, 1082911362401135340799655936, 37831419035145199760036593664, 37831439885025234283227250688, 1082885867928968762885144576,
    2573089036008783546941440, 101608896215323430336069632, 1121364688872725567391137792, 101609358377531940863475712, 2572644111327846780108800, 19409470620576899957522432,
    680435836294914188882477056, 680436237162850295920721920, 19408991978289977997918208, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    36, 33, 41, 34, 33, 37,
    40, 35, 33, 39, 46, 45,
    41, 37, 40, 46, 41, 34,
    36, 39, 38, 36, 38, 43,
    43, 38, 40, 46, 48, 46,
    40, 33, 46, 43, 41, 36,
    41, 41, 36, 35, 41, 46,
    41, 37, 41, 45, 43, 41,
    33, 34, 40, 37, 33, 34,
    41, 38, 36, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3700439718136550, 17832599557447122, 23959285907993984, 20959286704067526, 18832565564017989, 18103436373760122
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    36027338124315826, 33806563010901534, 41806973724155615, 34004963142297280, 33090025138984506, 37393403021465163,
    40857560016821223, 35393409583865841, 33089775656477198, 39158670349744886, 46933164462560876, 45933571556801382,
    41136589592028447, 37393403021465163, 40745523092471530, 46212429002858751, 41745528918000253, 34393157187723430,
    36027338124315826, 39158670349744886, 38158671196482374, 36027302641170745, 38158671196482374, 43933165257707096,
    43933572351908071, 38136590441969003, 40857560016821223, 46212429002858751, 48679454707248739, 46212434748098419,
    40857314109946531, 33806563010901534, 46933164462560876, 43933165257707096, 41806529044652831, 36027302641170745,
    41806529044652831, 41806939759065436, 36004927564646466, 35393409583865841, 41745528918000253, 46212434748098419,
    41745534743491758, 37393163749723754, 41806973724155615, 45933571556801382, 43933572351908071, 41806939759065436,
    33089775656477198, 34393157187723430, 40857314109946531, 37393163749723754, 33089526171859952, 34004963142297280,
    41136589592028447, 38136590441969003, 36004927564646466, 0
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
noncomputable def positiveFloor : ℝ := 131694147 / 1000000000000
noncomputable def negativeCeiling : ℝ := 581767583 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 19712841555147651280797696, coefficient := (-19712841555147651280797696) }, { argument := 1082603117950833975976001536, coefficient := (-1082603117950833975976001536) }, { argument := 1082911362401135340799655936, coefficient := (-1082911362401135340799655936) }, { argument := 19409470620576899957522432, coefficient := (-19409470620576899957522432) }, { argument := 2573534033873214258544640, coefficient := (-2573534033873214258544640) }, { argument := 101626211741302087292551168, coefficient := (-101626211741302087292551168) }, { argument := 1121555841382440137819947008, coefficient := (-1121555841382440137819947008) }, { argument := 101626674010471088970006528, coefficient := (-101626674010471088970006528) }, { argument := 2573089036008783546941440, coefficient := (-2573089036008783546941440) }, { argument := 690930157094103367574093824, coefficient := (-690930157094103367574093824) }, { argument := 37820745415568909278682021888, coefficient := (-37820745415568909278682021888) }, { argument := 37831419035145199760036593664, coefficient := (-37831419035145199760036593664) }, { argument := 680435836294914188882477056, coefficient := (-680435836294914188882477056) }, { argument := 101626211741302087292551168, coefficient := (-101626211741302087292551168) }, { argument := 4151016107955859804531982336, coefficient := (-4151016107955859804531982336) }, { argument := 45898351746355487409799430144, coefficient := (-45898351746355487409799430144) }, { argument := 4151032869580179641517211648, coefficient := (-4151032869580179641517211648) }, { argument := 101608896215323430336069632, coefficient := (-101608896215323430336069632) }, { argument := 19712841555147651280797696, coefficient := (-19712841555147651280797696) }, { argument := 690930157094103367574093824, coefficient := (-690930157094103367574093824) }, { argument := 690930562610598714988822528, coefficient := (-690930562610598714988822528) }, { argument := 19712356722944516477157376, coefficient := (-19712356722944516477157376) }, { argument := 690930562610598714988822528, coefficient := (-690930562610598714988822528) }, { argument := 37820766260602789127845314560, coefficient := (-37820766260602789127845314560) }, { argument := 37831439885025234283227250688, coefficient := (-37831439885025234283227250688) }, { argument := 680436237162850295920721920, coefficient := (-680436237162850295920721920) }, { argument := 1121555841382440137819947008, coefficient := (-1121555841382440137819947008) }, { argument := 45898351746355487409799430144, coefficient := (-45898351746355487409799430144) }, { argument := 507546482904823766871401562112, coefficient := (-507546482904823766871401562112) }, { argument := 45898534527573088724043431936, coefficient := (-45898534527573088724043431936) }, { argument := 1121364688872725567391137792, coefficient := (-1121364688872725567391137792) }, { argument := 1082603117950833975976001536, coefficient := (-1082603117950833975976001536) }, { argument := 37820745415568909278682021888, coefficient := (-37820745415568909278682021888) }, { argument := 37820766260602789127845314560, coefficient := (-37820766260602789127845314560) }, { argument := 1082577629866179044556406784, coefficient := (-1082577629866179044556406784) }, { argument := 19712356722944516477157376, coefficient := (-19712356722944516477157376) }, { argument := 1082577629866179044556406784, coefficient := (-1082577629866179044556406784) }, { argument := 1082885867928968762885144576, coefficient := (-1082885867928968762885144576) }, { argument := 19408991978289977997918208, coefficient := (-19408991978289977997918208) }, { argument := 101626674010471088970006528, coefficient := (-101626674010471088970006528) }, { argument := 4151032869580179641517211648, coefficient := (-4151032869580179641517211648) }, { argument := 45898534527573088724043431936, coefficient := (-45898534527573088724043431936) }, { argument := 4151049631165092981762949120, coefficient := (-4151049631165092981762949120) }, { argument := 101609358377531940863475712, coefficient := (-101609358377531940863475712) }, { argument := 1082911362401135340799655936, coefficient := (-1082911362401135340799655936) }, { argument := 37831419035145199760036593664, coefficient := (-37831419035145199760036593664) }, { argument := 37831439885025234283227250688, coefficient := (-37831439885025234283227250688) }, { argument := 1082885867928968762885144576, coefficient := (-1082885867928968762885144576) }, { argument := 2573089036008783546941440, coefficient := (-2573089036008783546941440) }, { argument := 101608896215323430336069632, coefficient := (-101608896215323430336069632) }, { argument := 1121364688872725567391137792, coefficient := (-1121364688872725567391137792) }, { argument := 101609358377531940863475712, coefficient := (-101609358377531940863475712) }, { argument := 2572644111327846780108800, coefficient := (-2572644111327846780108800) }, { argument := 19409470620576899957522432, coefficient := (-19409470620576899957522432) }, { argument := 680435836294914188882477056, coefficient := (-680435836294914188882477056) }, { argument := 680436237162850295920721920, coefficient := (-680436237162850295920721920) }, { argument := 19408991978289977997918208, coefficient := (-19408991978289977997918208) }, { argument := 1029966112685436388716071354368, coefficient := 1029966112685436388716071354368 }, { argument := 4409273585055387736027955200, coefficient := 4409273585055387736027955200 }, { argument := 154047060888206253190350372864, coefficient := 154047060888206253190350372864 }, { argument := 154047145890802944843964219392, coefficient := 154047145890802944843964219392 }, { argument := 4409169692992764603833253888, coefficient := 4409169692992764603833253888 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 2659910700408190623775981568, coefficient := 2659910700408190623775981568 }] }

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


end Parent0

namespace Parent0

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-38765120382196912043827482591232)
def positiveArguments : Array ℕ := #[
    5760209, 31847713, 720029, 281581, 300969, 1029763,
    16480859, 74099
  ]
def positiveCoefficients : Array ℕ := #[
    108807271663696304746954489856, 1203172579418015017420911017984, 108807706121412728754314149888, 2659457353225835137835466752, 2842571835965588500641742848, 155613384847977422854119489536,
    155657312301001076293897289728, 2799381072113262725517279232
  ]
def positiveScales : Array ℕ := #[
    22, 24, 19, 18, 18, 19,
    23, 16
  ]
def negativeArguments : Array ℕ := #[
    9, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1426106925256758076683791106048, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    22457689727830877, 24924686439352064, 19457695488371805, 18103190464198395, 18199255370559777, 19973880907651264,
    23974288102537513, 16177166452380480
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    3169925001442313, 0
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
noncomputable def positiveFloor : ℝ := 99990783 / 200000000000
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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 108807271663696304746954489856, coefficient := 108807271663696304746954489856 }, { argument := 1203172579418015017420911017984, coefficient := 1203172579418015017420911017984 }, { argument := 108807706121412728754314149888, coefficient := 108807706121412728754314149888 }, { argument := 2659457353225835137835466752, coefficient := 2659457353225835137835466752 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 2842571835965588500641742848, coefficient := 2842571835965588500641742848 }, { argument := 155613384847977422854119489536, coefficient := 155613384847977422854119489536 }, { argument := 155657312301001076293897289728, coefficient := 155657312301001076293897289728 }, { argument := 2799381072113262725517279232, coefficient := 2799381072113262725517279232 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk4
