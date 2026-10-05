import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 5, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk5

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
def constantNumerator : ℤ := (-373538981177713049133786333184)
def positiveArguments : Array ℕ := #[
    3, 8386841, 8390375, 15112297, 53665651, 3777033,
    2260401, 81625649, 81625769, 2260341, 106365, 10041,
    28205277, 1284761, 25693
  ]
def positiveCoefficients : Array ℕ := #[
    1901475900342344102245054808064, 158422947342227752534717497344, 158489702714829597839458304000, 285463219327885963016009678848, 1013715486255119434128119824384, 285384544702281354726749503488,
    21348883840490057821367304192, 770932457960164345935359377408, 770933591328120234650210664448, 21348317156512113463941660672, 1004589021900859626309550080, 24277648309500983086449426432,
    266391309489708196288039747584, 24268449139592353017573146624, 970654096354958355803930624
  ]
def positiveScales : Array ℕ := #[
    1, 22, 23, 23, 25, 21,
    21, 26, 26, 21, 16, 13,
    24, 20, 14
  ]
def negativeArguments : Array ℕ := #[
    111508827255, 1347389503641, 118276693070481, 10775028556651, 13467814043, 3416423518233,
    123354666184061, 123354847860485, 3416333462373, 3416423518233, 6064889208003, 3415415977569,
    111508827255, 111554745225, 111554745225, 1347970910055, 118326319213935, 10779684248725,
    13473249125, 6064889208003, 54756271354579, 54756351783259, 6064727544453, 123354666184061,
    54756271354579, 123320735185899, 1347389503641, 1347970910055, 3415415977569, 123320735185899,
    123320916712995, 3415326044049, 123354847860485, 54756351783259, 123320916712995, 118276693070481,
    118326319213935, 3416333462373, 6064727544453, 3415326044049, 10775028556651, 10779684248725,
    13467814043, 13473249125, 1, 5, 5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    251095556437069504173834240, 6068102866520525163447975936, 66583858854854094748303491072, 6065801824079987118662746112, 242614569222199732770701312, 1923275460456742218362781696,
    69442503582618630418472108032, 69442605857353058969001656320, 1923224763514549902168293376, 1923275460456742218362781696, 6828458194301413351722319872, 1922708265486873340598550528,
    251095556437069504173834240, 251198954513360308980940800, 251198954513360308980940800, 6070721288229966379776737280, 66611795890000003395716382720, 6068422745716189390123827200,
    242712478955279445131264000, 6828458194301413351722319872, 246600323268679748653819101184, 246600685487253026554683326464, 6828276177325528503835164672, 69442503582618630418472108032,
    246600323268679748653819101184, 69423402128783793895388479488, 6068102866520525163447975936, 6070721288229966379776737280, 1922708265486873340598550528, 69423402128783793895388479488,
    69423504319454031801420349440, 1922657637415978325967372288, 69442605857353058969001656320, 246600685487253026554683326464, 69423504319454031801420349440, 66583858854854094748303491072,
    66611795890000003395716382720, 1923224763514549902168293376, 6828276177325528503835164672, 1922657637415978325967372288, 6065801824079987118662746112, 6068422745716189390123827200,
    242614569222199732770701312, 242712478955279445131264000, 316912650057057350374175801344, 1584563250285286751870879006720, 1584563250285286751870879006720, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    36, 40, 46, 43, 33, 41,
    46, 46, 41, 41, 42, 41,
    36, 36, 36, 40, 46, 43,
    33, 42, 45, 45, 42, 46,
    45, 46, 40, 40, 41, 46,
    46, 41, 46, 45, 46, 46,
    46, 41, 42, 41, 43, 43,
    33, 33, 0, 2, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 22999696073192418, 23000303861342093, 23849219624320750, 25677495642780928, 21848821957903024,
    21108147301873022, 26282519221686644, 26282521342628772, 21108109006521304, 16698663976462904, 13293615336407685,
    24749461769712197, 20293068573736175, 14649087733486068
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    36698366965033933, 40293304104327044, 46749159141084259, 43292756926375299, 33648796655281346, 41635623968943778,
    46809805619257488, 46809807744053373, 41635585939450544, 41635623968943778, 42463618429414725, 41635198439646307,
    36698366965033933, 36698960926906913, 36698960926906913, 40293926501360826, 46749764335344181, 43293380153790312,
    33649378753018904, 42463618429414725, 45638089442721967, 45638091561821200, 42463579972931449, 46809805619257488,
    45638089442721967, 46809408724523836, 40293304104327044, 40293926501360826, 41635198439646307, 46809408724523836,
    46809410848157401, 41635160450612917, 46809807744053373, 45638091561821200, 46809410848157401, 46749159141084259,
    46749764335344181, 41635585939450544, 42463579972931449, 41635160450612917, 43292756926375299, 43293380153790312,
    33648796655281346, 33649378753018904, 0, 2321928094887363, 2321928094887363, 0
  ]

abbrev PositiveTerm := Fin 15
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
noncomputable def positiveFloor : ℝ := 147815821 / 125000000000
noncomputable def negativeCeiling : ℝ := 1140264241 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 251095556437069504173834240, coefficient := (-251095556437069504173834240) }, { argument := 6068102866520525163447975936, coefficient := (-6068102866520525163447975936) }, { argument := 66583858854854094748303491072, coefficient := (-66583858854854094748303491072) }, { argument := 6065801824079987118662746112, coefficient := (-6065801824079987118662746112) }, { argument := 242614569222199732770701312, coefficient := (-242614569222199732770701312) }, { argument := 1923275460456742218362781696, coefficient := (-1923275460456742218362781696) }, { argument := 69442503582618630418472108032, coefficient := (-69442503582618630418472108032) }, { argument := 69442605857353058969001656320, coefficient := (-69442605857353058969001656320) }, { argument := 1923224763514549902168293376, coefficient := (-1923224763514549902168293376) }, { argument := 1923275460456742218362781696, coefficient := (-1923275460456742218362781696) }, { argument := 6828458194301413351722319872, coefficient := (-6828458194301413351722319872) }, { argument := 1922708265486873340598550528, coefficient := (-1922708265486873340598550528) }, { argument := 251095556437069504173834240, coefficient := (-251095556437069504173834240) }, { argument := 251198954513360308980940800, coefficient := (-251198954513360308980940800) }, { argument := 251198954513360308980940800, coefficient := (-251198954513360308980940800) }, { argument := 6070721288229966379776737280, coefficient := (-6070721288229966379776737280) }, { argument := 66611795890000003395716382720, coefficient := (-66611795890000003395716382720) }, { argument := 6068422745716189390123827200, coefficient := (-6068422745716189390123827200) }, { argument := 242712478955279445131264000, coefficient := (-242712478955279445131264000) }, { argument := 6828458194301413351722319872, coefficient := (-6828458194301413351722319872) }, { argument := 246600323268679748653819101184, coefficient := (-246600323268679748653819101184) }, { argument := 246600685487253026554683326464, coefficient := (-246600685487253026554683326464) }, { argument := 6828276177325528503835164672, coefficient := (-6828276177325528503835164672) }, { argument := 69442503582618630418472108032, coefficient := (-69442503582618630418472108032) }, { argument := 246600323268679748653819101184, coefficient := (-246600323268679748653819101184) }, { argument := 69423402128783793895388479488, coefficient := (-69423402128783793895388479488) }, { argument := 6068102866520525163447975936, coefficient := (-6068102866520525163447975936) }, { argument := 6070721288229966379776737280, coefficient := (-6070721288229966379776737280) }, { argument := 1922708265486873340598550528, coefficient := (-1922708265486873340598550528) }, { argument := 69423402128783793895388479488, coefficient := (-69423402128783793895388479488) }, { argument := 69423504319454031801420349440, coefficient := (-69423504319454031801420349440) }, { argument := 1922657637415978325967372288, coefficient := (-1922657637415978325967372288) }, { argument := 69442605857353058969001656320, coefficient := (-69442605857353058969001656320) }, { argument := 246600685487253026554683326464, coefficient := (-246600685487253026554683326464) }, { argument := 69423504319454031801420349440, coefficient := (-69423504319454031801420349440) }, { argument := 66583858854854094748303491072, coefficient := (-66583858854854094748303491072) }, { argument := 66611795890000003395716382720, coefficient := (-66611795890000003395716382720) }, { argument := 1923224763514549902168293376, coefficient := (-1923224763514549902168293376) }, { argument := 6828276177325528503835164672, coefficient := (-6828276177325528503835164672) }, { argument := 1922657637415978325967372288, coefficient := (-1922657637415978325967372288) }, { argument := 6065801824079987118662746112, coefficient := (-6065801824079987118662746112) }, { argument := 6068422745716189390123827200, coefficient := (-6068422745716189390123827200) }, { argument := 242614569222199732770701312, coefficient := (-242614569222199732770701312) }, { argument := 242712478955279445131264000, coefficient := (-242712478955279445131264000) }, { argument := 1901475900342344102245054808064, coefficient := 1901475900342344102245054808064 }, { argument := 158422947342227752534717497344, coefficient := 158422947342227752534717497344 }, { argument := 158489702714829597839458304000, coefficient := 158489702714829597839458304000 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 285463219327885963016009678848, coefficient := 285463219327885963016009678848 }, { argument := 1013715486255119434128119824384, coefficient := 1013715486255119434128119824384 }, { argument := 285384544702281354726749503488, coefficient := 285384544702281354726749503488 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }, { argument := 21348883840490057821367304192, coefficient := 21348883840490057821367304192 }, { argument := 770932457960164345935359377408, coefficient := 770932457960164345935359377408 }, { argument := 770933591328120234650210664448, coefficient := 770933591328120234650210664448 }, { argument := 21348317156512113463941660672, coefficient := 21348317156512113463941660672 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }, { argument := 1004589021900859626309550080, coefficient := 1004589021900859626309550080 }, { argument := 24277648309500983086449426432, coefficient := 24277648309500983086449426432 }, { argument := 266391309489708196288039747584, coefficient := 266391309489708196288039747584 }, { argument := 24268449139592353017573146624, coefficient := 24268449139592353017573146624 }, { argument := 970654096354958355803930624, coefficient := 970654096354958355803930624 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk5
