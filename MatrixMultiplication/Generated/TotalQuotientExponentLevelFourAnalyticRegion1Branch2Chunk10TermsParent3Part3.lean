import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 10, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-174377035165173877034286704047947776)
def positiveArguments : Array ℕ := #[
    356820915613, 8451, 1632374789, 16929, 7587, 2565,
    837, 7670554043, 38869, 134469054215, 961801, 30599,
    67234241637, 15713, 15713, 531761, 28945, 961801,
    531761, 7671722659, 30599, 28945, 38869, 57341871,
    17363845, 71451, 82077727565, 73319, 2335, 71451,
    40629, 73319, 1144617, 1401, 1111286663, 71451,
    2335, 1401, 2335, 35959, 40629, 114683677,
    29710037, 923035947, 1155, 1023, 47883, 13035,
    461518107, 47883, 1155, 1155, 495, 1155,
    13035, 495, 14854885, 1023
  ]
def positiveCoefficients : Array ℕ := #[
    1685039132277689284875469767835648, 653864454500046793948281176064, 493355007427520590093559546249216, 654908966408193833555227312128, 587015692378636259103728467968, 793829050191750101279063408640,
    32379869152558227815330217984, 36223167317703447335891451772928, 751835802921616342266469679104, 1270024309216194382036605369057280, 18603936995698719277785196527616, 591870738470208609869348470784,
    1270018916830910189880389463441408, 607867244915349383109060591616, 607867244915349383109060591616, 10285753644225517193134893694976, 559877725579927063389924229120, 18603936995698719277785196527616,
    10285753644225517193134893694976, 36228685950733192529202500337664, 591870738470208609869348470784, 559877725579927063389924229120, 751835802921616342266469679104, 541578659350869811319046930432,
    41983201096572761444151921213440, 5528253359186231626363582808064, 387601109643061979257946494730240, 5672782858772799773458055561216, 180661874483210183868090941440, 5528253359186231626363582808064,
    3143516616007857199304782381056, 5672782858772799773458055561216, 88560450871669632132138179493888, 3468707990077635530267346075648, 41983223121690037548177197891584, 5528253359186231626363582808064,
    180661874483210183868090941440, 3468707990077635530267346075648, 180661874483210183868090941440, 5564385734082873663137200996352, 3143516616007857199304782381056, 541578352397048424792108040192,
    140301682933617025475781066752, 4358914018596642247377904730112, 89363796585913388594280529920, 79150791261809001326362755072, 3704767681318866481437172826112, 1008534275755308242706880266240,
    4358915279468493173573176786944, 3704767681318866481437172826112, 89363796585913388594280529920, 89363796585913388594280529920, 76597539930782904509383311360, 89363796585913388594280529920,
    1008534275755308242706880266240, 76597539930782904509383311360, 140300422061766099280509009920, 79150791261809001326362755072
  ]
def positiveScales : Array ℕ := #[
    38, 13, 30, 14, 12, 11,
    9, 32, 15, 36, 19, 14,
    35, 13, 13, 19, 14, 19,
    19, 32, 14, 14, 15, 25,
    24, 16, 36, 16, 11, 16,
    15, 16, 20, 10, 30, 16,
    11, 10, 11, 15, 15, 26,
    24, 29, 10, 9, 15, 13,
    28, 15, 10, 10, 8, 10,
    13, 8, 23, 9
  ]
def negativeArguments : Array ℕ := #[
    33767, 33767, 15, 241
  ]
def negativeCoefficients : Array ℕ := #[
    2675297363619163887521198570995712, 2675297363619163887521198570995712, 608472288109550112718417538580480, 19093987165937705360044092030976
  ]
def negativeScales : Array ℕ := #[
    15, 15, 3, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    38376409227311697, 13044906349096086, 30604325188350761, 14047209134965507, 12889313822161717, 11324743110494416,
    9709083812544787, 32836683641047479, 15246332370848911, 36968483241932126, 19875378900471935, 14901196884524413,
    35968477116392753, 13939671032074786, 13939671032074786, 19020418446499221, 14821026536055186, 19875378900471935,
    19020418446499221, 32836903420229043, 14901196884524413, 14821026536055186, 15246332370848911, 25773085643032570,
    24049583113619102, 16124666582402313, 36256271737371115, 16161899488601288, 11189206834597024, 16124666582402313,
    15310222235558389, 16161899488601288, 20126433508576501, 10452241240430814, 30049583870481807, 16124666582402313,
    11189206834597024, 10452241240430814, 11189206834597024, 15134065280404563, 15310222235558389, 26773084825347321,
    24824447066010327, 29781811592802444, 10173677136303419, 9998590428318153, 15547225923425121, 13670102962420728,
    28781812010120449, 15547225923425121, 10173677136303419, 10173677136303419, 8951284714309401, 10173677136303419,
    13670102962420728, 8951284714309401, 23824434100650968, 9998590428318153
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    15043326389591331, 15043326389591331, 3906890600547867, 7912889341723050
  ]

abbrev PositiveTerm := Fin 58
abbrev NegativeTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 587622431259 / 250000000000
noncomputable def negativeCeiling : ℝ := 499652829427 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1685039132277689284875469767835648, coefficient := 1685039132277689284875469767835648 }, { argument := 653864454500046793948281176064, coefficient := 653864454500046793948281176064 }, { argument := 493355007427520590093559546249216, coefficient := 493355007427520590093559546249216 }, { argument := 654908966408193833555227312128, coefficient := 654908966408193833555227312128 }, { argument := 587015692378636259103728467968, coefficient := 587015692378636259103728467968 }, { argument := 793829050191750101279063408640, coefficient := 793829050191750101279063408640 }, { argument := 32379869152558227815330217984, coefficient := 32379869152558227815330217984 }, { argument := 2675297363619163887521198570995712, coefficient := (-2675297363619163887521198570995712) }, { argument := 36223167317703447335891451772928, coefficient := 36223167317703447335891451772928 }, { argument := 751835802921616342266469679104, coefficient := 751835802921616342266469679104 }, { argument := 1270024309216194382036605369057280, coefficient := 1270024309216194382036605369057280 }, { argument := 18603936995698719277785196527616, coefficient := 18603936995698719277785196527616 }, { argument := 591870738470208609869348470784, coefficient := 591870738470208609869348470784 }, { argument := 1270018916830910189880389463441408, coefficient := 1270018916830910189880389463441408 }, { argument := 607867244915349383109060591616, coefficient := 607867244915349383109060591616 }, { argument := 607867244915349383109060591616, coefficient := 607867244915349383109060591616 }, { argument := 10285753644225517193134893694976, coefficient := 10285753644225517193134893694976 }, { argument := 559877725579927063389924229120, coefficient := 559877725579927063389924229120 }, { argument := 18603936995698719277785196527616, coefficient := 18603936995698719277785196527616 }, { argument := 10285753644225517193134893694976, coefficient := 10285753644225517193134893694976 }, { argument := 36228685950733192529202500337664, coefficient := 36228685950733192529202500337664 }, { argument := 591870738470208609869348470784, coefficient := 591870738470208609869348470784 }, { argument := 559877725579927063389924229120, coefficient := 559877725579927063389924229120 }, { argument := 751835802921616342266469679104, coefficient := 751835802921616342266469679104 }, { argument := 2675297363619163887521198570995712, coefficient := (-2675297363619163887521198570995712) }, { argument := 541578659350869811319046930432, coefficient := 541578659350869811319046930432 }, { argument := 41983201096572761444151921213440, coefficient := 41983201096572761444151921213440 }, { argument := 5528253359186231626363582808064, coefficient := 5528253359186231626363582808064 }, { argument := 387601109643061979257946494730240, coefficient := 387601109643061979257946494730240 }, { argument := 5672782858772799773458055561216, coefficient := 5672782858772799773458055561216 }, { argument := 180661874483210183868090941440, coefficient := 180661874483210183868090941440 }, { argument := 5528253359186231626363582808064, coefficient := 5528253359186231626363582808064 }, { argument := 3143516616007857199304782381056, coefficient := 3143516616007857199304782381056 }, { argument := 5672782858772799773458055561216, coefficient := 5672782858772799773458055561216 }, { argument := 88560450871669632132138179493888, coefficient := 88560450871669632132138179493888 }, { argument := 3468707990077635530267346075648, coefficient := 3468707990077635530267346075648 }, { argument := 41983223121690037548177197891584, coefficient := 41983223121690037548177197891584 }, { argument := 5528253359186231626363582808064, coefficient := 5528253359186231626363582808064 }, { argument := 180661874483210183868090941440, coefficient := 180661874483210183868090941440 }, { argument := 3468707990077635530267346075648, coefficient := 3468707990077635530267346075648 }, { argument := 180661874483210183868090941440, coefficient := 180661874483210183868090941440 }, { argument := 5564385734082873663137200996352, coefficient := 5564385734082873663137200996352 }, { argument := 3143516616007857199304782381056, coefficient := 3143516616007857199304782381056 }, { argument := 541578352397048424792108040192, coefficient := 541578352397048424792108040192 }, { argument := 608472288109550112718417538580480, coefficient := (-608472288109550112718417538580480) }, { argument := 140301682933617025475781066752, coefficient := 140301682933617025475781066752 }, { argument := 4358914018596642247377904730112, coefficient := 4358914018596642247377904730112 }, { argument := 89363796585913388594280529920, coefficient := 89363796585913388594280529920 }, { argument := 79150791261809001326362755072, coefficient := 79150791261809001326362755072 }, { argument := 3704767681318866481437172826112, coefficient := 3704767681318866481437172826112 }, { argument := 1008534275755308242706880266240, coefficient := 1008534275755308242706880266240 }, { argument := 4358915279468493173573176786944, coefficient := 4358915279468493173573176786944 }, { argument := 3704767681318866481437172826112, coefficient := 3704767681318866481437172826112 }, { argument := 89363796585913388594280529920, coefficient := 89363796585913388594280529920 }, { argument := 89363796585913388594280529920, coefficient := 89363796585913388594280529920 }, { argument := 76597539930782904509383311360, coefficient := 76597539930782904509383311360 }, { argument := 89363796585913388594280529920, coefficient := 89363796585913388594280529920 }, { argument := 1008534275755308242706880266240, coefficient := 1008534275755308242706880266240 }, { argument := 76597539930782904509383311360, coefficient := 76597539930782904509383311360 }, { argument := 140300422061766099280509009920, coefficient := 140300422061766099280509009920 }, { argument := 79150791261809001326362755072, coefficient := 79150791261809001326362755072 }, { argument := 19093987165937705360044092030976, coefficient := (-19093987165937705360044092030976) }] }

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

end TermShard6


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10
