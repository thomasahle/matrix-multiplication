import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 5, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk5

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
def constantNumerator : ℤ := 16729574990892806665425219747840
def positiveArguments : Array ℕ := #[
    17, 25165825, 25165823, 84631095, 150231777, 84667399,
    390909, 55817, 228626563, 6254509, 108937, 1784081,
    21486325, 7136373, 227425
  ]
def positiveCoefficients : Array ℕ := #[
    5387515050969974956360988622848, 475368993975051957039844556800, 475368956196120094082682847232, 799318092873113633393202954240, 2837798033466987439252379271168, 799660974458701832592878993408,
    59072497902466884506902069248, 2159315599149752212626388025344, 2159316836409770724473434013696, 59072167336813083631737110528, 2057761750177482162577604608, 67400674536996476019967787008,
    811730408160353037569333657600, 67401137328911797245198729216, 2147968394733258125449625600
  ]
def positiveScales : Array ℕ := #[
    4, 24, 24, 26, 27, 26,
    18, 15, 27, 22, 16, 20,
    24, 22, 17
  ]
def negativeArguments : Array ℕ := #[
    913829863813, 14965957011327, 180240364399641, 14966059771887, 953889613677, 1181280409161,
    691036450313523, 691036843769715, 9450190250853, 1181280409161, 67124569923159, 18908779199769,
    913829863813, 913829715579, 913829715579, 14965955287169, 180240351171559, 14966058047505,
    953889560723, 67124569923159, 613336471211853, 1226673647896017, 67124195023059, 691036450313523,
    613336471211853, 691332697812377, 14965957011327, 14965955287169, 18908779199769, 691332697812377,
    691333091226859, 18908672942179, 691036843769715, 1226673647896017, 691333091226859, 180240364399641,
    180240351171559, 9450190250853, 67124195023059, 18908672942179, 14966059771887, 14966058047505,
    953889613677, 953889560723, 3, 7, 7, 3
  ]
def negativeCoefficients : Array ℕ := #[
    514440479268532238371782656, 16850169604863784795974402048, 202932609486836405145629097984, 16850285302968715891848511488, 536992113588540448098484224, 5320014010517546649419513856,
    194509468758213278534455001088, 194509579506285758397850583040, 5319984161540233114876379136, 5320014010517546649419513856, 18893886755833979732496482304, 5322348184881915871535038464,
    514440479268532238371782656, 514440395820208842917019648, 514440395820208842917019648, 16850167663634453214009491456, 202932594593340113639037730816, 16850283361487182730750853120,
    536992083778088614626328576, 18893886755833979732496482304, 690555475800609029504234422272, 690555872946213646979567714304, 18893781230837063409891016704, 194509468758213278534455001088,
    690555475800609029504234422272, 194592855016053798274504589312, 16850169604863784795974402048, 16850167663634453214009491456, 5322348184881915871535038464, 194592855016053798274504589312,
    194592965752385956859298709504, 5322318276029245291101159424, 194509579506285758397850583040, 690555872946213646979567714304, 194592965752385956859298709504, 202932609486836405145629097984,
    202932594593340113639037730816, 5319984161540233114876379136, 18893781230837063409891016704, 5322318276029245291101159424, 16850285302968715891848511488, 16850283361487182730750853120,
    536992113588540448098484224, 536992083778088614626328576, 950737950171172051122527404032, 4436777100798802905238461218816, 4436777100798802905238461218816, 950737950171172051122527404032
  ]
def negativeScales : Array ℕ := #[
    39, 43, 47, 43, 39, 40,
    49, 49, 43, 40, 45, 44,
    39, 39, 39, 43, 47, 43,
    39, 45, 49, 50, 45, 49,
    49, 49, 43, 43, 44, 49,
    49, 44, 49, 50, 49, 47,
    47, 43, 45, 44, 43, 43,
    39, 39, 1, 2, 2, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    4087462841250339, 24584962558048474, 24584962443393373, 26334684497296563, 27162614762839631, 26335303234065329,
    18576473274990917, 15768416965390379, 27768417792035813, 22576465201745655, 16733134517098981, 20766749686605812,
    24356915410929504, 22766759592520157, 17795031327547133
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    39733134634274539, 43766749770051802, 47356915463870169, 43766759675976445, 39795031368211609, 40103488607098326,
    49295755139325509, 49295755960754154, 43103480512553411, 40103488607098326, 45931906180761894, 44104121455665630,
    39733134634274539, 39733134400252339, 39733134400252339, 43766749603845635, 47356915357988842, 43766759509749826,
    39795031288122178, 45931906180761894, 49123672069833849, 50123672899542467, 45931898123084987, 49295755139325509,
    49123672069833849, 49296373490515703, 43766749770051802, 43766749603845635, 44104121455665630, 49296373490515703,
    49296374311505311, 44104113348440554, 49295755960754154, 50123672899542467, 49296374311505311, 47356915463870169,
    47356915357988842, 43103480512553411, 45931898123084987, 44104113348440554, 43766759675976445, 43766759509749826,
    39795031368211609, 39795031288122178, 1584962500724866, 2807354922807594, 2807354922807594, 1584962500724866
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
noncomputable def positiveFloor : ℝ := 341618019 / 100000000000
noncomputable def negativeCeiling : ℝ := 3509107051 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 514440479268532238371782656, coefficient := (-514440479268532238371782656) }, { argument := 16850169604863784795974402048, coefficient := (-16850169604863784795974402048) }, { argument := 202932609486836405145629097984, coefficient := (-202932609486836405145629097984) }, { argument := 16850285302968715891848511488, coefficient := (-16850285302968715891848511488) }, { argument := 536992113588540448098484224, coefficient := (-536992113588540448098484224) }, { argument := 5320014010517546649419513856, coefficient := (-5320014010517546649419513856) }, { argument := 194509468758213278534455001088, coefficient := (-194509468758213278534455001088) }, { argument := 194509579506285758397850583040, coefficient := (-194509579506285758397850583040) }, { argument := 5319984161540233114876379136, coefficient := (-5319984161540233114876379136) }, { argument := 5320014010517546649419513856, coefficient := (-5320014010517546649419513856) }, { argument := 18893886755833979732496482304, coefficient := (-18893886755833979732496482304) }, { argument := 5322348184881915871535038464, coefficient := (-5322348184881915871535038464) }, { argument := 514440479268532238371782656, coefficient := (-514440479268532238371782656) }, { argument := 514440395820208842917019648, coefficient := (-514440395820208842917019648) }, { argument := 514440395820208842917019648, coefficient := (-514440395820208842917019648) }, { argument := 16850167663634453214009491456, coefficient := (-16850167663634453214009491456) }, { argument := 202932594593340113639037730816, coefficient := (-202932594593340113639037730816) }, { argument := 16850283361487182730750853120, coefficient := (-16850283361487182730750853120) }, { argument := 536992083778088614626328576, coefficient := (-536992083778088614626328576) }, { argument := 18893886755833979732496482304, coefficient := (-18893886755833979732496482304) }, { argument := 690555475800609029504234422272, coefficient := (-690555475800609029504234422272) }, { argument := 690555872946213646979567714304, coefficient := (-690555872946213646979567714304) }, { argument := 18893781230837063409891016704, coefficient := (-18893781230837063409891016704) }, { argument := 194509468758213278534455001088, coefficient := (-194509468758213278534455001088) }, { argument := 690555475800609029504234422272, coefficient := (-690555475800609029504234422272) }, { argument := 194592855016053798274504589312, coefficient := (-194592855016053798274504589312) }, { argument := 16850169604863784795974402048, coefficient := (-16850169604863784795974402048) }, { argument := 16850167663634453214009491456, coefficient := (-16850167663634453214009491456) }, { argument := 5322348184881915871535038464, coefficient := (-5322348184881915871535038464) }, { argument := 194592855016053798274504589312, coefficient := (-194592855016053798274504589312) }, { argument := 194592965752385956859298709504, coefficient := (-194592965752385956859298709504) }, { argument := 5322318276029245291101159424, coefficient := (-5322318276029245291101159424) }, { argument := 194509579506285758397850583040, coefficient := (-194509579506285758397850583040) }, { argument := 690555872946213646979567714304, coefficient := (-690555872946213646979567714304) }, { argument := 194592965752385956859298709504, coefficient := (-194592965752385956859298709504) }, { argument := 202932609486836405145629097984, coefficient := (-202932609486836405145629097984) }, { argument := 202932594593340113639037730816, coefficient := (-202932594593340113639037730816) }, { argument := 5319984161540233114876379136, coefficient := (-5319984161540233114876379136) }, { argument := 18893781230837063409891016704, coefficient := (-18893781230837063409891016704) }, { argument := 5322318276029245291101159424, coefficient := (-5322318276029245291101159424) }, { argument := 16850285302968715891848511488, coefficient := (-16850285302968715891848511488) }, { argument := 16850283361487182730750853120, coefficient := (-16850283361487182730750853120) }, { argument := 536992113588540448098484224, coefficient := (-536992113588540448098484224) }, { argument := 536992083778088614626328576, coefficient := (-536992083778088614626328576) }, { argument := 5387515050969974956360988622848, coefficient := 5387515050969974956360988622848 }, { argument := 475368993975051957039844556800, coefficient := 475368993975051957039844556800 }, { argument := 475368956196120094082682847232, coefficient := 475368956196120094082682847232 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 799318092873113633393202954240, coefficient := 799318092873113633393202954240 }, { argument := 2837798033466987439252379271168, coefficient := 2837798033466987439252379271168 }, { argument := 799660974458701832592878993408, coefficient := 799660974458701832592878993408 }, { argument := 4436777100798802905238461218816, coefficient := (-4436777100798802905238461218816) }, { argument := 59072497902466884506902069248, coefficient := 59072497902466884506902069248 }, { argument := 2159315599149752212626388025344, coefficient := 2159315599149752212626388025344 }, { argument := 2159316836409770724473434013696, coefficient := 2159316836409770724473434013696 }, { argument := 59072167336813083631737110528, coefficient := 59072167336813083631737110528 }, { argument := 4436777100798802905238461218816, coefficient := (-4436777100798802905238461218816) }, { argument := 2057761750177482162577604608, coefficient := 2057761750177482162577604608 }, { argument := 67400674536996476019967787008, coefficient := 67400674536996476019967787008 }, { argument := 811730408160353037569333657600, coefficient := 811730408160353037569333657600 }, { argument := 67401137328911797245198729216, coefficient := 67401137328911797245198729216 }, { argument := 2147968394733258125449625600, coefficient := 2147968394733258125449625600 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk5
