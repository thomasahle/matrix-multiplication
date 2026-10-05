import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 4, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk4

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
def constantNumerator : ℤ := 11703733436018628267159960158208
def positiveArguments : Array ℕ := #[
    1, 61743, 1017703, 2035409, 30873, 20585
  ]
def positiveCoefficients : Array ℕ := #[
    316912650057057350374175801344, 2332584590014564035433857024, 76895464587454184686624964608, 76895577924249773558110093312, 2332697926810152906918985728, 777679312398973173791457280
  ]
def positiveScales : Array ℕ := #[
    0, 15, 19, 20, 14, 14
  ]
def negativeArguments : Array ℕ := #[
    11684924493, 253197855405, 506115953277, 2919764727, 51458325, 26661072605,
    290439377105, 26642271165, 792937285, 192601310453, 4173432082005, 8342252951717,
    48126157167, 26661072605, 842904384509, 4577582382757, 1685383249493, 51050758499,
    11684924493, 192601310453, 385203188659, 5842746123, 385203188659, 8346876466515,
    16684530494851, 96252456201, 290439377105, 4577582382757, 99401190138719, 18306749943083,
    555731128289, 253197855405, 4173432082005, 8346876466515, 126605078955, 5842746123,
    126605078955, 253070272347, 1459953297, 26642271165, 1685383249493, 18306749943083,
    210617904105, 25510207199, 506115953277, 8342252951717, 16684530494851, 253070272347,
    792937285, 51050758499, 555731128289, 25510207199, 381270685, 2919764727,
    48126157167, 96252456201, 1459953297, 1
  ]
def negativeCoefficients : Array ℕ := #[
    13156055398131795473989632, 570150883626483363285565440, 569835904646140140976078848, 13149451336526717981294592, 926990773180439514316800, 30017699162293934772715520,
    327005667625949241823723520, 29996530622749427588136960, 892768015313543196835840, 433699594993600008074297344, 18795467169373791304789524480, 18785083642391550779579170816,
    433481886968150250869489664, 30017699162293934772715520, 949025967995922420246511616, 10307799156621086197060468736, 948786421799143811439394816, 28739022119134697711730688,
    13156055398131795473989632, 433699594993600008074297344, 433700234226649817694601216, 13156694631181605094293504, 433700234226649817694601216, 18795494872152258166621470720,
    18785111329865660207699329024, 433482525880318587039645696, 327005667625949241823723520, 10307799156621086197060468736, 111915790717229677499861958656, 10305784027754180957119184896,
    312848812785065713538695168, 570150883626483363285565440, 18795467169373791304789524480, 18795494872152258166621470720, 570178586404950225117511680, 13156694631181605094293504,
    570178586404950225117511680, 569863592120249569096237056, 13150090248695054151450624, 29996530622749427588136960, 948786421799143811439394816, 10305784027754180957119184896,
    948538714444832859834286080, 28721939908890136124850176, 569835904646140140976078848, 18785083642391550779579170816, 18785111329865660207699329024, 569863592120249569096237056,
    892768015313543196835840, 28739022119134697711730688, 312848812785065713538695168, 28721939908890136124850176, 858545257446646879354880, 13149451336526717981294592,
    433481886968150250869489664, 433482525880318587039645696, 13150090248695054151450624, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    33, 37, 38, 31, 25, 34,
    38, 34, 29, 37, 41, 42,
    35, 34, 39, 42, 40, 35,
    33, 37, 38, 32, 38, 42,
    43, 36, 38, 42, 46, 44,
    39, 37, 41, 42, 36, 32,
    36, 37, 30, 34, 40, 44,
    37, 34, 38, 42, 43, 37,
    29, 35, 39, 34, 28, 31,
    35, 36, 30, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 15913987962253181, 19956885164451995, 20956887290849324, 14914058058943529, 14329305828208631
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    33443929360450419, 37881474232021130, 38880676997079453, 31443204976219873, 25616901161449181, 34634015771729709,
    38079446107641849, 34632998021492448, 29562631523898363, 37486826563025672, 41924371438192554, 42923574203203592,
    35486102178795122, 34634015771729709, 39616578031024667, 42057722989089415, 40616213830523151, 35571213345329178,
    33443929360450419, 37486826563025672, 38486828689423026, 32443999457141193, 38486828689423026, 42924373564590157,
    43923576329601191, 36486104305192477, 38079446107641849, 42057722989089415, 46498328358934685, 44057440921056284,
    39015596096304939, 37881474232021130, 41924371438192554, 42924373564590157, 36881544328715920, 32443999457141193,
    36881544328715920, 37880747093774189, 30443275072910648, 34632998021492448, 40616213830523151, 44057440921056284,
    37615837125269060, 34570355565721416, 38880676997079453, 42923574203203592, 43923576329601191, 37880747093774189,
    29562631523898363, 35571213345329178, 39015596096304939, 34570355565721416, 28506240369022502, 31443204976219873,
    35486102178795122, 36486104305192477, 30443275072910648, 0
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
noncomputable def positiveFloor : ℝ := 38869361 / 1000000000000
noncomputable def negativeCeiling : ℝ := 167842357 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 13156055398131795473989632, coefficient := (-13156055398131795473989632) }, { argument := 570150883626483363285565440, coefficient := (-570150883626483363285565440) }, { argument := 569835904646140140976078848, coefficient := (-569835904646140140976078848) }, { argument := 13149451336526717981294592, coefficient := (-13149451336526717981294592) }, { argument := 926990773180439514316800, coefficient := (-926990773180439514316800) }, { argument := 30017699162293934772715520, coefficient := (-30017699162293934772715520) }, { argument := 327005667625949241823723520, coefficient := (-327005667625949241823723520) }, { argument := 29996530622749427588136960, coefficient := (-29996530622749427588136960) }, { argument := 892768015313543196835840, coefficient := (-892768015313543196835840) }, { argument := 433699594993600008074297344, coefficient := (-433699594993600008074297344) }, { argument := 18795467169373791304789524480, coefficient := (-18795467169373791304789524480) }, { argument := 18785083642391550779579170816, coefficient := (-18785083642391550779579170816) }, { argument := 433481886968150250869489664, coefficient := (-433481886968150250869489664) }, { argument := 30017699162293934772715520, coefficient := (-30017699162293934772715520) }, { argument := 949025967995922420246511616, coefficient := (-949025967995922420246511616) }, { argument := 10307799156621086197060468736, coefficient := (-10307799156621086197060468736) }, { argument := 948786421799143811439394816, coefficient := (-948786421799143811439394816) }, { argument := 28739022119134697711730688, coefficient := (-28739022119134697711730688) }, { argument := 13156055398131795473989632, coefficient := (-13156055398131795473989632) }, { argument := 433699594993600008074297344, coefficient := (-433699594993600008074297344) }, { argument := 433700234226649817694601216, coefficient := (-433700234226649817694601216) }, { argument := 13156694631181605094293504, coefficient := (-13156694631181605094293504) }, { argument := 433700234226649817694601216, coefficient := (-433700234226649817694601216) }, { argument := 18795494872152258166621470720, coefficient := (-18795494872152258166621470720) }, { argument := 18785111329865660207699329024, coefficient := (-18785111329865660207699329024) }, { argument := 433482525880318587039645696, coefficient := (-433482525880318587039645696) }, { argument := 327005667625949241823723520, coefficient := (-327005667625949241823723520) }, { argument := 10307799156621086197060468736, coefficient := (-10307799156621086197060468736) }, { argument := 111915790717229677499861958656, coefficient := (-111915790717229677499861958656) }, { argument := 10305784027754180957119184896, coefficient := (-10305784027754180957119184896) }, { argument := 312848812785065713538695168, coefficient := (-312848812785065713538695168) }, { argument := 570150883626483363285565440, coefficient := (-570150883626483363285565440) }, { argument := 18795467169373791304789524480, coefficient := (-18795467169373791304789524480) }, { argument := 18795494872152258166621470720, coefficient := (-18795494872152258166621470720) }, { argument := 570178586404950225117511680, coefficient := (-570178586404950225117511680) }, { argument := 13156694631181605094293504, coefficient := (-13156694631181605094293504) }, { argument := 570178586404950225117511680, coefficient := (-570178586404950225117511680) }, { argument := 569863592120249569096237056, coefficient := (-569863592120249569096237056) }, { argument := 13150090248695054151450624, coefficient := (-13150090248695054151450624) }, { argument := 29996530622749427588136960, coefficient := (-29996530622749427588136960) }, { argument := 948786421799143811439394816, coefficient := (-948786421799143811439394816) }, { argument := 10305784027754180957119184896, coefficient := (-10305784027754180957119184896) }, { argument := 948538714444832859834286080, coefficient := (-948538714444832859834286080) }, { argument := 28721939908890136124850176, coefficient := (-28721939908890136124850176) }, { argument := 569835904646140140976078848, coefficient := (-569835904646140140976078848) }, { argument := 18785083642391550779579170816, coefficient := (-18785083642391550779579170816) }, { argument := 18785111329865660207699329024, coefficient := (-18785111329865660207699329024) }, { argument := 569863592120249569096237056, coefficient := (-569863592120249569096237056) }, { argument := 892768015313543196835840, coefficient := (-892768015313543196835840) }, { argument := 28739022119134697711730688, coefficient := (-28739022119134697711730688) }, { argument := 312848812785065713538695168, coefficient := (-312848812785065713538695168) }, { argument := 28721939908890136124850176, coefficient := (-28721939908890136124850176) }, { argument := 858545257446646879354880, coefficient := (-858545257446646879354880) }, { argument := 13149451336526717981294592, coefficient := (-13149451336526717981294592) }, { argument := 433481886968150250869489664, coefficient := (-433481886968150250869489664) }, { argument := 433482525880318587039645696, coefficient := (-433482525880318587039645696) }, { argument := 13150090248695054151450624, coefficient := (-13150090248695054151450624) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 2332584590014564035433857024, coefficient := 2332584590014564035433857024 }, { argument := 76895464587454184686624964608, coefficient := 76895464587454184686624964608 }, { argument := 76895577924249773558110093312, coefficient := 76895577924249773558110093312 }, { argument := 2332697926810152906918985728, coefficient := 2332697926810152906918985728 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 777679312398973173791457280, coefficient := 777679312398973173791457280 }] }

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
def constantNumerator : ℤ := (-11701503003075397276971485364224)
def positiveArguments : Array ℕ := #[
    2597081, 28199681, 2596543, 78787, 189251, 4100835,
    8197139, 47289
  ]
def positiveCoefficients : Array ℕ := #[
    24528736535395162122461642752, 266338456764031919218808061952, 24523655269059594384211705856, 744122176171701474902933504, 1787425158499126452674363392, 77462583023114966119628144640,
    77419788938047201394701631488, 1786527908867381220083761152
  ]
def positiveScales : Array ℕ := #[
    21, 24, 21, 16, 17, 21,
    22, 15
  ]
def negativeArguments : Array ℕ := #[
    1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    316912650057057350374175801344, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    21308459580058227, 24749175506881441, 21308160686670961, 16265669981531174, 17529941397851098, 21967486265438996,
    22966689030553932, 15529217013620555
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0
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
noncomputable def positiveFloor : ℝ := 4208381 / 31250000000
noncomputable def negativeCeiling : ℝ := 0 / 1

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 24528736535395162122461642752, coefficient := 24528736535395162122461642752 }, { argument := 266338456764031919218808061952, coefficient := 266338456764031919218808061952 }, { argument := 24523655269059594384211705856, coefficient := 24523655269059594384211705856 }, { argument := 744122176171701474902933504, coefficient := 744122176171701474902933504 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 1787425158499126452674363392, coefficient := 1787425158499126452674363392 }, { argument := 77462583023114966119628144640, coefficient := 77462583023114966119628144640 }, { argument := 77419788938047201394701631488, coefficient := 77419788938047201394701631488 }, { argument := 1786527908867381220083761152, coefficient := 1786527908867381220083761152 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk4
