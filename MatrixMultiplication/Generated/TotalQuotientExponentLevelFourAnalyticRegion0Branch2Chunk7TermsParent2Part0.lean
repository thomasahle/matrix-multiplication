import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 7, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk7

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
def constantNumerator : ℤ := (-28434120455207796835632436740096)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    149420346231, 383635889397, 110332779, 32805450549923, 158044251, 26837703,
    432385215, 110332779, 158044251, 7141810965, 158044251, 1533000451483,
    432385215, 26837703, 158044251, 26837703, 110332779, 110332779,
    18206485601, 114686494461, 9695738012751, 4849437356631, 231245441289, 149420346231,
    2128525100533, 597645216815, 2128525100533, 10868572239911, 399958937, 462969830018371,
    572914153, 97287309, 1567406645, 399958937, 572914153, 25889233895,
    572914153, 2714407944753, 1567406645, 97287309, 572914153, 97287309,
    399958937, 399958937, 518528327239, 9695738012751, 50301043525845, 402523119242727,
    4879617991569, 383635889397, 10868572239911, 3067676450865, 110332779, 399958937,
    27616319, 597645216815, 3067676450865, 27616319, 131129274615857, 39558511,
    6717483, 108226115, 27616319, 39558511
  ]
def negativeCoefficients : Array ℕ := #[
    168232353901875524108550144, 3455484897068556034794061824, 508820134288538917159305216, 36935653718088613971416317952, 364425231314764359587069952, 61883529845903381816672256,
    498506212647555020189859840, 508820134288538917159305216, 364425231314764359587069952, 8233947443385477747273891840, 364425231314764359587069952, 3452010131028820466056822784,
    498506212647555020189859840, 61883529845903381816672256, 364425231314764359587069952, 61883529845903381816672256, 508820134288538917159305216, 508820134288538917159305216,
    163989443536779801832456192, 64562756714873506687352832, 2729107631331709812165574656, 2729990534034991839939919872, 65089805201266644388675584, 168232353901875524108550144,
    599126553100572896052379648, 168222173484237080640880640, 599126553100572896052379648, 12236924472428124163448766464, 1844485037707980477770498048, 130314422122157344305631461376,
    1321050094574634666511302656, 224329261342862490539655168, 1807096827484170062680555520, 1844485037707980477770498048, 1321050094574634666511302656, 29848254495341981380137451520,
    1321050094574634666511302656, 12224606608521124693030207488, 1807096827484170062680555520, 224329261342862490539655168, 1321050094574634666511302656, 224329261342862490539655168,
    1844485037707980477770498048, 1844485037707980477770498048, 583810995333651752745435136, 2729107631331709812165574656, 113267880439671321140983234560, 113300185614347190328111398912,
    2746980721067564561520918528, 3455484897068556034794061824, 12236924472428124163448766464, 3453896630252214920423669760, 508820134288538917159305216, 1844485037707980477770498048,
    509431168850922490774421504, 168222173484237080640880640, 3453896630252214920423669760, 509431168850922490774421504, 36909609518583564075838472192, 364862864177012054203301888,
    61957844860247329959051264, 499104861374214602447912960, 509431168850922490774421504, 364862864177012054203301888
  ]
def negativeScales : Array ℕ := #[
    37, 38, 26, 44, 27, 24,
    28, 26, 27, 32, 27, 40,
    28, 24, 27, 24, 26, 26,
    34, 36, 43, 42, 37, 37,
    40, 39, 40, 43, 28, 48,
    29, 26, 30, 28, 29, 34,
    29, 41, 30, 26, 29, 26,
    28, 28, 38, 43, 45, 48,
    42, 38, 43, 41, 26, 28,
    24, 39, 41, 24, 46, 25,
    22, 26, 24, 25
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    37120585653788941, 38480946735527727, 26717286227156201, 44899000773036719, 27235753315982310, 24677757862903935,
    28687741951488152, 26717286227156201, 27235753315982310, 32733642802199278, 27235753315982310, 40479495260532447,
    28687741951488152, 24677757862903935, 27235753315982310, 24677757862903935, 26717286227156201, 26717286227156201,
    34083733414553087, 36738904552803136, 43140487855114806, 42140954510714003, 37750633968992746, 37120585653788941,
    40952991252745407, 39120498347856935, 40952991252745407, 43305227665373859, 28575276648033063, 48717911510136939,
    29093743736964503, 26535748283844474, 30545732372417406, 28575276648033063, 29093743736964503, 34591633223029324,
    29093743736964503, 41303774696414864, 30545732372417406, 26535748283844474, 29093743736964503, 26535748283844474,
    28575276648033063, 28575276648033063, 38915631855249022, 43140487855114806, 45515653563466477, 48516064976393534,
    42149905347247755, 38480946735527727, 43305227665373859, 41480283467855836, 26717286227156201, 28575276648033063,
    24719017698823920, 39120498347856935, 41480283467855836, 24719017698823920, 46897983135878970, 25237484787645657,
    22679489334569110, 26689473423153789, 24719017698823920, 25237484787645657
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
noncomputable def negativeCeiling : ℝ := 76076703 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 168232353901875524108550144, coefficient := (-168232353901875524108550144) }, { argument := 3455484897068556034794061824, coefficient := (-3455484897068556034794061824) }, { argument := 508820134288538917159305216, coefficient := (-508820134288538917159305216) }, { argument := 36935653718088613971416317952, coefficient := (-36935653718088613971416317952) }, { argument := 364425231314764359587069952, coefficient := (-364425231314764359587069952) }, { argument := 61883529845903381816672256, coefficient := (-61883529845903381816672256) }, { argument := 498506212647555020189859840, coefficient := (-498506212647555020189859840) }, { argument := 508820134288538917159305216, coefficient := (-508820134288538917159305216) }, { argument := 364425231314764359587069952, coefficient := (-364425231314764359587069952) }, { argument := 8233947443385477747273891840, coefficient := (-8233947443385477747273891840) }, { argument := 364425231314764359587069952, coefficient := (-364425231314764359587069952) }, { argument := 3452010131028820466056822784, coefficient := (-3452010131028820466056822784) }, { argument := 498506212647555020189859840, coefficient := (-498506212647555020189859840) }, { argument := 61883529845903381816672256, coefficient := (-61883529845903381816672256) }, { argument := 364425231314764359587069952, coefficient := (-364425231314764359587069952) }, { argument := 61883529845903381816672256, coefficient := (-61883529845903381816672256) }, { argument := 508820134288538917159305216, coefficient := (-508820134288538917159305216) }, { argument := 508820134288538917159305216, coefficient := (-508820134288538917159305216) }, { argument := 163989443536779801832456192, coefficient := (-163989443536779801832456192) }, { argument := 64562756714873506687352832, coefficient := (-64562756714873506687352832) }, { argument := 2729107631331709812165574656, coefficient := (-2729107631331709812165574656) }, { argument := 2729990534034991839939919872, coefficient := (-2729990534034991839939919872) }, { argument := 65089805201266644388675584, coefficient := (-65089805201266644388675584) }, { argument := 168232353901875524108550144, coefficient := (-168232353901875524108550144) }, { argument := 599126553100572896052379648, coefficient := (-599126553100572896052379648) }, { argument := 168222173484237080640880640, coefficient := (-168222173484237080640880640) }, { argument := 599126553100572896052379648, coefficient := (-599126553100572896052379648) }, { argument := 12236924472428124163448766464, coefficient := (-12236924472428124163448766464) }, { argument := 1844485037707980477770498048, coefficient := (-1844485037707980477770498048) }, { argument := 130314422122157344305631461376, coefficient := (-130314422122157344305631461376) }, { argument := 1321050094574634666511302656, coefficient := (-1321050094574634666511302656) }, { argument := 224329261342862490539655168, coefficient := (-224329261342862490539655168) }, { argument := 1807096827484170062680555520, coefficient := (-1807096827484170062680555520) }, { argument := 1844485037707980477770498048, coefficient := (-1844485037707980477770498048) }, { argument := 1321050094574634666511302656, coefficient := (-1321050094574634666511302656) }, { argument := 29848254495341981380137451520, coefficient := (-29848254495341981380137451520) }, { argument := 1321050094574634666511302656, coefficient := (-1321050094574634666511302656) }, { argument := 12224606608521124693030207488, coefficient := (-12224606608521124693030207488) }, { argument := 1807096827484170062680555520, coefficient := (-1807096827484170062680555520) }, { argument := 224329261342862490539655168, coefficient := (-224329261342862490539655168) }, { argument := 1321050094574634666511302656, coefficient := (-1321050094574634666511302656) }, { argument := 224329261342862490539655168, coefficient := (-224329261342862490539655168) }, { argument := 1844485037707980477770498048, coefficient := (-1844485037707980477770498048) }, { argument := 1844485037707980477770498048, coefficient := (-1844485037707980477770498048) }, { argument := 583810995333651752745435136, coefficient := (-583810995333651752745435136) }, { argument := 2729107631331709812165574656, coefficient := (-2729107631331709812165574656) }, { argument := 113267880439671321140983234560, coefficient := (-113267880439671321140983234560) }, { argument := 113300185614347190328111398912, coefficient := (-113300185614347190328111398912) }, { argument := 2746980721067564561520918528, coefficient := (-2746980721067564561520918528) }, { argument := 3455484897068556034794061824, coefficient := (-3455484897068556034794061824) }, { argument := 12236924472428124163448766464, coefficient := (-12236924472428124163448766464) }, { argument := 3453896630252214920423669760, coefficient := (-3453896630252214920423669760) }, { argument := 508820134288538917159305216, coefficient := (-508820134288538917159305216) }, { argument := 1844485037707980477770498048, coefficient := (-1844485037707980477770498048) }, { argument := 509431168850922490774421504, coefficient := (-509431168850922490774421504) }, { argument := 168222173484237080640880640, coefficient := (-168222173484237080640880640) }, { argument := 3453896630252214920423669760, coefficient := (-3453896630252214920423669760) }, { argument := 509431168850922490774421504, coefficient := (-509431168850922490774421504) }, { argument := 36909609518583564075838472192, coefficient := (-36909609518583564075838472192) }, { argument := 364862864177012054203301888, coefficient := (-364862864177012054203301888) }, { argument := 61957844860247329959051264, coefficient := (-61957844860247329959051264) }, { argument := 499104861374214602447912960, coefficient := (-499104861374214602447912960) }, { argument := 509431168850922490774421504, coefficient := (-509431168850922490774421504) }, { argument := 364862864177012054203301888, coefficient := (-364862864177012054203301888) }] }

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
def constantNumerator : ℤ := (-27482847676781227201782301589504)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1787596865, 39558511, 1532295181827, 108226115, 6717483, 39558511,
    6717483, 27616319, 27616319, 145639227057, 4849437356631, 402523119242727,
    201318945237585, 9762360785097, 32805450549923, 462969830018371, 131129274615857, 158044251,
    572914153, 39558511, 26837703, 97287309, 6717483, 432385215,
    1567406645, 108226115, 110332779, 399958937, 27616319, 158044251,
    572914153, 39558511, 7141810965, 25889233895, 1787596865, 158044251,
    572914153, 39558511, 231245441289, 4879617991569, 9762360785097, 58275059139,
    1533000451483, 2714407944753, 1532295181827, 432385215, 1567406645, 108226115,
    26837703, 97287309, 6717483, 158044251, 572914153, 39558511,
    26837703, 97287309, 6717483, 110332779, 399958937, 27616319,
    110332779, 399958937, 27616319, 18206485601
  ]
def negativeCoefficients : Array ℕ := #[
    8243835468905130847329320960, 364862864177012054203301888, 3450422004948841807107588096, 499104861374214602447912960, 61957844860247329959051264, 364862864177012054203301888,
    61957844860247329959051264, 509431168850922490774421504, 509431168850922490774421504, 163975192176108064701677568, 2729990534034991839939919872, 113300185614347190328111398912,
    113332490844326137039442411520, 2747860274626199498765893632, 36935653718088613971416317952, 130314422122157344305631461376, 36909609518583564075838472192, 364425231314764359587069952,
    1321050094574634666511302656, 364862864177012054203301888, 61883529845903381816672256, 224329261342862490539655168, 61957844860247329959051264, 498506212647555020189859840,
    1807096827484170062680555520, 499104861374214602447912960, 508820134288538917159305216, 1844485037707980477770498048, 509431168850922490774421504, 364425231314764359587069952,
    1321050094574634666511302656, 364862864177012054203301888, 8233947443385477747273891840, 29848254495341981380137451520, 8243835468905130847329320960, 364425231314764359587069952,
    1321050094574634666511302656, 364862864177012054203301888, 65089805201266644388675584, 2746980721067564561520918528, 2747860274626199498765893632, 65611883655848504365940736,
    3452010131028820466056822784, 12224606608521124693030207488, 3450422004948841807107588096, 498506212647555020189859840, 1807096827484170062680555520, 499104861374214602447912960,
    61883529845903381816672256, 224329261342862490539655168, 61957844860247329959051264, 364425231314764359587069952, 1321050094574634666511302656, 364862864177012054203301888,
    61883529845903381816672256, 224329261342862490539655168, 61957844860247329959051264, 508820134288538917159305216, 1844485037707980477770498048, 509431168850922490774421504,
    508820134288538917159305216, 1844485037707980477770498048, 509431168850922490774421504, 163989443536779801832456192
  ]
def negativeScales : Array ℕ := #[
    30, 25, 40, 26, 22, 25,
    22, 24, 24, 37, 42, 48,
    47, 43, 44, 48, 46, 27,
    29, 25, 24, 26, 22, 28,
    30, 26, 26, 28, 24, 27,
    29, 25, 32, 34, 30, 27,
    29, 25, 37, 42, 43, 35,
    40, 41, 40, 28, 30, 26,
    24, 26, 22, 27, 29, 25,
    24, 26, 22, 26, 28, 24,
    26, 28, 24, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30735374273868805, 25237484787645657, 40478831383911801, 26689473423153789, 22679489334569110, 25237484787645657,
    22679489334569110, 24719017698823920, 24719017698823920, 37083608032940918, 42140954510714003, 48516064976393534,
    47516476272735527, 43150367208680714, 44899000773036719, 48717911510136939, 46897983135878970, 27235753315982310,
    29093743736964503, 25237484787645657, 24677757862903935, 26535748283844474, 22679489334569110, 28687741951488152,
    30545732372417406, 26689473423153789, 26717286227156201, 28575276648033063, 24719017698823920, 27235753315982310,
    29093743736964503, 25237484787645657, 32733642802199278, 34591633223029324, 30735374273868805, 27235753315982310,
    29093743736964503, 25237484787645657, 37750633968992746, 42149905347247755, 43150367208680714, 35762159512604491,
    40479495260532447, 41303774696414864, 40478831383911801, 28687741951488152, 30545732372417406, 26689473423153789,
    24677757862903935, 26535748283844474, 22679489334569110, 27235753315982310, 29093743736964503, 25237484787645657,
    24677757862903935, 26535748283844474, 22679489334569110, 26717286227156201, 28575276648033063, 24719017698823920,
    26717286227156201, 28575276648033063, 24719017698823920, 34083733414553087
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
noncomputable def negativeCeiling : ℝ := 59117027 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 8243835468905130847329320960, coefficient := (-8243835468905130847329320960) }, { argument := 364862864177012054203301888, coefficient := (-364862864177012054203301888) }, { argument := 3450422004948841807107588096, coefficient := (-3450422004948841807107588096) }, { argument := 499104861374214602447912960, coefficient := (-499104861374214602447912960) }, { argument := 61957844860247329959051264, coefficient := (-61957844860247329959051264) }, { argument := 364862864177012054203301888, coefficient := (-364862864177012054203301888) }, { argument := 61957844860247329959051264, coefficient := (-61957844860247329959051264) }, { argument := 509431168850922490774421504, coefficient := (-509431168850922490774421504) }, { argument := 509431168850922490774421504, coefficient := (-509431168850922490774421504) }, { argument := 163975192176108064701677568, coefficient := (-163975192176108064701677568) }, { argument := 2729990534034991839939919872, coefficient := (-2729990534034991839939919872) }, { argument := 113300185614347190328111398912, coefficient := (-113300185614347190328111398912) }, { argument := 113332490844326137039442411520, coefficient := (-113332490844326137039442411520) }, { argument := 2747860274626199498765893632, coefficient := (-2747860274626199498765893632) }, { argument := 36935653718088613971416317952, coefficient := (-36935653718088613971416317952) }, { argument := 130314422122157344305631461376, coefficient := (-130314422122157344305631461376) }, { argument := 36909609518583564075838472192, coefficient := (-36909609518583564075838472192) }, { argument := 364425231314764359587069952, coefficient := (-364425231314764359587069952) }, { argument := 1321050094574634666511302656, coefficient := (-1321050094574634666511302656) }, { argument := 364862864177012054203301888, coefficient := (-364862864177012054203301888) }, { argument := 61883529845903381816672256, coefficient := (-61883529845903381816672256) }, { argument := 224329261342862490539655168, coefficient := (-224329261342862490539655168) }, { argument := 61957844860247329959051264, coefficient := (-61957844860247329959051264) }, { argument := 498506212647555020189859840, coefficient := (-498506212647555020189859840) }, { argument := 1807096827484170062680555520, coefficient := (-1807096827484170062680555520) }, { argument := 499104861374214602447912960, coefficient := (-499104861374214602447912960) }, { argument := 508820134288538917159305216, coefficient := (-508820134288538917159305216) }, { argument := 1844485037707980477770498048, coefficient := (-1844485037707980477770498048) }, { argument := 509431168850922490774421504, coefficient := (-509431168850922490774421504) }, { argument := 364425231314764359587069952, coefficient := (-364425231314764359587069952) }, { argument := 1321050094574634666511302656, coefficient := (-1321050094574634666511302656) }, { argument := 364862864177012054203301888, coefficient := (-364862864177012054203301888) }, { argument := 8233947443385477747273891840, coefficient := (-8233947443385477747273891840) }, { argument := 29848254495341981380137451520, coefficient := (-29848254495341981380137451520) }, { argument := 8243835468905130847329320960, coefficient := (-8243835468905130847329320960) }, { argument := 364425231314764359587069952, coefficient := (-364425231314764359587069952) }, { argument := 1321050094574634666511302656, coefficient := (-1321050094574634666511302656) }, { argument := 364862864177012054203301888, coefficient := (-364862864177012054203301888) }, { argument := 65089805201266644388675584, coefficient := (-65089805201266644388675584) }, { argument := 2746980721067564561520918528, coefficient := (-2746980721067564561520918528) }, { argument := 2747860274626199498765893632, coefficient := (-2747860274626199498765893632) }, { argument := 65611883655848504365940736, coefficient := (-65611883655848504365940736) }, { argument := 3452010131028820466056822784, coefficient := (-3452010131028820466056822784) }, { argument := 12224606608521124693030207488, coefficient := (-12224606608521124693030207488) }, { argument := 3450422004948841807107588096, coefficient := (-3450422004948841807107588096) }, { argument := 498506212647555020189859840, coefficient := (-498506212647555020189859840) }, { argument := 1807096827484170062680555520, coefficient := (-1807096827484170062680555520) }, { argument := 499104861374214602447912960, coefficient := (-499104861374214602447912960) }, { argument := 61883529845903381816672256, coefficient := (-61883529845903381816672256) }, { argument := 224329261342862490539655168, coefficient := (-224329261342862490539655168) }, { argument := 61957844860247329959051264, coefficient := (-61957844860247329959051264) }, { argument := 364425231314764359587069952, coefficient := (-364425231314764359587069952) }, { argument := 1321050094574634666511302656, coefficient := (-1321050094574634666511302656) }, { argument := 364862864177012054203301888, coefficient := (-364862864177012054203301888) }, { argument := 61883529845903381816672256, coefficient := (-61883529845903381816672256) }, { argument := 224329261342862490539655168, coefficient := (-224329261342862490539655168) }, { argument := 61957844860247329959051264, coefficient := (-61957844860247329959051264) }, { argument := 508820134288538917159305216, coefficient := (-508820134288538917159305216) }, { argument := 1844485037707980477770498048, coefficient := (-1844485037707980477770498048) }, { argument := 509431168850922490774421504, coefficient := (-509431168850922490774421504) }, { argument := 508820134288538917159305216, coefficient := (-508820134288538917159305216) }, { argument := 1844485037707980477770498048, coefficient := (-1844485037707980477770498048) }, { argument := 509431168850922490774421504, coefficient := (-509431168850922490774421504) }, { argument := 163989443536779801832456192, coefficient := (-163989443536779801832456192) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk7
