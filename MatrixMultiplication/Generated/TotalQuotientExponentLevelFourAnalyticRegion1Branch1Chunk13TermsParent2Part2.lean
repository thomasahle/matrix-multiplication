import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 13, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3221169573629551824721376612188160)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    6365, 3819, 6365, 194769, 6365, 3819,
    3120123, 199861, 110751, 194769, 6365, 199861,
    6365, 194769, 6365, 3819, 4179182079, 4059,
    39488111187, 42471, 1881, 78976203099, 1881, 3663,
    69201, 3663, 42471, 69201, 4179182079, 3663,
    3663, 4059, 40223664991694005, 147223929676309741, 20109584788617007, 497803653,
    6765, 4737751521, 70785, 3135, 9475500729, 3135,
    6105, 115335, 6105, 70785, 115335, 497803653,
    6105, 6105, 6765, 20657384717, 148499917233, 41325018165,
    132474507425855, 132474492094401, 7437, 215673, 190883, 12395,
    7437, 12395, 379287, 12395
  ]
def negativeCoefficients : Array ℕ := #[
    60115725326930583570350080, 1154221926277067204550721536, 60115725326930583570350080, 1839541195004075857252712448, 1923703210461778674251202560, 1154221926277067204550721536,
    29468728555261372066185609216, 1887633775265620324108992512, 1046013620688592154124091392, 1839541195004075857252712448, 60115725326930583570350080, 1887633775265620324108992512,
    60115725326930583570350080, 1839541195004075857252712448, 1923703210461778674251202560, 72138870392316700284420096, 19273075562186603291178172416, 1226757475453944955033092096,
    728427081020776097756523528192, 12836072121213228919736500224, 1136994733347558738811158528, 728426903240280087380719828992, 1136994733347558738811158528, 1107073819312096666737180672,
    41829437821575976759421042688, 1107073819312096666737180672, 12836072121213228919736500224, 41829437821575976759421042688, 19273075562186603291178172416, 1107073819312096666737180672,
    1107073819312096666737180672, 1226757475453944955033092096, 11321955166754299125056174817280, 41439852176890541084588791300096, 11320689820073868412112479453184, 1147857073231089506929606656,
    63893618513226299741306880, 43698044896357582140466003968, 668545422979855672902942720, 59218475695185350979747840, 43698034229527821517917782016, 59218475695185350979747840,
    57660094755838368059228160, 2178616553207082122886512640, 57660094755838368059228160, 668545422979855672902942720, 2178616553207082122886512640, 1147857073231089506929606656,
    57660094755838368059228160, 57660094755838368059228160, 63893618513226299741306880, 47632686138332251631160131584, 171208748010262604141096337408, 47644502120697082466575319040,
    37288258892448161453708410880, 37288254577027503863214637056, 70240479066203102908514304, 1018486946459944992173457408, 1802838962699212974651867136, 58533732555169252423761920,
    1123847665059249646536228864, 58533732555169252423761920, 1791132216188179124167114752, 1873079441765416077560381440
  ]
def negativeScales : Array ℕ := #[
    12, 11, 12, 17, 12, 11,
    21, 17, 16, 17, 12, 17,
    12, 17, 12, 11, 31, 11,
    35, 15, 10, 36, 10, 11,
    16, 11, 15, 16, 31, 11,
    11, 11, 55, 57, 54, 28,
    12, 32, 16, 11, 33, 11,
    12, 16, 12, 16, 16, 28,
    12, 12, 12, 34, 37, 35,
    46, 46, 12, 17, 17, 13,
    12, 13, 18, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    12635944798803559, 11898979208910875, 12635944798803559, 17571404546596521, 12635944798803559, 11898979208910875,
    21573171472770842, 17608637452800154, 16756960200011716, 17571404546596521, 12635944798803559, 17608637452800154,
    12635944798803559, 17571404546596521, 12635944798803559, 11898979208910875, 31960573481937836, 11986908643884053,
    35200699310687624, 15374190457579158, 10877284136413052, 36200698958582276, 10877284136413052, 11838809987105390,
    16078505265455047, 11838809987105390, 15374190457579158, 16078505265455047, 31960573481937836, 11838809987105390,
    11838809987105390, 11986908643884053, 55158894057435543, 57030789798199512, 54158732812193760, 28891001580004972,
    12723874218989575, 32141555390086268, 16111156051745362, 11614249727697750, 33141555037919843, 11614249727697750,
    12575775579877617, 16815470860503971, 12575775579877617, 16111156051745362, 16815470860503971, 28891001580004972,
    12575775579877617, 12575775579877617, 12723874218989575, 34265938565388103, 37111671170695622, 35266296402548495,
    46912708096980206, 46912707930015131, 12860505058921762, 17718486052046604, 17542329096782676, 13597470650979357,
    12860505058921762, 13597470650979357, 18532930398780161, 13597470650979357
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
noncomputable def negativeCeiling : ℝ := 22107652817 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 60115725326930583570350080, coefficient := (-60115725326930583570350080) }, { argument := 1154221926277067204550721536, coefficient := (-1154221926277067204550721536) }, { argument := 60115725326930583570350080, coefficient := (-60115725326930583570350080) }, { argument := 1839541195004075857252712448, coefficient := (-1839541195004075857252712448) }, { argument := 1923703210461778674251202560, coefficient := (-1923703210461778674251202560) }, { argument := 1154221926277067204550721536, coefficient := (-1154221926277067204550721536) }, { argument := 29468728555261372066185609216, coefficient := (-29468728555261372066185609216) }, { argument := 1887633775265620324108992512, coefficient := (-1887633775265620324108992512) }, { argument := 1046013620688592154124091392, coefficient := (-1046013620688592154124091392) }, { argument := 1839541195004075857252712448, coefficient := (-1839541195004075857252712448) }, { argument := 60115725326930583570350080, coefficient := (-60115725326930583570350080) }, { argument := 1887633775265620324108992512, coefficient := (-1887633775265620324108992512) }, { argument := 60115725326930583570350080, coefficient := (-60115725326930583570350080) }, { argument := 1839541195004075857252712448, coefficient := (-1839541195004075857252712448) }, { argument := 1923703210461778674251202560, coefficient := (-1923703210461778674251202560) }, { argument := 72138870392316700284420096, coefficient := (-72138870392316700284420096) }, { argument := 19273075562186603291178172416, coefficient := (-19273075562186603291178172416) }, { argument := 1226757475453944955033092096, coefficient := (-1226757475453944955033092096) }, { argument := 728427081020776097756523528192, coefficient := (-728427081020776097756523528192) }, { argument := 12836072121213228919736500224, coefficient := (-12836072121213228919736500224) }, { argument := 1136994733347558738811158528, coefficient := (-1136994733347558738811158528) }, { argument := 728426903240280087380719828992, coefficient := (-728426903240280087380719828992) }, { argument := 1136994733347558738811158528, coefficient := (-1136994733347558738811158528) }, { argument := 1107073819312096666737180672, coefficient := (-1107073819312096666737180672) }, { argument := 41829437821575976759421042688, coefficient := (-41829437821575976759421042688) }, { argument := 1107073819312096666737180672, coefficient := (-1107073819312096666737180672) }, { argument := 12836072121213228919736500224, coefficient := (-12836072121213228919736500224) }, { argument := 41829437821575976759421042688, coefficient := (-41829437821575976759421042688) }, { argument := 19273075562186603291178172416, coefficient := (-19273075562186603291178172416) }, { argument := 1107073819312096666737180672, coefficient := (-1107073819312096666737180672) }, { argument := 1107073819312096666737180672, coefficient := (-1107073819312096666737180672) }, { argument := 1226757475453944955033092096, coefficient := (-1226757475453944955033092096) }, { argument := 11321955166754299125056174817280, coefficient := (-11321955166754299125056174817280) }, { argument := 41439852176890541084588791300096, coefficient := (-41439852176890541084588791300096) }, { argument := 11320689820073868412112479453184, coefficient := (-11320689820073868412112479453184) }, { argument := 1147857073231089506929606656, coefficient := (-1147857073231089506929606656) }, { argument := 63893618513226299741306880, coefficient := (-63893618513226299741306880) }, { argument := 43698044896357582140466003968, coefficient := (-43698044896357582140466003968) }, { argument := 668545422979855672902942720, coefficient := (-668545422979855672902942720) }, { argument := 59218475695185350979747840, coefficient := (-59218475695185350979747840) }, { argument := 43698034229527821517917782016, coefficient := (-43698034229527821517917782016) }, { argument := 59218475695185350979747840, coefficient := (-59218475695185350979747840) }, { argument := 57660094755838368059228160, coefficient := (-57660094755838368059228160) }, { argument := 2178616553207082122886512640, coefficient := (-2178616553207082122886512640) }, { argument := 57660094755838368059228160, coefficient := (-57660094755838368059228160) }, { argument := 668545422979855672902942720, coefficient := (-668545422979855672902942720) }, { argument := 2178616553207082122886512640, coefficient := (-2178616553207082122886512640) }, { argument := 1147857073231089506929606656, coefficient := (-1147857073231089506929606656) }, { argument := 57660094755838368059228160, coefficient := (-57660094755838368059228160) }, { argument := 57660094755838368059228160, coefficient := (-57660094755838368059228160) }, { argument := 63893618513226299741306880, coefficient := (-63893618513226299741306880) }, { argument := 47632686138332251631160131584, coefficient := (-47632686138332251631160131584) }, { argument := 171208748010262604141096337408, coefficient := (-171208748010262604141096337408) }, { argument := 47644502120697082466575319040, coefficient := (-47644502120697082466575319040) }, { argument := 37288258892448161453708410880, coefficient := (-37288258892448161453708410880) }, { argument := 37288254577027503863214637056, coefficient := (-37288254577027503863214637056) }, { argument := 70240479066203102908514304, coefficient := (-70240479066203102908514304) }, { argument := 1018486946459944992173457408, coefficient := (-1018486946459944992173457408) }, { argument := 1802838962699212974651867136, coefficient := (-1802838962699212974651867136) }, { argument := 58533732555169252423761920, coefficient := (-58533732555169252423761920) }, { argument := 1123847665059249646536228864, coefficient := (-1123847665059249646536228864) }, { argument := 58533732555169252423761920, coefficient := (-58533732555169252423761920) }, { argument := 1791132216188179124167114752, coefficient := (-1791132216188179124167114752) }, { argument := 1873079441765416077560381440, coefficient := (-1873079441765416077560381440) }] }

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

end TermShard4


end Parent2

namespace Parent2

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-301354961738349874718646892232704)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    7437, 6076029, 389203, 215673, 379287, 12395,
    389203, 12395, 379287, 12395, 7437, 140499,
    4074471, 3606141, 234165, 140499, 234165, 7165449,
    234165, 140499, 114787683, 7352781, 4074471, 7165449,
    234165, 7352781, 234165, 7165449, 234165, 140499,
    13212638553, 207009, 124783858725, 2166021, 95931, 249567656541,
    95931, 186813, 3529251, 186813, 2166021, 3529251,
    13212638553, 186813, 186813, 207009, 7437, 215673,
    190883, 12395, 7437, 12395, 379287, 12395,
    7437, 6076029, 389203, 215673, 379287, 12395,
    389203, 12395, 379287, 12395
  ]
def negativeCoefficients : Array ℕ := #[
    1123847665059249646536228864, 28693235698543967538128093184, 1837959202232314526106124288, 1018486946459944992173457408, 1791132216188179124167114752, 58533732555169252423761920,
    1837959202232314526106124288, 58533732555169252423761920, 1791132216188179124167114752, 1873079441765416077560381440, 70240479066203102908514304, 2653951073906809131516297216,
    38482290571648732406986309632, 68118077563608101042251628544, 2211625894922340942930247680, 42463217182508946104260755456, 2211625894922340942930247680, 67675752384623632853665579008,
    70772028637514910173767925760, 42463217182508946104260755456, 1084139013690931530224407412736, 69445053100561505608009777152, 38482290571648732406986309632, 67675752384623632853665579008,
    2211625894922340942930247680, 69445053100561505608009777152, 2211625894922340942930247680, 67675752384623632853665579008, 70772028637514910173767925760, 2653951073906809131516297216,
    30466270240702386925738131456, 1955144726504724772083990528, 1150927953215001837767019724800, 20457489943183583590830047232, 1812085356272671739980283904, 1150927672321818141373249880064,
    1812085356272671739980283904, 1764398899528654062612381696, 66665666528136712960327286784, 1764398899528654062612381696, 20457489943183583590830047232, 66665666528136712960327286784,
    30466270240702386925738131456, 1764398899528654062612381696, 1764398899528654062612381696, 1955144726504724772083990528, 70240479066203102908514304, 1018486946459944992173457408,
    1802838962699212974651867136, 58533732555169252423761920, 1123847665059249646536228864, 58533732555169252423761920, 1791132216188179124167114752, 1873079441765416077560381440,
    1123847665059249646536228864, 28693235698543967538128093184, 1837959202232314526106124288, 1018486946459944992173457408, 1791132216188179124167114752, 58533732555169252423761920,
    1837959202232314526106124288, 58533732555169252423761920, 1791132216188179124167114752, 1873079441765416077560381440
  ]
def negativeScales : Array ℕ := #[
    12, 22, 18, 17, 18, 13,
    18, 13, 18, 13, 12, 17,
    21, 21, 17, 17, 17, 22,
    17, 17, 26, 22, 21, 22,
    17, 22, 17, 22, 17, 17,
    33, 17, 36, 21, 16, 37,
    16, 17, 21, 17, 21, 21,
    33, 17, 17, 17, 12, 17,
    17, 13, 12, 13, 18, 13,
    12, 22, 18, 17, 18, 13,
    18, 13, 18, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    12860505058921762, 22534697324954393, 18570163304980772, 17718486052046604, 18532930398780161, 13597470650979357,
    18570163304980772, 13597470650979357, 18532930398780161, 13597470650979357, 12860505058921762, 17100200336554366,
    21958181343642402, 21782024376973904, 17837165932073584, 17100200336554366, 17837165932073584, 22772625678891702,
    17837165932073584, 17100200336554366, 26774392605079814, 22809858585513638, 21958181343642402, 22772625678891702,
    17837165932073584, 22809858585513638, 17837165932073584, 22772625678891702, 17837165932073584, 17100200336554366,
    33621199549246831, 17659333966696159, 36860640373962964, 21046615799550651, 16549709475496009, 37860640021861630,
    16549709475496009, 17511235327680448, 21750930607656040, 17511235327680448, 21046615799550651, 21750930607656040,
    33621199549246831, 17511235327680448, 17511235327680448, 17659333966696159, 12860505058921762, 17718486052046604,
    17542329096782676, 13597470650979357, 12860505058921762, 13597470650979357, 18532930398780161, 13597470650979357,
    12860505058921762, 22534697324954393, 18570163304980772, 17718486052046604, 18532930398780161, 13597470650979357,
    18570163304980772, 13597470650979357, 18532930398780161, 13597470650979357
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
noncomputable def negativeCeiling : ℝ := 207770309 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1123847665059249646536228864, coefficient := (-1123847665059249646536228864) }, { argument := 28693235698543967538128093184, coefficient := (-28693235698543967538128093184) }, { argument := 1837959202232314526106124288, coefficient := (-1837959202232314526106124288) }, { argument := 1018486946459944992173457408, coefficient := (-1018486946459944992173457408) }, { argument := 1791132216188179124167114752, coefficient := (-1791132216188179124167114752) }, { argument := 58533732555169252423761920, coefficient := (-58533732555169252423761920) }, { argument := 1837959202232314526106124288, coefficient := (-1837959202232314526106124288) }, { argument := 58533732555169252423761920, coefficient := (-58533732555169252423761920) }, { argument := 1791132216188179124167114752, coefficient := (-1791132216188179124167114752) }, { argument := 1873079441765416077560381440, coefficient := (-1873079441765416077560381440) }, { argument := 70240479066203102908514304, coefficient := (-70240479066203102908514304) }, { argument := 2653951073906809131516297216, coefficient := (-2653951073906809131516297216) }, { argument := 38482290571648732406986309632, coefficient := (-38482290571648732406986309632) }, { argument := 68118077563608101042251628544, coefficient := (-68118077563608101042251628544) }, { argument := 2211625894922340942930247680, coefficient := (-2211625894922340942930247680) }, { argument := 42463217182508946104260755456, coefficient := (-42463217182508946104260755456) }, { argument := 2211625894922340942930247680, coefficient := (-2211625894922340942930247680) }, { argument := 67675752384623632853665579008, coefficient := (-67675752384623632853665579008) }, { argument := 70772028637514910173767925760, coefficient := (-70772028637514910173767925760) }, { argument := 42463217182508946104260755456, coefficient := (-42463217182508946104260755456) }, { argument := 1084139013690931530224407412736, coefficient := (-1084139013690931530224407412736) }, { argument := 69445053100561505608009777152, coefficient := (-69445053100561505608009777152) }, { argument := 38482290571648732406986309632, coefficient := (-38482290571648732406986309632) }, { argument := 67675752384623632853665579008, coefficient := (-67675752384623632853665579008) }, { argument := 2211625894922340942930247680, coefficient := (-2211625894922340942930247680) }, { argument := 69445053100561505608009777152, coefficient := (-69445053100561505608009777152) }, { argument := 2211625894922340942930247680, coefficient := (-2211625894922340942930247680) }, { argument := 67675752384623632853665579008, coefficient := (-67675752384623632853665579008) }, { argument := 70772028637514910173767925760, coefficient := (-70772028637514910173767925760) }, { argument := 2653951073906809131516297216, coefficient := (-2653951073906809131516297216) }, { argument := 30466270240702386925738131456, coefficient := (-30466270240702386925738131456) }, { argument := 1955144726504724772083990528, coefficient := (-1955144726504724772083990528) }, { argument := 1150927953215001837767019724800, coefficient := (-1150927953215001837767019724800) }, { argument := 20457489943183583590830047232, coefficient := (-20457489943183583590830047232) }, { argument := 1812085356272671739980283904, coefficient := (-1812085356272671739980283904) }, { argument := 1150927672321818141373249880064, coefficient := (-1150927672321818141373249880064) }, { argument := 1812085356272671739980283904, coefficient := (-1812085356272671739980283904) }, { argument := 1764398899528654062612381696, coefficient := (-1764398899528654062612381696) }, { argument := 66665666528136712960327286784, coefficient := (-66665666528136712960327286784) }, { argument := 1764398899528654062612381696, coefficient := (-1764398899528654062612381696) }, { argument := 20457489943183583590830047232, coefficient := (-20457489943183583590830047232) }, { argument := 66665666528136712960327286784, coefficient := (-66665666528136712960327286784) }, { argument := 30466270240702386925738131456, coefficient := (-30466270240702386925738131456) }, { argument := 1764398899528654062612381696, coefficient := (-1764398899528654062612381696) }, { argument := 1764398899528654062612381696, coefficient := (-1764398899528654062612381696) }, { argument := 1955144726504724772083990528, coefficient := (-1955144726504724772083990528) }, { argument := 70240479066203102908514304, coefficient := (-70240479066203102908514304) }, { argument := 1018486946459944992173457408, coefficient := (-1018486946459944992173457408) }, { argument := 1802838962699212974651867136, coefficient := (-1802838962699212974651867136) }, { argument := 58533732555169252423761920, coefficient := (-58533732555169252423761920) }, { argument := 1123847665059249646536228864, coefficient := (-1123847665059249646536228864) }, { argument := 58533732555169252423761920, coefficient := (-58533732555169252423761920) }, { argument := 1791132216188179124167114752, coefficient := (-1791132216188179124167114752) }, { argument := 1873079441765416077560381440, coefficient := (-1873079441765416077560381440) }, { argument := 1123847665059249646536228864, coefficient := (-1123847665059249646536228864) }, { argument := 28693235698543967538128093184, coefficient := (-28693235698543967538128093184) }, { argument := 1837959202232314526106124288, coefficient := (-1837959202232314526106124288) }, { argument := 1018486946459944992173457408, coefficient := (-1018486946459944992173457408) }, { argument := 1791132216188179124167114752, coefficient := (-1791132216188179124167114752) }, { argument := 58533732555169252423761920, coefficient := (-58533732555169252423761920) }, { argument := 1837959202232314526106124288, coefficient := (-1837959202232314526106124288) }, { argument := 58533732555169252423761920, coefficient := (-58533732555169252423761920) }, { argument := 1791132216188179124167114752, coefficient := (-1791132216188179124167114752) }, { argument := 1873079441765416077560381440, coefficient := (-1873079441765416077560381440) }] }

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

end TermShard5


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13
