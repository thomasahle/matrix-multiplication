import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
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

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-350714081000415352982201356517376)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    7437, 26335577307, 6765, 248005407999, 70785, 3135,
    496010694951, 3135, 6105, 115335, 6105, 70785,
    115335, 26335577307, 6105, 6105, 6765, 53321563167,
    191659335909, 13333694655, 86229, 2500641, 2213211, 143715,
    86229, 143715, 4397679, 143715, 86229, 70449093,
    4512651, 2500641, 4397679, 143715, 4512651, 143715,
    4397679, 143715, 86229, 4179182079, 4059, 39488111187,
    42471, 1881, 78976203099, 1881, 3663, 69201,
    3663, 42471, 69201, 4179182079, 3663, 3663,
    4059, 140499, 4074471, 3606141, 234165, 140499,
    234165, 7165449, 234165, 140499
  ]
def negativeCoefficients : Array ℕ := #[
    70240479066203102908514304, 30362853413476375177967173632, 2044595792423241591721820160, 1143723072563368169487357444096, 21393453535355381532894167040, 1894991222245931231351930880,
    1143722793447989433197345636352, 1894991222245931231351930880, 1845123032186827777895301120, 69715729702626627932368404480, 1845123032186827777895301120, 21393453535355381532894167040,
    69715729702626627932368404480, 30362853413476375177967173632, 1845123032186827777895301120, 1845123032186827777895301120, 2044595792423241591721820160, 61475576834486672531486932992,
    220968169928153375554544861184, 61490813214443493601176453120, 814409878902733274263584768, 11808943244089632476821979136, 20903186891836820706098675712, 678674899085611061886320640,
    13030558062443732388217356288, 678674899085611061886320640, 20767451912019698493721411584, 21717596770739553980362260480, 13030558062443732388217356288, 332686435531766542536674377728,
    21310391831288187343230468096, 11808943244089632476821979136, 20767451912019698493721411584, 678674899085611061886320640, 21310391831288187343230468096, 678674899085611061886320640,
    20767451912019698493721411584, 21717596770739553980362260480, 814409878902733274263584768, 19273075562186603291178172416, 1226757475453944955033092096, 728427081020776097756523528192,
    12836072121213228919736500224, 1136994733347558738811158528, 728426903240280087380719828992, 1136994733347558738811158528, 1107073819312096666737180672, 41829437821575976759421042688,
    1107073819312096666737180672, 12836072121213228919736500224, 41829437821575976759421042688, 19273075562186603291178172416, 1107073819312096666737180672, 1107073819312096666737180672,
    1226757475453944955033092096, 2653951073906809131516297216, 38482290571648732406986309632, 68118077563608101042251628544, 2211625894922340942930247680, 42463217182508946104260755456,
    2211625894922340942930247680, 67675752384623632853665579008, 70772028637514910173767925760, 42463217182508946104260755456
  ]
def negativeScales : Array ℕ := #[
    12, 34, 12, 37, 16, 11,
    38, 11, 12, 16, 12, 16,
    16, 34, 12, 12, 12, 35,
    37, 33, 16, 21, 21, 17,
    16, 17, 22, 17, 16, 26,
    22, 21, 22, 17, 22, 17,
    22, 17, 16, 31, 11, 35,
    15, 10, 36, 10, 11, 16,
    11, 15, 16, 31, 11, 11,
    11, 17, 21, 21, 17, 17,
    17, 22, 17, 17
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    12860505058921762, 34616294034302436, 12723874218989575, 37851580625869035, 16111156051745362, 11614249727697750,
    38851580273792168, 11614249727697750, 12575775579877617, 16815470860503971, 12575775579877617, 16111156051745362,
    16815470860503971, 34616294034302436, 12575775579877617, 12575775579877617, 12723874218989575, 35634000023767400,
    37479753318662248, 33634357543410234, 16395885528678480, 21253866523806047, 21077709568652220, 17132851122844681,
    16395885528678480, 17132851122844681, 22068310870649970, 17132851122844681, 16395885528678480, 26070077796824158,
    22105543776848946, 21253866523806047, 22068310870649970, 17132851122844681, 22105543776848946, 17132851122844681,
    22068310870649970, 17132851122844681, 16395885528678480, 31960573481937836, 11986908643884053, 35200699310687624,
    15374190457579158, 10877284136413052, 36200698958582276, 10877284136413052, 11838809987105390, 16078505265455047,
    11838809987105390, 15374190457579158, 16078505265455047, 31960573481937836, 11838809987105390, 11838809987105390,
    11986908643884053, 17100200336554366, 21958181343642402, 21782024376973904, 17837165932073584, 17100200336554366,
    17837165932073584, 22772625678891702, 17837165932073584, 17100200336554366
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
noncomputable def negativeCeiling : ℝ := 271689969 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 70240479066203102908514304, coefficient := (-70240479066203102908514304) }, { argument := 30362853413476375177967173632, coefficient := (-30362853413476375177967173632) }, { argument := 2044595792423241591721820160, coefficient := (-2044595792423241591721820160) }, { argument := 1143723072563368169487357444096, coefficient := (-1143723072563368169487357444096) }, { argument := 21393453535355381532894167040, coefficient := (-21393453535355381532894167040) }, { argument := 1894991222245931231351930880, coefficient := (-1894991222245931231351930880) }, { argument := 1143722793447989433197345636352, coefficient := (-1143722793447989433197345636352) }, { argument := 1894991222245931231351930880, coefficient := (-1894991222245931231351930880) }, { argument := 1845123032186827777895301120, coefficient := (-1845123032186827777895301120) }, { argument := 69715729702626627932368404480, coefficient := (-69715729702626627932368404480) }, { argument := 1845123032186827777895301120, coefficient := (-1845123032186827777895301120) }, { argument := 21393453535355381532894167040, coefficient := (-21393453535355381532894167040) }, { argument := 69715729702626627932368404480, coefficient := (-69715729702626627932368404480) }, { argument := 30362853413476375177967173632, coefficient := (-30362853413476375177967173632) }, { argument := 1845123032186827777895301120, coefficient := (-1845123032186827777895301120) }, { argument := 1845123032186827777895301120, coefficient := (-1845123032186827777895301120) }, { argument := 2044595792423241591721820160, coefficient := (-2044595792423241591721820160) }, { argument := 61475576834486672531486932992, coefficient := (-61475576834486672531486932992) }, { argument := 220968169928153375554544861184, coefficient := (-220968169928153375554544861184) }, { argument := 61490813214443493601176453120, coefficient := (-61490813214443493601176453120) }, { argument := 814409878902733274263584768, coefficient := (-814409878902733274263584768) }, { argument := 11808943244089632476821979136, coefficient := (-11808943244089632476821979136) }, { argument := 20903186891836820706098675712, coefficient := (-20903186891836820706098675712) }, { argument := 678674899085611061886320640, coefficient := (-678674899085611061886320640) }, { argument := 13030558062443732388217356288, coefficient := (-13030558062443732388217356288) }, { argument := 678674899085611061886320640, coefficient := (-678674899085611061886320640) }, { argument := 20767451912019698493721411584, coefficient := (-20767451912019698493721411584) }, { argument := 21717596770739553980362260480, coefficient := (-21717596770739553980362260480) }, { argument := 13030558062443732388217356288, coefficient := (-13030558062443732388217356288) }, { argument := 332686435531766542536674377728, coefficient := (-332686435531766542536674377728) }, { argument := 21310391831288187343230468096, coefficient := (-21310391831288187343230468096) }, { argument := 11808943244089632476821979136, coefficient := (-11808943244089632476821979136) }, { argument := 20767451912019698493721411584, coefficient := (-20767451912019698493721411584) }, { argument := 678674899085611061886320640, coefficient := (-678674899085611061886320640) }, { argument := 21310391831288187343230468096, coefficient := (-21310391831288187343230468096) }, { argument := 678674899085611061886320640, coefficient := (-678674899085611061886320640) }, { argument := 20767451912019698493721411584, coefficient := (-20767451912019698493721411584) }, { argument := 21717596770739553980362260480, coefficient := (-21717596770739553980362260480) }, { argument := 814409878902733274263584768, coefficient := (-814409878902733274263584768) }, { argument := 19273075562186603291178172416, coefficient := (-19273075562186603291178172416) }, { argument := 1226757475453944955033092096, coefficient := (-1226757475453944955033092096) }, { argument := 728427081020776097756523528192, coefficient := (-728427081020776097756523528192) }, { argument := 12836072121213228919736500224, coefficient := (-12836072121213228919736500224) }, { argument := 1136994733347558738811158528, coefficient := (-1136994733347558738811158528) }, { argument := 728426903240280087380719828992, coefficient := (-728426903240280087380719828992) }, { argument := 1136994733347558738811158528, coefficient := (-1136994733347558738811158528) }, { argument := 1107073819312096666737180672, coefficient := (-1107073819312096666737180672) }, { argument := 41829437821575976759421042688, coefficient := (-41829437821575976759421042688) }, { argument := 1107073819312096666737180672, coefficient := (-1107073819312096666737180672) }, { argument := 12836072121213228919736500224, coefficient := (-12836072121213228919736500224) }, { argument := 41829437821575976759421042688, coefficient := (-41829437821575976759421042688) }, { argument := 19273075562186603291178172416, coefficient := (-19273075562186603291178172416) }, { argument := 1107073819312096666737180672, coefficient := (-1107073819312096666737180672) }, { argument := 1107073819312096666737180672, coefficient := (-1107073819312096666737180672) }, { argument := 1226757475453944955033092096, coefficient := (-1226757475453944955033092096) }, { argument := 2653951073906809131516297216, coefficient := (-2653951073906809131516297216) }, { argument := 38482290571648732406986309632, coefficient := (-38482290571648732406986309632) }, { argument := 68118077563608101042251628544, coefficient := (-68118077563608101042251628544) }, { argument := 2211625894922340942930247680, coefficient := (-2211625894922340942930247680) }, { argument := 42463217182508946104260755456, coefficient := (-42463217182508946104260755456) }, { argument := 2211625894922340942930247680, coefficient := (-2211625894922340942930247680) }, { argument := 67675752384623632853665579008, coefficient := (-67675752384623632853665579008) }, { argument := 70772028637514910173767925760, coefficient := (-70772028637514910173767925760) }, { argument := 42463217182508946104260755456, coefficient := (-42463217182508946104260755456) }] }

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


end Parent2

namespace Parent2

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4406467471647454797726848343080960)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    114787683, 7352781, 4074471, 7165449, 234165, 7352781,
    234165, 7165449, 234165, 140499, 406262060529, 3316203,
    3827457899229, 34698807, 1536777, 7654913930325, 1536777, 2992671,
    56537217, 2992671, 34698807, 56537217, 406262060529, 2992671,
    2992671, 3316203, 44619958033, 2566119453621, 714096253755, 25990732077,
    212421, 244844023401, 2222649, 98439, 489687927297, 98439,
    191697, 3621519, 191697, 2222649, 3621519, 25990732077,
    191697, 191697, 212421, 1254593052821, 1127472598713, 1254902400135,
    101023994101, 101024018187, 1966990879041, 1294021706897355, 12905431133, 52200704881323357,
    4080370523, 485890233, 12900491357, 25716409127, 4080370523, 396703664725,
    25379309569, 5176095732443991, 12900491357, 485890233
  ]
def negativeCoefficients : Array ℕ := #[
    1084139013690931530224407412736, 69445053100561505608009777152, 38482290571648732406986309632, 67675752384623632853665579008, 2211625894922340942930247680, 69445053100561505608009777152,
    2211625894922340942930247680, 67675752384623632853665579008, 70772028637514910173767925760, 2653951073906809131516297216, 468388266089772618511552610304, 31320651795183532133188632576,
    17651034079993841489321725526016, 327720966344725250857022521344, 29028896785779859050272391168, 17651029772372423157916001894400, 29028896785779859050272391168, 28264978449311968022633644032,
    1067957834382111656638968496128, 28264978449311968022633644032, 327720966344725250857022521344, 1067957834382111656638968496128, 468388266089772618511552610304, 28264978449311968022633644032,
    28264978449311968022633644032, 31320651795183532133188632576, 823092946414411651737167331328, 2958534301469623396468676100096, 823296927313327399684150394880, 29965273932048280972953649152,
    2006259621315305811877036032, 1129143759413899881186280341504, 20992326281567468129152401408, 1859460136828820020764082176, 1129143483854131065103784607744, 1859460136828820020764082176,
    1810526975333324757059764224, 68408559770702378658636496896, 1810526975333324757059764224, 20992326281567468129152401408, 68408559770702378658636496896, 29965273932048280972953649152,
    1810526975333324757059764224, 1810526975333324757059764224, 2006259621315305811877036032, 1446447310127684762999032119296, 5199549619644735045615382167552, 1446803963298387729737066741760,
    232945470560636306455267377152, 232945526099171026376299905024, 8858539389890211970428174336, 1456938919248065292901306859520, 29757898158916811778074607616, 14693192190750318887956163592192,
    18817387690922348419368353792, 1120386597008262901127970816, 29746507810960130193819172864, 29649001103786092120298749952, 18817387690922348419368353792, 457368186017797165706484121600,
    29260351774174429040915513344, 1456941425741798276904932868096, 29746507810960130193819172864, 1120386597008262901127970816
  ]
def negativeScales : Array ℕ := #[
    26, 22, 21, 22, 17, 22,
    17, 22, 17, 17, 38, 21,
    41, 25, 20, 42, 20, 21,
    25, 21, 25, 25, 38, 21,
    21, 21, 35, 41, 39, 34,
    17, 37, 21, 16, 38, 16,
    17, 21, 17, 21, 21, 34,
    17, 17, 17, 40, 40, 40,
    36, 36, 40, 50, 33, 55,
    31, 28, 33, 34, 31, 38,
    34, 52, 33, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    26774392605079814, 22809858585513638, 21958181343642402, 22772625678891702, 17837165932073584, 22809858585513638,
    17837165932073584, 22772625678891702, 17837165932073584, 17100200336554366, 38563619686101244, 21661100892871566,
    41799523647932183, 25048382725724839, 20551476401670270, 42799523295851684, 20551476401670270, 21513002253854659,
    25752697533839239, 21513002253854659, 25048382725724839, 25752697533839239, 38563619686101244, 21513002253854659,
    21513002253854659, 21661100892871566, 35376970105539247, 41222725468520778, 39377327593443544, 34597278219433225,
    17696566872934922, 37833072025557896, 21083848705749627, 16586942381697590, 38833071673478042, 16586942381697590,
    17548468233880300, 21788163514132048, 17548468233880300, 21083848705749627, 21788163514132048, 34597278219433225,
    17548468233880300, 17548468233880300, 17696566872934922, 40190356617657490, 40036229510327462, 40190712301775231,
    36555907030396803, 36555907374362105, 40839127407892487, 50200783241699978, 33587259287368857, 55534918806256699,
    31926053024723458, 28856055193818461, 33586706965286289, 34581970157003975, 31926053024723458, 38529270768837930,
    34562933770815492, 52200785723686642, 33586706965286289, 28856055193818461
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
noncomputable def negativeCeiling : ℝ := 39126581351 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1084139013690931530224407412736, coefficient := (-1084139013690931530224407412736) }, { argument := 69445053100561505608009777152, coefficient := (-69445053100561505608009777152) }, { argument := 38482290571648732406986309632, coefficient := (-38482290571648732406986309632) }, { argument := 67675752384623632853665579008, coefficient := (-67675752384623632853665579008) }, { argument := 2211625894922340942930247680, coefficient := (-2211625894922340942930247680) }, { argument := 69445053100561505608009777152, coefficient := (-69445053100561505608009777152) }, { argument := 2211625894922340942930247680, coefficient := (-2211625894922340942930247680) }, { argument := 67675752384623632853665579008, coefficient := (-67675752384623632853665579008) }, { argument := 70772028637514910173767925760, coefficient := (-70772028637514910173767925760) }, { argument := 2653951073906809131516297216, coefficient := (-2653951073906809131516297216) }, { argument := 468388266089772618511552610304, coefficient := (-468388266089772618511552610304) }, { argument := 31320651795183532133188632576, coefficient := (-31320651795183532133188632576) }, { argument := 17651034079993841489321725526016, coefficient := (-17651034079993841489321725526016) }, { argument := 327720966344725250857022521344, coefficient := (-327720966344725250857022521344) }, { argument := 29028896785779859050272391168, coefficient := (-29028896785779859050272391168) }, { argument := 17651029772372423157916001894400, coefficient := (-17651029772372423157916001894400) }, { argument := 29028896785779859050272391168, coefficient := (-29028896785779859050272391168) }, { argument := 28264978449311968022633644032, coefficient := (-28264978449311968022633644032) }, { argument := 1067957834382111656638968496128, coefficient := (-1067957834382111656638968496128) }, { argument := 28264978449311968022633644032, coefficient := (-28264978449311968022633644032) }, { argument := 327720966344725250857022521344, coefficient := (-327720966344725250857022521344) }, { argument := 1067957834382111656638968496128, coefficient := (-1067957834382111656638968496128) }, { argument := 468388266089772618511552610304, coefficient := (-468388266089772618511552610304) }, { argument := 28264978449311968022633644032, coefficient := (-28264978449311968022633644032) }, { argument := 28264978449311968022633644032, coefficient := (-28264978449311968022633644032) }, { argument := 31320651795183532133188632576, coefficient := (-31320651795183532133188632576) }, { argument := 823092946414411651737167331328, coefficient := (-823092946414411651737167331328) }, { argument := 2958534301469623396468676100096, coefficient := (-2958534301469623396468676100096) }, { argument := 823296927313327399684150394880, coefficient := (-823296927313327399684150394880) }, { argument := 29965273932048280972953649152, coefficient := (-29965273932048280972953649152) }, { argument := 2006259621315305811877036032, coefficient := (-2006259621315305811877036032) }, { argument := 1129143759413899881186280341504, coefficient := (-1129143759413899881186280341504) }, { argument := 20992326281567468129152401408, coefficient := (-20992326281567468129152401408) }, { argument := 1859460136828820020764082176, coefficient := (-1859460136828820020764082176) }, { argument := 1129143483854131065103784607744, coefficient := (-1129143483854131065103784607744) }, { argument := 1859460136828820020764082176, coefficient := (-1859460136828820020764082176) }, { argument := 1810526975333324757059764224, coefficient := (-1810526975333324757059764224) }, { argument := 68408559770702378658636496896, coefficient := (-68408559770702378658636496896) }, { argument := 1810526975333324757059764224, coefficient := (-1810526975333324757059764224) }, { argument := 20992326281567468129152401408, coefficient := (-20992326281567468129152401408) }, { argument := 68408559770702378658636496896, coefficient := (-68408559770702378658636496896) }, { argument := 29965273932048280972953649152, coefficient := (-29965273932048280972953649152) }, { argument := 1810526975333324757059764224, coefficient := (-1810526975333324757059764224) }, { argument := 1810526975333324757059764224, coefficient := (-1810526975333324757059764224) }, { argument := 2006259621315305811877036032, coefficient := (-2006259621315305811877036032) }, { argument := 1446447310127684762999032119296, coefficient := (-1446447310127684762999032119296) }, { argument := 5199549619644735045615382167552, coefficient := (-5199549619644735045615382167552) }, { argument := 1446803963298387729737066741760, coefficient := (-1446803963298387729737066741760) }, { argument := 232945470560636306455267377152, coefficient := (-232945470560636306455267377152) }, { argument := 232945526099171026376299905024, coefficient := (-232945526099171026376299905024) }, { argument := 8858539389890211970428174336, coefficient := (-8858539389890211970428174336) }, { argument := 1456938919248065292901306859520, coefficient := (-1456938919248065292901306859520) }, { argument := 29757898158916811778074607616, coefficient := (-29757898158916811778074607616) }, { argument := 14693192190750318887956163592192, coefficient := (-14693192190750318887956163592192) }, { argument := 18817387690922348419368353792, coefficient := (-18817387690922348419368353792) }, { argument := 1120386597008262901127970816, coefficient := (-1120386597008262901127970816) }, { argument := 29746507810960130193819172864, coefficient := (-29746507810960130193819172864) }, { argument := 29649001103786092120298749952, coefficient := (-29649001103786092120298749952) }, { argument := 18817387690922348419368353792, coefficient := (-18817387690922348419368353792) }, { argument := 457368186017797165706484121600, coefficient := (-457368186017797165706484121600) }, { argument := 29260351774174429040915513344, coefficient := (-29260351774174429040915513344) }, { argument := 1456941425741798276904932868096, coefficient := (-1456941425741798276904932868096) }, { argument := 29746507810960130193819172864, coefficient := (-29746507810960130193819172864) }, { argument := 1120386597008262901127970816, coefficient := (-1120386597008262901127970816) }] }

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

end TermShard7


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13
