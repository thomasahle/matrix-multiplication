import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 9, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk9

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
def constantNumerator : ℤ := (-41331728759371839454000711729152)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    656675360461, 17462269632733, 52729529, 174374293465805, 46526055, 15508685,
    412531021, 52729529, 46526055, 7515508751, 46526055, 17449755279931,
    412531021, 15508685, 46526055, 15508685, 52729529, 52729529,
    328308459943, 249502324065, 4579725117095, 18320848433095, 497071786715, 656675360461,
    2258589036089, 328377942397, 2258589036089, 60211781837017, 179753529, 601963612932681,
    158606055, 52868685, 1406307021, 179753529, 158606055, 25620164751,
    158606055, 60169131231231, 1406307021, 52868685, 158606055, 52868685,
    179753529, 179753529, 1129193580371, 4579725117095, 10414845826175, 83326864536885,
    4563651315455, 17462269632733, 60211781837017, 8732496920357, 52729529, 179753529,
    26364807, 328377942397, 8732496920357, 26364807, 87202129151349, 23263065,
    7754355, 206265843, 26364807, 23263065
  ]
def negativeCoefficients : Array ℕ := #[
    184837681792221608899772416, 4915191938188716677527502848, 486344063295122969756434432, 49082000192224557092915118080, 429127114672167326255677440, 71521185778694554375946240,
    475615885428318786600042496, 486344063295122969756434432, 429127114672167326255677440, 8664791657088845262645886976, 429127114672167326255677440, 4911669461025224794870644736,
    475615885428318786600042496, 71521185778694554375946240, 429127114672167326255677440, 71521185778694554375946240, 486344063295122969756434432, 486344063295122969756434432,
    184821232232734526554505216, 140457321710900842101473280, 5156312082702085790137057280, 5156860386024873594789560320, 139913269589128791499735040, 184837681792221608899772416,
    635736296332094258894864384, 184860347376977425008164864, 635736296332094258894864384, 16948109890281460019759153152, 1657933672904564011991826432, 169437693930888727402943348736,
    1462882652562850598816317440, 243813775427141766469386240, 1621361606590492747021418496, 1657933672904564011991826432, 1462882652562850598816317440, 29538038892998225007766142976,
    1462882652562850598816317440, 16936104812011150299717697536, 1621361606590492747021418496, 243813775427141766469386240, 1462882652562850598816317440, 243813775427141766469386240,
    1657933672904564011991826432, 1657933672904564011991826432, 635679473473498978296266752, 5156312082702085790137057280, 187617183127531582223758131200, 187635418039133541872676372480,
    5138214590933002973263953920, 4915191938188716677527502848, 16948109890281460019759153152, 4915958734566723635730448384, 486344063295122969756434432, 1657933672904564011991826432,
    486344847281746102412378112, 184860347376977425008164864, 4915958734566723635730448384, 486344847281746102412378112, 49090434543991152873610149888, 429127806425070090363863040,
    71521301070845015060643840, 475616652121119350153281536, 486344847281746102412378112, 429127806425070090363863040
  ]
def negativeScales : Array ℕ := #[
    39, 43, 25, 47, 25, 23,
    28, 25, 25, 32, 25, 43,
    28, 23, 25, 23, 25, 25,
    38, 37, 42, 44, 38, 39,
    41, 38, 41, 45, 27, 49,
    27, 25, 30, 27, 27, 34,
    27, 45, 30, 25, 27, 25,
    27, 27, 40, 42, 43, 46,
    42, 43, 45, 42, 25, 27,
    24, 38, 42, 24, 46, 24,
    22, 27, 24, 24
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    39256389367727035, 43989306336793771, 25652107774314190, 47309180699828300, 25471535528649993, 23886573031355096,
    28619927368552286, 25652107774314190, 25471535528649993, 32807223623240723, 25471535528649993, 43988272056982624,
    28619927368552286, 23886573031355096, 25471535528649993, 23886573031355096, 25652107774314190, 25652107774314190,
    38256260969914824, 37860262299910463, 42058398146554607, 44058551549300044, 38854663265366746, 39256389367727035,
    41038558926186084, 38256566266299313, 41038558926186084, 45775111045403608, 27421444853662358, 49096669611042361,
    27240872608020522, 25655910107324111, 30389264447913197, 27421444853662358, 27240872608020522, 34576560701866266,
    27240872608020522, 45774088760076805, 30389264447913197, 25655910107324111, 27240872608020522, 25655910107324111,
    27421444853662358, 27421444853662358, 40038429970641712, 42058398146554607, 43243706716461168, 46243846928235733,
    42053325705761152, 43989306336793771, 45775111045403608, 42989531387497935, 25652107774314190, 27421444853662358,
    24652110099936702, 38256566266299313, 42989531387497935, 24652110099936702, 46309428594209843, 24471537854272504,
    22886575356977752, 27619929694174798, 24652110099936702, 24471537854272504
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
noncomputable def negativeCeiling : ℝ := 217409719 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 184837681792221608899772416, coefficient := (-184837681792221608899772416) }, { argument := 4915191938188716677527502848, coefficient := (-4915191938188716677527502848) }, { argument := 486344063295122969756434432, coefficient := (-486344063295122969756434432) }, { argument := 49082000192224557092915118080, coefficient := (-49082000192224557092915118080) }, { argument := 429127114672167326255677440, coefficient := (-429127114672167326255677440) }, { argument := 71521185778694554375946240, coefficient := (-71521185778694554375946240) }, { argument := 475615885428318786600042496, coefficient := (-475615885428318786600042496) }, { argument := 486344063295122969756434432, coefficient := (-486344063295122969756434432) }, { argument := 429127114672167326255677440, coefficient := (-429127114672167326255677440) }, { argument := 8664791657088845262645886976, coefficient := (-8664791657088845262645886976) }, { argument := 429127114672167326255677440, coefficient := (-429127114672167326255677440) }, { argument := 4911669461025224794870644736, coefficient := (-4911669461025224794870644736) }, { argument := 475615885428318786600042496, coefficient := (-475615885428318786600042496) }, { argument := 71521185778694554375946240, coefficient := (-71521185778694554375946240) }, { argument := 429127114672167326255677440, coefficient := (-429127114672167326255677440) }, { argument := 71521185778694554375946240, coefficient := (-71521185778694554375946240) }, { argument := 486344063295122969756434432, coefficient := (-486344063295122969756434432) }, { argument := 486344063295122969756434432, coefficient := (-486344063295122969756434432) }, { argument := 184821232232734526554505216, coefficient := (-184821232232734526554505216) }, { argument := 140457321710900842101473280, coefficient := (-140457321710900842101473280) }, { argument := 5156312082702085790137057280, coefficient := (-5156312082702085790137057280) }, { argument := 5156860386024873594789560320, coefficient := (-5156860386024873594789560320) }, { argument := 139913269589128791499735040, coefficient := (-139913269589128791499735040) }, { argument := 184837681792221608899772416, coefficient := (-184837681792221608899772416) }, { argument := 635736296332094258894864384, coefficient := (-635736296332094258894864384) }, { argument := 184860347376977425008164864, coefficient := (-184860347376977425008164864) }, { argument := 635736296332094258894864384, coefficient := (-635736296332094258894864384) }, { argument := 16948109890281460019759153152, coefficient := (-16948109890281460019759153152) }, { argument := 1657933672904564011991826432, coefficient := (-1657933672904564011991826432) }, { argument := 169437693930888727402943348736, coefficient := (-169437693930888727402943348736) }, { argument := 1462882652562850598816317440, coefficient := (-1462882652562850598816317440) }, { argument := 243813775427141766469386240, coefficient := (-243813775427141766469386240) }, { argument := 1621361606590492747021418496, coefficient := (-1621361606590492747021418496) }, { argument := 1657933672904564011991826432, coefficient := (-1657933672904564011991826432) }, { argument := 1462882652562850598816317440, coefficient := (-1462882652562850598816317440) }, { argument := 29538038892998225007766142976, coefficient := (-29538038892998225007766142976) }, { argument := 1462882652562850598816317440, coefficient := (-1462882652562850598816317440) }, { argument := 16936104812011150299717697536, coefficient := (-16936104812011150299717697536) }, { argument := 1621361606590492747021418496, coefficient := (-1621361606590492747021418496) }, { argument := 243813775427141766469386240, coefficient := (-243813775427141766469386240) }, { argument := 1462882652562850598816317440, coefficient := (-1462882652562850598816317440) }, { argument := 243813775427141766469386240, coefficient := (-243813775427141766469386240) }, { argument := 1657933672904564011991826432, coefficient := (-1657933672904564011991826432) }, { argument := 1657933672904564011991826432, coefficient := (-1657933672904564011991826432) }, { argument := 635679473473498978296266752, coefficient := (-635679473473498978296266752) }, { argument := 5156312082702085790137057280, coefficient := (-5156312082702085790137057280) }, { argument := 187617183127531582223758131200, coefficient := (-187617183127531582223758131200) }, { argument := 187635418039133541872676372480, coefficient := (-187635418039133541872676372480) }, { argument := 5138214590933002973263953920, coefficient := (-5138214590933002973263953920) }, { argument := 4915191938188716677527502848, coefficient := (-4915191938188716677527502848) }, { argument := 16948109890281460019759153152, coefficient := (-16948109890281460019759153152) }, { argument := 4915958734566723635730448384, coefficient := (-4915958734566723635730448384) }, { argument := 486344063295122969756434432, coefficient := (-486344063295122969756434432) }, { argument := 1657933672904564011991826432, coefficient := (-1657933672904564011991826432) }, { argument := 486344847281746102412378112, coefficient := (-486344847281746102412378112) }, { argument := 184860347376977425008164864, coefficient := (-184860347376977425008164864) }, { argument := 4915958734566723635730448384, coefficient := (-4915958734566723635730448384) }, { argument := 486344847281746102412378112, coefficient := (-486344847281746102412378112) }, { argument := 49090434543991152873610149888, coefficient := (-49090434543991152873610149888) }, { argument := 429127806425070090363863040, coefficient := (-429127806425070090363863040) }, { argument := 71521301070845015060643840, coefficient := (-71521301070845015060643840) }, { argument := 475616652121119350153281536, coefficient := (-475616652121119350153281536) }, { argument := 486344847281746102412378112, coefficient := (-486344847281746102412378112) }, { argument := 429127806425070090363863040, coefficient := (-429127806425070090363863040) }] }

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
def constantNumerator : ℤ := (-39753371331544824058877973626880)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3757760433, 23263065, 8726239754979, 206265843, 7754355, 23263065,
    7754355, 26364807, 26364807, 164174358403, 18320848433095, 83326864536885,
    41667481232185, 18256553210625, 174374293465805, 601963612932681, 87202129151349, 46526055,
    158606055, 23263065, 15508685, 52868685, 7754355, 412531021,
    1406307021, 206265843, 52729529, 179753529, 26364807, 46526055,
    158606055, 23263065, 7515508751, 25620164751, 3757760433, 46526055,
    158606055, 23263065, 497071786715, 4563651315455, 18256553210625, 61892369605,
    17449755279931, 60169131231231, 8726239754979, 412531021, 1406307021, 206265843,
    15508685, 52868685, 7754355, 46526055, 158606055, 23263065,
    15508685, 52868685, 7754355, 52729529, 179753529, 26364807,
    52729529, 179753529, 26364807, 328308459943
  ]
def negativeCoefficients : Array ℕ := #[
    8664805624732873574597001216, 429127806425070090363863040, 4912436263608629089636712448, 475616652121119350153281536, 71521301070845015060643840, 429127806425070090363863040,
    71521301070845015060643840, 486344847281746102412378112, 486344847281746102412378112, 184843894831885264692969472, 5156860386024873594789560320, 187635418039133541872676372480,
    187653652950735501521594613760, 5138762889777523898449920000, 49082000192224557092915118080, 169437693930888727402943348736, 49090434543991152873610149888, 429127114672167326255677440,
    1462882652562850598816317440, 429127806425070090363863040, 71521185778694554375946240, 243813775427141766469386240, 71521301070845015060643840, 475615885428318786600042496,
    1621361606590492747021418496, 475616652121119350153281536, 486344063295122969756434432, 1657933672904564011991826432, 486344847281746102412378112, 429127114672167326255677440,
    1462882652562850598816317440, 429127806425070090363863040, 8664791657088845262645886976, 29538038892998225007766142976, 8664805624732873574597001216, 429127114672167326255677440,
    1462882652562850598816317440, 429127806425070090363863040, 139913269589128791499735040, 5138214590933002973263953920, 5138762889777523898449920000, 139369226345077506352087040,
    4911669461025224794870644736, 16936104812011150299717697536, 4912436263608629089636712448, 475615885428318786600042496, 1621361606590492747021418496, 475616652121119350153281536,
    71521185778694554375946240, 243813775427141766469386240, 71521301070845015060643840, 429127114672167326255677440, 1462882652562850598816317440, 429127806425070090363863040,
    71521185778694554375946240, 243813775427141766469386240, 71521301070845015060643840, 486344063295122969756434432, 1657933672904564011991826432, 486344847281746102412378112,
    486344063295122969756434432, 1657933672904564011991826432, 486344847281746102412378112, 184821232232734526554505216
  ]
def negativeScales : Array ℕ := #[
    31, 24, 42, 27, 22, 24,
    22, 24, 24, 37, 44, 46,
    45, 44, 47, 49, 46, 25,
    27, 24, 23, 25, 22, 28,
    30, 27, 25, 27, 24, 25,
    27, 24, 32, 34, 31, 25,
    27, 24, 38, 42, 44, 35,
    43, 45, 42, 28, 30, 27,
    23, 25, 22, 25, 27, 24,
    23, 25, 22, 25, 27, 24,
    25, 27, 24, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31807225948863269, 24471537854272504, 42988497270893964, 27619929694174798, 22886575356977752, 24471537854272504,
    22886575356977752, 24652110099936702, 24652110099936702, 37256437860928099, 44058551549300044, 46243846928235733,
    45243987126384805, 44053479647525869, 47309180699828300, 49096669611042361, 46309428594209843, 25471535528649993,
    27240872608020522, 24471537854272504, 23886573031355096, 25655910107324111, 22886575356977752, 28619927368552286,
    30389264447913197, 27619929694174798, 25652107774314190, 27421444853662358, 24652110099936702, 25471535528649993,
    27240872608020522, 24471537854272504, 32807223623240723, 34576560701866266, 31807225948863269, 25471535528649993,
    27240872608020522, 24471537854272504, 38854663265366746, 42053325705761152, 44053479647525869, 35849042508453651,
    43988272056982624, 45774088760076805, 42988497270893964, 28619927368552286, 30389264447913197, 27619929694174798,
    23886573031355096, 25655910107324111, 22886575356977752, 25471535528649993, 27240872608020522, 24471537854272504,
    23886573031355096, 25655910107324111, 22886575356977752, 25652107774314190, 27421444853662358, 24652110099936702,
    25652107774314190, 27421444853662358, 24652110099936702, 38256260969914824
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
noncomputable def negativeCeiling : ℝ := 822127 / 1953125000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 8664805624732873574597001216, coefficient := (-8664805624732873574597001216) }, { argument := 429127806425070090363863040, coefficient := (-429127806425070090363863040) }, { argument := 4912436263608629089636712448, coefficient := (-4912436263608629089636712448) }, { argument := 475616652121119350153281536, coefficient := (-475616652121119350153281536) }, { argument := 71521301070845015060643840, coefficient := (-71521301070845015060643840) }, { argument := 429127806425070090363863040, coefficient := (-429127806425070090363863040) }, { argument := 71521301070845015060643840, coefficient := (-71521301070845015060643840) }, { argument := 486344847281746102412378112, coefficient := (-486344847281746102412378112) }, { argument := 486344847281746102412378112, coefficient := (-486344847281746102412378112) }, { argument := 184843894831885264692969472, coefficient := (-184843894831885264692969472) }, { argument := 5156860386024873594789560320, coefficient := (-5156860386024873594789560320) }, { argument := 187635418039133541872676372480, coefficient := (-187635418039133541872676372480) }, { argument := 187653652950735501521594613760, coefficient := (-187653652950735501521594613760) }, { argument := 5138762889777523898449920000, coefficient := (-5138762889777523898449920000) }, { argument := 49082000192224557092915118080, coefficient := (-49082000192224557092915118080) }, { argument := 169437693930888727402943348736, coefficient := (-169437693930888727402943348736) }, { argument := 49090434543991152873610149888, coefficient := (-49090434543991152873610149888) }, { argument := 429127114672167326255677440, coefficient := (-429127114672167326255677440) }, { argument := 1462882652562850598816317440, coefficient := (-1462882652562850598816317440) }, { argument := 429127806425070090363863040, coefficient := (-429127806425070090363863040) }, { argument := 71521185778694554375946240, coefficient := (-71521185778694554375946240) }, { argument := 243813775427141766469386240, coefficient := (-243813775427141766469386240) }, { argument := 71521301070845015060643840, coefficient := (-71521301070845015060643840) }, { argument := 475615885428318786600042496, coefficient := (-475615885428318786600042496) }, { argument := 1621361606590492747021418496, coefficient := (-1621361606590492747021418496) }, { argument := 475616652121119350153281536, coefficient := (-475616652121119350153281536) }, { argument := 486344063295122969756434432, coefficient := (-486344063295122969756434432) }, { argument := 1657933672904564011991826432, coefficient := (-1657933672904564011991826432) }, { argument := 486344847281746102412378112, coefficient := (-486344847281746102412378112) }, { argument := 429127114672167326255677440, coefficient := (-429127114672167326255677440) }, { argument := 1462882652562850598816317440, coefficient := (-1462882652562850598816317440) }, { argument := 429127806425070090363863040, coefficient := (-429127806425070090363863040) }, { argument := 8664791657088845262645886976, coefficient := (-8664791657088845262645886976) }, { argument := 29538038892998225007766142976, coefficient := (-29538038892998225007766142976) }, { argument := 8664805624732873574597001216, coefficient := (-8664805624732873574597001216) }, { argument := 429127114672167326255677440, coefficient := (-429127114672167326255677440) }, { argument := 1462882652562850598816317440, coefficient := (-1462882652562850598816317440) }, { argument := 429127806425070090363863040, coefficient := (-429127806425070090363863040) }, { argument := 139913269589128791499735040, coefficient := (-139913269589128791499735040) }, { argument := 5138214590933002973263953920, coefficient := (-5138214590933002973263953920) }, { argument := 5138762889777523898449920000, coefficient := (-5138762889777523898449920000) }, { argument := 139369226345077506352087040, coefficient := (-139369226345077506352087040) }, { argument := 4911669461025224794870644736, coefficient := (-4911669461025224794870644736) }, { argument := 16936104812011150299717697536, coefficient := (-16936104812011150299717697536) }, { argument := 4912436263608629089636712448, coefficient := (-4912436263608629089636712448) }, { argument := 475615885428318786600042496, coefficient := (-475615885428318786600042496) }, { argument := 1621361606590492747021418496, coefficient := (-1621361606590492747021418496) }, { argument := 475616652121119350153281536, coefficient := (-475616652121119350153281536) }, { argument := 71521185778694554375946240, coefficient := (-71521185778694554375946240) }, { argument := 243813775427141766469386240, coefficient := (-243813775427141766469386240) }, { argument := 71521301070845015060643840, coefficient := (-71521301070845015060643840) }, { argument := 429127114672167326255677440, coefficient := (-429127114672167326255677440) }, { argument := 1462882652562850598816317440, coefficient := (-1462882652562850598816317440) }, { argument := 429127806425070090363863040, coefficient := (-429127806425070090363863040) }, { argument := 71521185778694554375946240, coefficient := (-71521185778694554375946240) }, { argument := 243813775427141766469386240, coefficient := (-243813775427141766469386240) }, { argument := 71521301070845015060643840, coefficient := (-71521301070845015060643840) }, { argument := 486344063295122969756434432, coefficient := (-486344063295122969756434432) }, { argument := 1657933672904564011991826432, coefficient := (-1657933672904564011991826432) }, { argument := 486344847281746102412378112, coefficient := (-486344847281746102412378112) }, { argument := 486344063295122969756434432, coefficient := (-486344063295122969756434432) }, { argument := 1657933672904564011991826432, coefficient := (-1657933672904564011991826432) }, { argument := 486344847281746102412378112, coefficient := (-486344847281746102412378112) }, { argument := 184821232232734526554505216, coefficient := (-184821232232734526554505216) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk9
