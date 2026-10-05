import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 22, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk22

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
def constantNumerator : ℤ := (-2849284265296989144429277434871808)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3734785, 437, 110948095, 6877, 207, 443783077,
    207, 207, 17733, 207, 6877, 17733,
    14948443, 207, 207, 437, 282286225157, 30236744745,
    1698693525, 2069519545433, 91842696585, 282286164741, 91842696585, 91842696585,
    30236744745, 1698693525, 35194349697, 2714843495, 4399293699, 2714843495,
    626502345, 1075336503, 626502345, 7839156045, 7839152307, 3623179,
    440402025, 440401815, 437, 282286224347, 30236730327, 1698692715,
    2069519519783, 91842652791, 282286163931, 91842652791, 91842652791, 30236730327,
    1698692715, 516403183513, 4659791513, 516403176863, 4659791513, 106865397,
    23811069485, 23811058131, 6877, 207, 35194342209, 2714843495,
    4399292763, 2714843495, 106863071, 207
  ]
def negativeCoefficients : Array ℕ := #[
    70548094018897231597734461440, 16905618661490974379091165184, 2095750260664949079141756436480, 133020525783836877351269957632, 16015849258254607306507419648, 2095706328489558942832333422592,
    16015849258254607306507419648, 16015849258254607306507419648, 686012209895239012962067808256, 16015849258254607306507419648, 133020525783836877351269957632, 686012209895239012962067808256,
    70592026194287367907157475328, 16015849258254607306507419648, 16015849258254607306507419648, 16905618661490974379091165184, 1301815437751182472923922300928, 139442372983274294370348564480,
    7833841178835634515188121600, 4771987176267784738301821321216, 211774839867856653060585553920, 1301815159131559983614854692864, 211774839867856653060585553920, 211774839867856653060585553920,
    139442372983274294370348564480, 7833841178835634515188121600, 1298442323402392607165150920704, 50080023152440176724064337920, 1298442319528576351686145081344, 50080023152440176724064337920,
    46227713679175547745290158080, 158691658111670427779579510784, 46227713679175547745290158080, 144606905315988157124805918720, 144606836362058809598501978112, 68439916284148633102855438336,
    8123983444718435793528422400, 8123979570902180314522583040, 16905618661490974379091165184, 1301815434015716797997738098688, 139442306491985280684269764608, 7833837443369959589003919360,
    4771987117122911551970571452416, 211774738885767907556072620032, 1301815155396094308688670490624, 211774738885767907556072620032, 211774738885767907556072620032, 139442306491985280684269764608,
    7833837443369959589003919360, 4762978682556589390909096853504, 171915962954309630094544470016, 4762978621221165345824837730304, 171915962954309630094544470016, 2018630275885433340043091509248,
    219618352455555047618385018880, 219618247733388941169260494848, 133020525783836877351269957632, 16015849258254607306507419648, 1298442047143953359290905919488, 50080023152440176724064337920,
    1298442043270137103811900080128, 50080023152440176724064337920, 2018586338987676720864023281664, 16015849258254607306507419648
  ]
def negativeScales : Array ℕ := #[
    21, 8, 26, 12, 7, 28,
    7, 7, 14, 7, 12, 14,
    23, 7, 7, 8, 38, 34,
    30, 40, 36, 38, 36, 36,
    34, 30, 35, 31, 32, 31,
    29, 30, 29, 32, 32, 21,
    28, 28, 8, 38, 34, 30,
    40, 36, 38, 36, 36, 34,
    30, 38, 32, 38, 32, 26,
    34, 34, 12, 7, 35, 31,
    32, 31, 26, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    21832593764483674, 8771489469857739, 26725309655626681, 12747563630468318, 7693486957561383, 28725279412807550,
    7693486957561383, 7693486957561383, 14114149005972048, 7693486957561383, 12747563630468318, 14114149005972048,
    23833491889482665, 7693486957561383, 7693486957561383, 8771489469857739, 38038367774452416, 34815583778700994,
    30661778441765918, 40912433018162597, 36418445950346017, 38038367465681158, 36418445950346017, 36418445950346017,
    34815583778700994, 30661778441765918, 35034624777780512, 31338221886087583, 32034624773476328, 31338221886087583,
    29222744668667646, 30002141044259258, 29222744668667646, 32868051200145473, 32868050512214838, 21788824652480419,
    28714245861732228, 28714245173801623, 8771489469857739, 38038367770312707, 34815583090770378, 30661777753835314,
    40912433000281571, 36418445262415413, 38038367461541448, 36418445262415413, 36418445262415413, 34815583090770378,
    30661777753835314, 38909706943526288, 32117618261679194, 38909706924947931, 32117618261679194, 26671219543363527,
    34470913370240238, 34470912682309634, 12747563630468318, 7693486957561383, 35034624470830627, 31338221886087583,
    32034624466526441, 31338221886087583, 26671188141756622, 7693486957561383
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
noncomputable def negativeCeiling : ℝ := 226357163 / 12500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 70548094018897231597734461440, coefficient := (-70548094018897231597734461440) }, { argument := 16905618661490974379091165184, coefficient := (-16905618661490974379091165184) }, { argument := 2095750260664949079141756436480, coefficient := (-2095750260664949079141756436480) }, { argument := 133020525783836877351269957632, coefficient := (-133020525783836877351269957632) }, { argument := 16015849258254607306507419648, coefficient := (-16015849258254607306507419648) }, { argument := 2095706328489558942832333422592, coefficient := (-2095706328489558942832333422592) }, { argument := 16015849258254607306507419648, coefficient := (-16015849258254607306507419648) }, { argument := 16015849258254607306507419648, coefficient := (-16015849258254607306507419648) }, { argument := 686012209895239012962067808256, coefficient := (-686012209895239012962067808256) }, { argument := 16015849258254607306507419648, coefficient := (-16015849258254607306507419648) }, { argument := 133020525783836877351269957632, coefficient := (-133020525783836877351269957632) }, { argument := 686012209895239012962067808256, coefficient := (-686012209895239012962067808256) }, { argument := 70592026194287367907157475328, coefficient := (-70592026194287367907157475328) }, { argument := 16015849258254607306507419648, coefficient := (-16015849258254607306507419648) }, { argument := 16015849258254607306507419648, coefficient := (-16015849258254607306507419648) }, { argument := 16905618661490974379091165184, coefficient := (-16905618661490974379091165184) }, { argument := 1301815437751182472923922300928, coefficient := (-1301815437751182472923922300928) }, { argument := 139442372983274294370348564480, coefficient := (-139442372983274294370348564480) }, { argument := 7833841178835634515188121600, coefficient := (-7833841178835634515188121600) }, { argument := 4771987176267784738301821321216, coefficient := (-4771987176267784738301821321216) }, { argument := 211774839867856653060585553920, coefficient := (-211774839867856653060585553920) }, { argument := 1301815159131559983614854692864, coefficient := (-1301815159131559983614854692864) }, { argument := 211774839867856653060585553920, coefficient := (-211774839867856653060585553920) }, { argument := 211774839867856653060585553920, coefficient := (-211774839867856653060585553920) }, { argument := 139442372983274294370348564480, coefficient := (-139442372983274294370348564480) }, { argument := 7833841178835634515188121600, coefficient := (-7833841178835634515188121600) }, { argument := 1298442323402392607165150920704, coefficient := (-1298442323402392607165150920704) }, { argument := 50080023152440176724064337920, coefficient := (-50080023152440176724064337920) }, { argument := 1298442319528576351686145081344, coefficient := (-1298442319528576351686145081344) }, { argument := 50080023152440176724064337920, coefficient := (-50080023152440176724064337920) }, { argument := 46227713679175547745290158080, coefficient := (-46227713679175547745290158080) }, { argument := 158691658111670427779579510784, coefficient := (-158691658111670427779579510784) }, { argument := 46227713679175547745290158080, coefficient := (-46227713679175547745290158080) }, { argument := 144606905315988157124805918720, coefficient := (-144606905315988157124805918720) }, { argument := 144606836362058809598501978112, coefficient := (-144606836362058809598501978112) }, { argument := 68439916284148633102855438336, coefficient := (-68439916284148633102855438336) }, { argument := 8123983444718435793528422400, coefficient := (-8123983444718435793528422400) }, { argument := 8123979570902180314522583040, coefficient := (-8123979570902180314522583040) }, { argument := 16905618661490974379091165184, coefficient := (-16905618661490974379091165184) }, { argument := 1301815434015716797997738098688, coefficient := (-1301815434015716797997738098688) }, { argument := 139442306491985280684269764608, coefficient := (-139442306491985280684269764608) }, { argument := 7833837443369959589003919360, coefficient := (-7833837443369959589003919360) }, { argument := 4771987117122911551970571452416, coefficient := (-4771987117122911551970571452416) }, { argument := 211774738885767907556072620032, coefficient := (-211774738885767907556072620032) }, { argument := 1301815155396094308688670490624, coefficient := (-1301815155396094308688670490624) }, { argument := 211774738885767907556072620032, coefficient := (-211774738885767907556072620032) }, { argument := 211774738885767907556072620032, coefficient := (-211774738885767907556072620032) }, { argument := 139442306491985280684269764608, coefficient := (-139442306491985280684269764608) }, { argument := 7833837443369959589003919360, coefficient := (-7833837443369959589003919360) }, { argument := 4762978682556589390909096853504, coefficient := (-4762978682556589390909096853504) }, { argument := 171915962954309630094544470016, coefficient := (-171915962954309630094544470016) }, { argument := 4762978621221165345824837730304, coefficient := (-4762978621221165345824837730304) }, { argument := 171915962954309630094544470016, coefficient := (-171915962954309630094544470016) }, { argument := 2018630275885433340043091509248, coefficient := (-2018630275885433340043091509248) }, { argument := 219618352455555047618385018880, coefficient := (-219618352455555047618385018880) }, { argument := 219618247733388941169260494848, coefficient := (-219618247733388941169260494848) }, { argument := 133020525783836877351269957632, coefficient := (-133020525783836877351269957632) }, { argument := 16015849258254607306507419648, coefficient := (-16015849258254607306507419648) }, { argument := 1298442047143953359290905919488, coefficient := (-1298442047143953359290905919488) }, { argument := 50080023152440176724064337920, coefficient := (-50080023152440176724064337920) }, { argument := 1298442043270137103811900080128, coefficient := (-1298442043270137103811900080128) }, { argument := 50080023152440176724064337920, coefficient := (-50080023152440176724064337920) }, { argument := 2018586338987676720864023281664, coefficient := (-2018586338987676720864023281664) }, { argument := 16015849258254607306507419648, coefficient := (-16015849258254607306507419648) }] }

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
def constantNumerator : ℤ := 5426130708992666988754249269116928
def positiveArguments : Array ℕ := #[
    585, 23, 437, 667, 6877, 207,
    667, 207, 207, 17733, 207, 6877,
    17733, 23, 207, 207, 437, 825,
    14685, 825, 26125, 44605, 825, 44605,
    44605, 14685, 825, 12075, 13525, 12075,
    13525, 17, 135, 1711276087, 1711275977, 1135281509,
    4071224865, 567640637
  ]
def positiveCoefficients : Array ℕ := #[
    46348475070844637492223210946560, 28472620903563746322679857152, 33811237322981948758182330368, 25803312693854645104928620544, 266041051567673754702539915264, 32031698516509214613014839296,
    25803312693854645104928620544, 32031698516509214613014839296, 32031698516509214613014839296, 1372024419790478025924135616512, 32031698516509214613014839296, 266041051567673754702539915264,
    1372024419790478025924135616512, 28472620903563746322679857152, 32031698516509214613014839296, 32031698516509214613014839296, 33811237322981948758182330368, 31915641637826210212243046400,
    568098421153306541777926225920, 31915641637826210212243046400, 505330992598914995027181568000, 862786178942568549404303687680, 31915641637826210212243046400, 862786178942568549404303687680,
    862786178942568549404303687680, 568098421153306541777926225920, 31915641637826210212243046400, 467128936699092713106466406400, 523223094729211506812832972800, 467128936699092713106466406400,
    523223094729211506812832972800, 1346878762742493739090247155712, 10695801939425685575128433295360, 16162545672370237984743939375104, 16162544633449611753421992361984, 5361215346723273468499422347264,
    19225815846701496147727393751040, 5361214236967149994132797128704
  ]
def positiveScales : Array ℕ := #[
    9, 4, 8, 9, 12, 7,
    9, 7, 7, 14, 7, 12,
    14, 4, 7, 7, 8, 9,
    13, 9, 14, 15, 9, 15,
    15, 13, 9, 13, 13, 13,
    13, 4, 7, 30, 30, 30,
    31, 29
  ]
def negativeArguments : Array ℕ := #[
    626502345, 1075336503, 626502345, 23811069485, 23811058131, 207,
    23811069485, 23811058131, 17733, 207, 7839156045, 7839152307,
    6877, 17733, 3625505, 440402025, 440401815, 207,
    207, 437, 23, 55, 25, 17,
    135, 51
  ]
def negativeCoefficients : Array ℕ := #[
    46227713679175547745290158080, 158691658111670427779579510784, 46227713679175547745290158080, 219618352455555047618385018880, 219618247733388941169260494848, 16015849258254607306507419648,
    219618352455555047618385018880, 219618247733388941169260494848, 686012209895239012962067808256, 16015849258254607306507419648, 144606905315988157124805918720, 144606836362058809598501978112,
    133020525783836877351269957632, 686012209895239012962067808256, 68483853181905252281923665920, 8123983444718435793528422400, 8123979570902180314522583040, 16015849258254607306507419648,
    16015849258254607306507419648, 16905618661490974379091165184, 3644495475656159529303021715456, 4357548938284538567644917268480, 1980704062856608439838598758400, 1346878762742493739090247155712,
    10695801939425685575128433295360, 32325090305819849738165931737088
  ]
def negativeScales : Array ℕ := #[
    29, 30, 29, 34, 34, 7,
    34, 34, 14, 7, 32, 32,
    12, 14, 21, 28, 28, 7,
    7, 8, 4, 5, 4, 4,
    7, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    9192292814470766, 4523561956056975, 8771489469478456, 9381542951184584, 12747563630241893, 7693486957495471,
    9381542951184584, 7693486957495471, 7693486957495471, 14114149005972047, 7693486957495471, 12747563630241893,
    14114149005972047, 4523561956056975, 7693486957495471, 7693486957495471, 8771489469478456, 9688250309129776,
    13842055645120155, 9688250309129776, 14673143416740609, 15444917817741929, 9688250309129776, 15444917817741929,
    15444917817741929, 13842055645120155, 9688250309129776, 13559735568610386, 13723340973593834, 13559735568610386,
    13723340973593834, 4087462841250339, 7076815597050830, 30672425388337047, 30672425295601304, 30080402932366839,
    31922815761294912, 29080402633733093
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    29222744668667646, 30002141044259258, 29222744668667646, 34470913370240238, 34470912682309634, 7693486957561383,
    34470913370240238, 34470912682309634, 14114149005972048, 7693486957561383, 32868051200145473, 32868050512214838,
    12747563630468318, 14114149005972048, 21789750533320658, 28714245861732228, 28714245173801623, 7693486957561383,
    7693486957561383, 8771489469857739, 4523561956057598, 5781359713964302, 4643856189792934, 4087462841250340,
    7076815597050831, 5672425342008812
  ]

abbrev PositiveTerm := Fin 38
abbrev NegativeTerm := Fin 26
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
noncomputable def positiveFloor : ℝ := 7731893357 / 250000000000
noncomputable def negativeCeiling : ℝ := 4650484217 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 46227713679175547745290158080, coefficient := (-46227713679175547745290158080) }, { argument := 158691658111670427779579510784, coefficient := (-158691658111670427779579510784) }, { argument := 46227713679175547745290158080, coefficient := (-46227713679175547745290158080) }, { argument := 219618352455555047618385018880, coefficient := (-219618352455555047618385018880) }, { argument := 219618247733388941169260494848, coefficient := (-219618247733388941169260494848) }, { argument := 16015849258254607306507419648, coefficient := (-16015849258254607306507419648) }, { argument := 219618352455555047618385018880, coefficient := (-219618352455555047618385018880) }, { argument := 219618247733388941169260494848, coefficient := (-219618247733388941169260494848) }, { argument := 686012209895239012962067808256, coefficient := (-686012209895239012962067808256) }, { argument := 16015849258254607306507419648, coefficient := (-16015849258254607306507419648) }, { argument := 144606905315988157124805918720, coefficient := (-144606905315988157124805918720) }, { argument := 144606836362058809598501978112, coefficient := (-144606836362058809598501978112) }, { argument := 133020525783836877351269957632, coefficient := (-133020525783836877351269957632) }, { argument := 686012209895239012962067808256, coefficient := (-686012209895239012962067808256) }, { argument := 68483853181905252281923665920, coefficient := (-68483853181905252281923665920) }, { argument := 8123983444718435793528422400, coefficient := (-8123983444718435793528422400) }, { argument := 8123979570902180314522583040, coefficient := (-8123979570902180314522583040) }, { argument := 16015849258254607306507419648, coefficient := (-16015849258254607306507419648) }, { argument := 16015849258254607306507419648, coefficient := (-16015849258254607306507419648) }, { argument := 16905618661490974379091165184, coefficient := (-16905618661490974379091165184) }, { argument := 46348475070844637492223210946560, coefficient := 46348475070844637492223210946560 }, { argument := 28472620903563746322679857152, coefficient := 28472620903563746322679857152 }, { argument := 33811237322981948758182330368, coefficient := 33811237322981948758182330368 }, { argument := 25803312693854645104928620544, coefficient := 25803312693854645104928620544 }, { argument := 266041051567673754702539915264, coefficient := 266041051567673754702539915264 }, { argument := 32031698516509214613014839296, coefficient := 32031698516509214613014839296 }, { argument := 25803312693854645104928620544, coefficient := 25803312693854645104928620544 }, { argument := 32031698516509214613014839296, coefficient := 32031698516509214613014839296 }, { argument := 32031698516509214613014839296, coefficient := 32031698516509214613014839296 }, { argument := 1372024419790478025924135616512, coefficient := 1372024419790478025924135616512 }, { argument := 32031698516509214613014839296, coefficient := 32031698516509214613014839296 }, { argument := 266041051567673754702539915264, coefficient := 266041051567673754702539915264 }, { argument := 1372024419790478025924135616512, coefficient := 1372024419790478025924135616512 }, { argument := 28472620903563746322679857152, coefficient := 28472620903563746322679857152 }, { argument := 32031698516509214613014839296, coefficient := 32031698516509214613014839296 }, { argument := 32031698516509214613014839296, coefficient := 32031698516509214613014839296 }, { argument := 33811237322981948758182330368, coefficient := 33811237322981948758182330368 }, { argument := 3644495475656159529303021715456, coefficient := (-3644495475656159529303021715456) }, { argument := 31915641637826210212243046400, coefficient := 31915641637826210212243046400 }, { argument := 568098421153306541777926225920, coefficient := 568098421153306541777926225920 }, { argument := 31915641637826210212243046400, coefficient := 31915641637826210212243046400 }, { argument := 505330992598914995027181568000, coefficient := 505330992598914995027181568000 }, { argument := 862786178942568549404303687680, coefficient := 862786178942568549404303687680 }, { argument := 31915641637826210212243046400, coefficient := 31915641637826210212243046400 }, { argument := 862786178942568549404303687680, coefficient := 862786178942568549404303687680 }, { argument := 862786178942568549404303687680, coefficient := 862786178942568549404303687680 }, { argument := 568098421153306541777926225920, coefficient := 568098421153306541777926225920 }, { argument := 31915641637826210212243046400, coefficient := 31915641637826210212243046400 }, { argument := 4357548938284538567644917268480, coefficient := (-4357548938284538567644917268480) }, { argument := 467128936699092713106466406400, coefficient := 467128936699092713106466406400 }, { argument := 523223094729211506812832972800, coefficient := 523223094729211506812832972800 }, { argument := 467128936699092713106466406400, coefficient := 467128936699092713106466406400 }, { argument := 523223094729211506812832972800, coefficient := 523223094729211506812832972800 }, { argument := 1980704062856608439838598758400, coefficient := (-1980704062856608439838598758400) }, { argument := 1346878762742493739090247155712, coefficient := 1346878762742493739090247155712 }, { argument := 1346878762742493739090247155712, coefficient := (-1346878762742493739090247155712) }, { argument := 10695801939425685575128433295360, coefficient := 10695801939425685575128433295360 }, { argument := 10695801939425685575128433295360, coefficient := (-10695801939425685575128433295360) }, { argument := 16162545672370237984743939375104, coefficient := 16162545672370237984743939375104 }, { argument := 16162544633449611753421992361984, coefficient := 16162544633449611753421992361984 }, { argument := 32325090305819849738165931737088, coefficient := (-32325090305819849738165931737088) }, { argument := 5361215346723273468499422347264, coefficient := 5361215346723273468499422347264 }, { argument := 19225815846701496147727393751040, coefficient := 19225815846701496147727393751040 }, { argument := 5361214236967149994132797128704, coefficient := 5361214236967149994132797128704 }] }

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

namespace Parent2

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3098138066957792657257942633938944)
def positiveArguments : Array ℕ := #[
    1462659, 54111869, 865771297, 23421151
  ]
def positiveCoefficients : Array ℕ := #[
    110515389399482118377910042624, 4088577223856527774079919325184, 4088489354783381018591428083712, 110603258472628873866401284096
  ]
def positiveScales : Array ℕ := #[
    20, 25, 29, 24
  ]
def negativeArguments : Array ℕ := #[
    189, 53
  ]
def negativeCoefficients : Array ℕ := #[
    29948245430391919610359613227008, 8398185226512019784915658735616
  ]
def negativeScales : Array ℕ := #[
    7, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    20480162032340262, 25689441736437007, 29689410730629520, 24481308641040786
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    7562242424222992, 5727920454700926
  ]

abbrev PositiveTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 2785246081 / 1000000000000
noncomputable def negativeCeiling : ℝ := 826284219 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 29948245430391919610359613227008, coefficient := (-29948245430391919610359613227008) }, { argument := 110515389399482118377910042624, coefficient := 110515389399482118377910042624 }, { argument := 4088577223856527774079919325184, coefficient := 4088577223856527774079919325184 }, { argument := 4088489354783381018591428083712, coefficient := 4088489354783381018591428083712 }, { argument := 110603258472628873866401284096, coefficient := 110603258472628873866401284096 }, { argument := 8398185226512019784915658735616, coefficient := (-8398185226512019784915658735616) }] }

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

end TermShard2


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk22
