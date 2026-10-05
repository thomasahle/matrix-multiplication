import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 2,
parent chunk 7, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1472520902363046154028628536459264)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    130311165, 8051925, 1285467225, 51308119275, 1285467225, 32204025,
    38982573, 1464675411, 2929129269, 78186699, 15768639699, 11115,
    3627, 27081383469, 36621, 15768639699, 73359, 32877,
    11115, 3627, 64970955, 2441125685, 4881882115, 130311165,
    6758121087, 11115, 3627, 11607670017, 36621, 6758121087,
    73359, 32877, 11115, 3627, 725, 725,
    10812585, 1726198845, 68899474455, 1726198845, 43245405, 1000552707,
    37593335549, 75180984571, 2006791941, 15768639699, 11115, 3627,
    27081383469, 36621, 15768639699, 73359, 32877, 11115,
    3627, 1130494617, 42475586919, 84944748801, 2267414271, 177998829243,
    11115, 3627, 306027972933, 36621
  ]
def negativeCoefficients : Array ℕ := #[
    2403816710701937542708592640, 74265899887851890697830400, 11856342457358306385906892800, 118308468146161133252562124800, 11856342457358306385906892800, 74257425914793030372556800,
    46022499037804798506751229952, 1729183517297430515698592907264, 1729052735489758113385339158528, 46153280845477200820004978688, 145440030458994708903773601792, 419912827656768852401848320,
    17128023233368203190075392, 499563350014631568640944635904, 345875565938338554741522432, 145440030458994708903773601792, 346428082816834303231524864, 310514485714610651381366784,
    419912827656768852401848320, 17128023233368203190075392, 2397005158218999922226626560, 90061641525907839359301713920, 90054829973424901738819747840, 2403816710701937542708592640,
    124665330111028803089404526592, 419912827656768852401848320, 17128023233368203190075392, 428247436191341600519114194944, 345875565938338554741522432, 124665330111028803089404526592,
    346428082816834303231524864, 310514485714610651381366784, 419912827656768852401848320, 17128023233368203190075392, 7011769753764849213295820800, 7011769753764849213295820800,
    99728494135115396079943680, 15921374157024011432503541760, 158871371510559236082011996160, 15921374157024011432503541760, 99717114799864926500290560, 73827758873145197604580098048,
    2773898558997961452266492788736, 2773688763181486973555648233472, 74037554689619676315424653312, 145440030458994708903773601792, 419912827656768852401848320, 17128023233368203190075392,
    499563350014631568640944635904, 345875565938338554741522432, 145440030458994708903773601792, 346428082816834303231524864, 310514485714610651381366784, 419912827656768852401848320,
    17128023233368203190075392, 41707889753010598646743302144, 1567072562550796404851849822208, 1566954041537593290255463612416, 41826410766213713243129511936, 1641749424232774341837239353344,
    13437210485016603276859146240, 548096743467782502082412544, 5645219696091164818844814409728, 11068018110026833751728717824
  ]
def negativeScales : Array ℕ := #[
    26, 22, 30, 35, 30, 24,
    25, 30, 31, 26, 33, 13,
    11, 34, 15, 33, 16, 15,
    13, 11, 25, 31, 32, 26,
    32, 13, 11, 33, 15, 32,
    16, 15, 13, 11, 9, 9,
    23, 30, 36, 30, 25, 29,
    35, 36, 30, 33, 13, 11,
    34, 15, 33, 16, 15, 13,
    11, 30, 35, 36, 31, 37,
    13, 11, 38, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    26957385469542887, 22940902312533566, 30259645680857361, 35578468092660583, 30259645680857361, 24940737687068613,
    25216325981380777, 30447933836159254, 31447824717954675, 26220419863574444, 33876339161356662, 13440220327914385,
    11824561031027542, 34656582390650814, 15160383566516023, 33876339161356662, 16162686352385444, 15004791039804331,
    13440220327914385, 11824561031027542, 25953291586565642, 31184899430325417, 32184790312120838, 26957385469542887,
    32653975053882570, 13440220327914385, 11824561031027542, 33434359361019787, 15160383566516023, 32653975053882570,
    16162686352385444, 15004791039804331, 13440220327914385, 11824561031027542, 9501837184902585, 9501837184902585,
    23366208138333985, 30684951515640630, 36003773927390173, 30684951515640630, 25366043512894097, 29898150025579494,
    35129757876132956, 36129648757928377, 30902243908094838, 33876339161356662, 13440220327914385, 11824561031027542,
    34656582390650814, 15160383566516023, 33876339161356662, 16162686352385444, 15004791039804331, 13440220327914385,
    11824561031027542, 30074306976508349, 35305914831286783, 36305805713082204, 31078400858702016, 37373076795902815,
    13440220327914385, 11824561031027542, 38154872574349645, 15160383566516023
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
noncomputable def negativeCeiling : ℝ := 150080543 / 15625000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2403816710701937542708592640, coefficient := (-2403816710701937542708592640) }, { argument := 74265899887851890697830400, coefficient := (-74265899887851890697830400) }, { argument := 11856342457358306385906892800, coefficient := (-11856342457358306385906892800) }, { argument := 118308468146161133252562124800, coefficient := (-118308468146161133252562124800) }, { argument := 11856342457358306385906892800, coefficient := (-11856342457358306385906892800) }, { argument := 74257425914793030372556800, coefficient := (-74257425914793030372556800) }, { argument := 46022499037804798506751229952, coefficient := (-46022499037804798506751229952) }, { argument := 1729183517297430515698592907264, coefficient := (-1729183517297430515698592907264) }, { argument := 1729052735489758113385339158528, coefficient := (-1729052735489758113385339158528) }, { argument := 46153280845477200820004978688, coefficient := (-46153280845477200820004978688) }, { argument := 145440030458994708903773601792, coefficient := (-145440030458994708903773601792) }, { argument := 419912827656768852401848320, coefficient := (-419912827656768852401848320) }, { argument := 17128023233368203190075392, coefficient := (-17128023233368203190075392) }, { argument := 499563350014631568640944635904, coefficient := (-499563350014631568640944635904) }, { argument := 345875565938338554741522432, coefficient := (-345875565938338554741522432) }, { argument := 145440030458994708903773601792, coefficient := (-145440030458994708903773601792) }, { argument := 346428082816834303231524864, coefficient := (-346428082816834303231524864) }, { argument := 310514485714610651381366784, coefficient := (-310514485714610651381366784) }, { argument := 419912827656768852401848320, coefficient := (-419912827656768852401848320) }, { argument := 17128023233368203190075392, coefficient := (-17128023233368203190075392) }, { argument := 2397005158218999922226626560, coefficient := (-2397005158218999922226626560) }, { argument := 90061641525907839359301713920, coefficient := (-90061641525907839359301713920) }, { argument := 90054829973424901738819747840, coefficient := (-90054829973424901738819747840) }, { argument := 2403816710701937542708592640, coefficient := (-2403816710701937542708592640) }, { argument := 124665330111028803089404526592, coefficient := (-124665330111028803089404526592) }, { argument := 419912827656768852401848320, coefficient := (-419912827656768852401848320) }, { argument := 17128023233368203190075392, coefficient := (-17128023233368203190075392) }, { argument := 428247436191341600519114194944, coefficient := (-428247436191341600519114194944) }, { argument := 345875565938338554741522432, coefficient := (-345875565938338554741522432) }, { argument := 124665330111028803089404526592, coefficient := (-124665330111028803089404526592) }, { argument := 346428082816834303231524864, coefficient := (-346428082816834303231524864) }, { argument := 310514485714610651381366784, coefficient := (-310514485714610651381366784) }, { argument := 419912827656768852401848320, coefficient := (-419912827656768852401848320) }, { argument := 17128023233368203190075392, coefficient := (-17128023233368203190075392) }, { argument := 7011769753764849213295820800, coefficient := (-7011769753764849213295820800) }, { argument := 7011769753764849213295820800, coefficient := (-7011769753764849213295820800) }, { argument := 99728494135115396079943680, coefficient := (-99728494135115396079943680) }, { argument := 15921374157024011432503541760, coefficient := (-15921374157024011432503541760) }, { argument := 158871371510559236082011996160, coefficient := (-158871371510559236082011996160) }, { argument := 15921374157024011432503541760, coefficient := (-15921374157024011432503541760) }, { argument := 99717114799864926500290560, coefficient := (-99717114799864926500290560) }, { argument := 73827758873145197604580098048, coefficient := (-73827758873145197604580098048) }, { argument := 2773898558997961452266492788736, coefficient := (-2773898558997961452266492788736) }, { argument := 2773688763181486973555648233472, coefficient := (-2773688763181486973555648233472) }, { argument := 74037554689619676315424653312, coefficient := (-74037554689619676315424653312) }, { argument := 145440030458994708903773601792, coefficient := (-145440030458994708903773601792) }, { argument := 419912827656768852401848320, coefficient := (-419912827656768852401848320) }, { argument := 17128023233368203190075392, coefficient := (-17128023233368203190075392) }, { argument := 499563350014631568640944635904, coefficient := (-499563350014631568640944635904) }, { argument := 345875565938338554741522432, coefficient := (-345875565938338554741522432) }, { argument := 145440030458994708903773601792, coefficient := (-145440030458994708903773601792) }, { argument := 346428082816834303231524864, coefficient := (-346428082816834303231524864) }, { argument := 310514485714610651381366784, coefficient := (-310514485714610651381366784) }, { argument := 419912827656768852401848320, coefficient := (-419912827656768852401848320) }, { argument := 17128023233368203190075392, coefficient := (-17128023233368203190075392) }, { argument := 41707889753010598646743302144, coefficient := (-41707889753010598646743302144) }, { argument := 1567072562550796404851849822208, coefficient := (-1567072562550796404851849822208) }, { argument := 1566954041537593290255463612416, coefficient := (-1566954041537593290255463612416) }, { argument := 41826410766213713243129511936, coefficient := (-41826410766213713243129511936) }, { argument := 1641749424232774341837239353344, coefficient := (-1641749424232774341837239353344) }, { argument := 13437210485016603276859146240, coefficient := (-13437210485016603276859146240) }, { argument := 548096743467782502082412544, coefficient := (-548096743467782502082412544) }, { argument := 5645219696091164818844814409728, coefficient := (-5645219696091164818844814409728) }, { argument := 11068018110026833751728717824, coefficient := (-11068018110026833751728717824) }] }

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

end TermShard8


end Parent2

namespace Parent2

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-388906771559043133769332606107648)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    177998829243, 73359, 32877, 11115, 3627, 23403,
    23403, 6758121087, 11115, 3627, 11607670017, 36621,
    6758121087, 73359, 32877, 11115, 3627, 15631,
    15631, 489, 17841638983483, 42421683, 321517546901879, 1049711007,
    33395793, 1286041507784665, 17149191, 17149191, 580364727, 31590615,
    1049711007, 580364727, 35712013927381, 33395793, 31590615, 42421683,
    23707515078723, 12825, 4185, 324496180702221, 42255, 94830059057895,
    84645, 37935, 12825, 4185, 16009315, 16009315,
    13967102607, 13395, 4371, 23992462449, 44133, 13967102607,
    88407, 39621, 13395, 4371, 14529, 14529,
    535, 87, 87, 489
  ]
def negativeCoefficients : Array ℕ := #[
    1641749424232774341837239353344, 11085698650138697703408795648, 9936463542867540844203737088, 13437210485016603276859146240, 548096743467782502082412544, 226339927651529332605189095424,
    226339927651529332605189095424, 124665330111028803089404526592, 419912827656768852401848320, 17128023233368203190075392, 428247436191341600519114194944, 345875565938338554741522432,
    124665330111028803089404526592, 346428082816834303231524864, 310514485714610651381366784, 419912827656768852401848320, 17128023233368203190075392, 151173755891170149038657896448,
    151173755891170149038657896448, 18917271225329717325802242048, 10043949834711619229708189696, 97817741184629404090761216, 361996576105094558764022890496, 2420468787185616956543729664,
    77005455826197615986343936, 361988503452625507799258890240, 79086684362040794796785664, 79086684362040794796785664, 1338229948547163975114031104, 72842998754511258365460480,
    2420468787185616956543729664, 1338229948547163975114031104, 10052038288500189687432871936, 77005455826197615986343936, 72842998754511258365460480, 97817741184629404090761216,
    213538312148834635885855113216, 484514801142425598925209600, 19763103730809465219317760, 730700439246835815318508535808, 399087191467313717009448960, 213538309318329025482939432960,
    399724710942501119113297920, 358285945055319982363115520, 484514801142425598925209600, 19763103730809465219317760, 37800926284851127082150789120, 37800926284851127082150789120,
    128823783621285239268317331456, 506048792304311181099663360, 20641463896623219229065216, 442582814494789705279507267584, 416824399976972104432091136, 128823783621285239268317331456,
    417490253651056724407222272, 374209764835556426023698432, 506048792304311181099663360, 20641463896623219229065216, 140515865865447578234448248832, 140515865865447578234448248832,
    20696810031802451470969733120, 6731298963614255244763987968, 6731298963614255244763987968, 18917271225329717325802242048
  ]
def negativeScales : Array ℕ := #[
    37, 16, 15, 13, 11, 14,
    14, 32, 13, 11, 33, 15,
    32, 16, 15, 13, 11, 13,
    13, 8, 44, 25, 48, 29,
    24, 50, 24, 24, 29, 24,
    29, 29, 45, 24, 24, 25,
    44, 13, 12, 48, 15, 46,
    16, 15, 13, 12, 23, 23,
    33, 13, 12, 34, 15, 33,
    16, 15, 13, 12, 13, 13,
    9, 6, 6, 8
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    37373076795902815, 16162686352385444, 15004791039804331, 13440220327914385, 11824561031027542, 14514405858405788,
    14514405858405788, 32653975053882570, 13440220327914385, 11824561031027542, 33434359361019787, 15160383566516023,
    32653975053882570, 16162686352385444, 15004791039804331, 13440220327914385, 11824561031027542, 13932122465563277,
    13932122465563277, 8933690662845865, 44020313384933638, 25338298522411192, 48191890803573589, 29967345066136994,
    24993163057584726, 50191858630602037, 24031637184177139, 24031637184177139, 29112384598061501, 24912992693181637,
    29967345066136994, 29112384598061501, 45021474728454326, 24993163057584726, 24912992693181637, 25338298522411192,
    44430409687098878, 13646671205401350, 12031011907437707, 48205194826325786, 15366834443983451, 46430409667975582,
    16369137229852872, 15211241917271758, 13646671205401350, 12031011907437707, 23932408251664123, 23932408251664123,
    33701313722161910, 13709406960819918, 12093747662785669, 34481862184064398, 15429570199331434, 33701313722161910,
    16431872985200856, 15273977672619720, 13709406960819918, 12093747662785669, 13826647789424418, 13826647789424418,
    9063395081288510, 6442943495848765, 6442943495848765, 8933690662845865
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
noncomputable def negativeCeiling : ℝ := 2610031829 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1641749424232774341837239353344, coefficient := (-1641749424232774341837239353344) }, { argument := 11085698650138697703408795648, coefficient := (-11085698650138697703408795648) }, { argument := 9936463542867540844203737088, coefficient := (-9936463542867540844203737088) }, { argument := 13437210485016603276859146240, coefficient := (-13437210485016603276859146240) }, { argument := 548096743467782502082412544, coefficient := (-548096743467782502082412544) }, { argument := 226339927651529332605189095424, coefficient := (-226339927651529332605189095424) }, { argument := 226339927651529332605189095424, coefficient := (-226339927651529332605189095424) }, { argument := 124665330111028803089404526592, coefficient := (-124665330111028803089404526592) }, { argument := 419912827656768852401848320, coefficient := (-419912827656768852401848320) }, { argument := 17128023233368203190075392, coefficient := (-17128023233368203190075392) }, { argument := 428247436191341600519114194944, coefficient := (-428247436191341600519114194944) }, { argument := 345875565938338554741522432, coefficient := (-345875565938338554741522432) }, { argument := 124665330111028803089404526592, coefficient := (-124665330111028803089404526592) }, { argument := 346428082816834303231524864, coefficient := (-346428082816834303231524864) }, { argument := 310514485714610651381366784, coefficient := (-310514485714610651381366784) }, { argument := 419912827656768852401848320, coefficient := (-419912827656768852401848320) }, { argument := 17128023233368203190075392, coefficient := (-17128023233368203190075392) }, { argument := 151173755891170149038657896448, coefficient := (-151173755891170149038657896448) }, { argument := 151173755891170149038657896448, coefficient := (-151173755891170149038657896448) }, { argument := 18917271225329717325802242048, coefficient := (-18917271225329717325802242048) }, { argument := 10043949834711619229708189696, coefficient := (-10043949834711619229708189696) }, { argument := 97817741184629404090761216, coefficient := (-97817741184629404090761216) }, { argument := 361996576105094558764022890496, coefficient := (-361996576105094558764022890496) }, { argument := 2420468787185616956543729664, coefficient := (-2420468787185616956543729664) }, { argument := 77005455826197615986343936, coefficient := (-77005455826197615986343936) }, { argument := 361988503452625507799258890240, coefficient := (-361988503452625507799258890240) }, { argument := 79086684362040794796785664, coefficient := (-79086684362040794796785664) }, { argument := 79086684362040794796785664, coefficient := (-79086684362040794796785664) }, { argument := 1338229948547163975114031104, coefficient := (-1338229948547163975114031104) }, { argument := 72842998754511258365460480, coefficient := (-72842998754511258365460480) }, { argument := 2420468787185616956543729664, coefficient := (-2420468787185616956543729664) }, { argument := 1338229948547163975114031104, coefficient := (-1338229948547163975114031104) }, { argument := 10052038288500189687432871936, coefficient := (-10052038288500189687432871936) }, { argument := 77005455826197615986343936, coefficient := (-77005455826197615986343936) }, { argument := 72842998754511258365460480, coefficient := (-72842998754511258365460480) }, { argument := 97817741184629404090761216, coefficient := (-97817741184629404090761216) }, { argument := 213538312148834635885855113216, coefficient := (-213538312148834635885855113216) }, { argument := 484514801142425598925209600, coefficient := (-484514801142425598925209600) }, { argument := 19763103730809465219317760, coefficient := (-19763103730809465219317760) }, { argument := 730700439246835815318508535808, coefficient := (-730700439246835815318508535808) }, { argument := 399087191467313717009448960, coefficient := (-399087191467313717009448960) }, { argument := 213538309318329025482939432960, coefficient := (-213538309318329025482939432960) }, { argument := 399724710942501119113297920, coefficient := (-399724710942501119113297920) }, { argument := 358285945055319982363115520, coefficient := (-358285945055319982363115520) }, { argument := 484514801142425598925209600, coefficient := (-484514801142425598925209600) }, { argument := 19763103730809465219317760, coefficient := (-19763103730809465219317760) }, { argument := 37800926284851127082150789120, coefficient := (-37800926284851127082150789120) }, { argument := 37800926284851127082150789120, coefficient := (-37800926284851127082150789120) }, { argument := 128823783621285239268317331456, coefficient := (-128823783621285239268317331456) }, { argument := 506048792304311181099663360, coefficient := (-506048792304311181099663360) }, { argument := 20641463896623219229065216, coefficient := (-20641463896623219229065216) }, { argument := 442582814494789705279507267584, coefficient := (-442582814494789705279507267584) }, { argument := 416824399976972104432091136, coefficient := (-416824399976972104432091136) }, { argument := 128823783621285239268317331456, coefficient := (-128823783621285239268317331456) }, { argument := 417490253651056724407222272, coefficient := (-417490253651056724407222272) }, { argument := 374209764835556426023698432, coefficient := (-374209764835556426023698432) }, { argument := 506048792304311181099663360, coefficient := (-506048792304311181099663360) }, { argument := 20641463896623219229065216, coefficient := (-20641463896623219229065216) }, { argument := 140515865865447578234448248832, coefficient := (-140515865865447578234448248832) }, { argument := 140515865865447578234448248832, coefficient := (-140515865865447578234448248832) }, { argument := 20696810031802451470969733120, coefficient := (-20696810031802451470969733120) }, { argument := 6731298963614255244763987968, coefficient := (-6731298963614255244763987968) }, { argument := 6731298963614255244763987968, coefficient := (-6731298963614255244763987968) }, { argument := 18917271225329717325802242048, coefficient := (-18917271225329717325802242048) }] }

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

end TermShard9


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7
