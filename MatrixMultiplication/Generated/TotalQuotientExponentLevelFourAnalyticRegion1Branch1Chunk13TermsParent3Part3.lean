import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 13, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent3

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4242245999784381964095175597752320)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    4020825543, 164733966915, 3391999945005, 164733966915, 4020825543, 1263088071,
    79089, 192289785237, 827541, 36651, 48072463929, 36651,
    71373, 1348371, 71373, 827541, 1348371, 5052422763,
    71373, 71373, 79089, 257213355, 10538078775, 216987202425,
    10538078775, 257213355, 35369924949, 143049, 5379545826495, 1496781,
    66291, 1344886949547, 66291, 129093, 2438811, 129093,
    1496781, 2438811, 141481671489, 129093, 129093, 143049,
    20714986587, 38414089735, 20711040919, 20330393104611, 1478105911365405, 592863885,
    1529231535, 1279583415, 35832820005, 369464440775925, 1279583415, 1156343355,
    593324685, 592863885, 1155421755, 35832820005, 1155421755, 5082568622859,
    1529231535, 14027619063679, 3794787241476813, 5344098385
  ]
def negativeCoefficients : Array ℕ := #[
    18542784939188809975172431872, 3038805327927941597229628784640, 31285677441772054373907604439040, 3038805327927941597229628784640, 18542784939188809975172431872, 93199449553169917459713490944,
    2987897942109418962448023552, 3547120456255512178156206292992, 31263615052803432558297612288, 2769271263418485867634753536, 3547121756363587749131694637056, 2769271263418485867634753536,
    2696395703854841502696996864, 101880032269974822182983827456, 2696395703854841502696996864, 31263615052803432558297612288, 101880032269974822182983827456, 93200749661245488435201835008,
    2696395703854841502696996864, 2696395703854841502696996864, 2987897942109418962448023552, 1186187233006300266674257920, 194393242191015661399336550400, 2001353695202091798578488934400,
    194393242191015661399336550400, 1186187233006300266674257920, 163114988360129341170590416896, 5404238424064159025391992832, 6202194068384099565541911429120, 56546787412768883460808900608,
    5008806344254586413777944576, 6202196341591359748329846079488, 5008806344254586413777944576, 4876995650984728876573261824, 184271349191260837012146487296, 4876995650984728876573261824,
    56546787412768883460808900608, 184271349191260837012146487296, 163117261567389523958525067264, 4876995650984728876573261824, 4876995650984728876573261824, 5404238424064159025391992832,
    191062028030357550529612087296, 708614882166058170103638261760, 191025635666459637820059287552, 11444993851277725112972869632, 832099653954920668305146511360, 5468204178570085566334894080,
    7052335688897752690474352640, 94416591109873119099680194560, 165249715017883703926346219520, 831959958902552259014846054400, 94416591109873119099680194560, 5332692482754917552797777920,
    5472454308404668247027220480, 5468204178570085566334894080, 5328442352920334872105451520, 165249715017883703926346219520, 5328442352920334872105451520, 11444927077996383709043884032,
    7052335688897752690474352640, 31587389994040005200174907392, 4272550601666321862441736077312, 197162430425639071500279480320
  ]
def negativeScales : Array ℕ := #[
    31, 37, 41, 37, 31, 30,
    16, 37, 19, 15, 35, 15,
    16, 20, 16, 19, 20, 32,
    16, 16, 16, 27, 33, 37,
    33, 27, 35, 17, 42, 20,
    16, 40, 16, 16, 21, 16,
    20, 21, 37, 16, 16, 17,
    34, 35, 34, 44, 50, 29,
    30, 30, 35, 48, 30, 30,
    29, 29, 30, 35, 30, 42,
    30, 43, 51, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31904844600082747, 37261347102452202, 41625273285170043, 37261347102452202, 31904844600082747, 30234308091025518,
    16271189432667188, 37484491170040939, 19658471265575042, 15161564941492690, 35484491698824541, 15161564941492690,
    16123090793678054, 20362786073424542, 16123090793678054, 19658471265575042, 20362786073424542, 32234328216105654,
    16123090793678054, 16123090793678054, 16271189432667188, 27938390319699783, 33294892818275093, 37658819001008346,
    33294892818275093, 27938390319699783, 35041804106679196, 17126149886812459, 42290621515608320, 20513431719694343,
    16016525395637961, 40290622044379946, 16016525395637961, 16978051264435663, 21217746527569812, 16978051264435663,
    20513431719694343, 21217746527569812, 37041824212262516, 16978051264435663, 16978051264435663, 17126149886812459,
    34269955835042791, 35160916516655879, 34269681012858937, 44208703344664734, 50392671070553144, 29143125675040099,
    30510159710069002, 30253027052543175, 35060562535462600, 48392428846827257, 30253027052543175, 30106922697330867,
    29144246565807548, 29143125675040099, 30105772417992912, 35060562535462600, 30105772417992912, 42208694927555548,
    30510159710069002, 43673335391746344, 51752940425325139, 32315299422098570
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
noncomputable def negativeCeiling : ℝ := 33609780303 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 18542784939188809975172431872, coefficient := (-18542784939188809975172431872) }, { argument := 3038805327927941597229628784640, coefficient := (-3038805327927941597229628784640) }, { argument := 31285677441772054373907604439040, coefficient := (-31285677441772054373907604439040) }, { argument := 3038805327927941597229628784640, coefficient := (-3038805327927941597229628784640) }, { argument := 18542784939188809975172431872, coefficient := (-18542784939188809975172431872) }, { argument := 93199449553169917459713490944, coefficient := (-93199449553169917459713490944) }, { argument := 2987897942109418962448023552, coefficient := (-2987897942109418962448023552) }, { argument := 3547120456255512178156206292992, coefficient := (-3547120456255512178156206292992) }, { argument := 31263615052803432558297612288, coefficient := (-31263615052803432558297612288) }, { argument := 2769271263418485867634753536, coefficient := (-2769271263418485867634753536) }, { argument := 3547121756363587749131694637056, coefficient := (-3547121756363587749131694637056) }, { argument := 2769271263418485867634753536, coefficient := (-2769271263418485867634753536) }, { argument := 2696395703854841502696996864, coefficient := (-2696395703854841502696996864) }, { argument := 101880032269974822182983827456, coefficient := (-101880032269974822182983827456) }, { argument := 2696395703854841502696996864, coefficient := (-2696395703854841502696996864) }, { argument := 31263615052803432558297612288, coefficient := (-31263615052803432558297612288) }, { argument := 101880032269974822182983827456, coefficient := (-101880032269974822182983827456) }, { argument := 93200749661245488435201835008, coefficient := (-93200749661245488435201835008) }, { argument := 2696395703854841502696996864, coefficient := (-2696395703854841502696996864) }, { argument := 2696395703854841502696996864, coefficient := (-2696395703854841502696996864) }, { argument := 2987897942109418962448023552, coefficient := (-2987897942109418962448023552) }, { argument := 1186187233006300266674257920, coefficient := (-1186187233006300266674257920) }, { argument := 194393242191015661399336550400, coefficient := (-194393242191015661399336550400) }, { argument := 2001353695202091798578488934400, coefficient := (-2001353695202091798578488934400) }, { argument := 194393242191015661399336550400, coefficient := (-194393242191015661399336550400) }, { argument := 1186187233006300266674257920, coefficient := (-1186187233006300266674257920) }, { argument := 163114988360129341170590416896, coefficient := (-163114988360129341170590416896) }, { argument := 5404238424064159025391992832, coefficient := (-5404238424064159025391992832) }, { argument := 6202194068384099565541911429120, coefficient := (-6202194068384099565541911429120) }, { argument := 56546787412768883460808900608, coefficient := (-56546787412768883460808900608) }, { argument := 5008806344254586413777944576, coefficient := (-5008806344254586413777944576) }, { argument := 6202196341591359748329846079488, coefficient := (-6202196341591359748329846079488) }, { argument := 5008806344254586413777944576, coefficient := (-5008806344254586413777944576) }, { argument := 4876995650984728876573261824, coefficient := (-4876995650984728876573261824) }, { argument := 184271349191260837012146487296, coefficient := (-184271349191260837012146487296) }, { argument := 4876995650984728876573261824, coefficient := (-4876995650984728876573261824) }, { argument := 56546787412768883460808900608, coefficient := (-56546787412768883460808900608) }, { argument := 184271349191260837012146487296, coefficient := (-184271349191260837012146487296) }, { argument := 163117261567389523958525067264, coefficient := (-163117261567389523958525067264) }, { argument := 4876995650984728876573261824, coefficient := (-4876995650984728876573261824) }, { argument := 4876995650984728876573261824, coefficient := (-4876995650984728876573261824) }, { argument := 5404238424064159025391992832, coefficient := (-5404238424064159025391992832) }, { argument := 191062028030357550529612087296, coefficient := (-191062028030357550529612087296) }, { argument := 708614882166058170103638261760, coefficient := (-708614882166058170103638261760) }, { argument := 191025635666459637820059287552, coefficient := (-191025635666459637820059287552) }, { argument := 11444993851277725112972869632, coefficient := (-11444993851277725112972869632) }, { argument := 832099653954920668305146511360, coefficient := (-832099653954920668305146511360) }, { argument := 5468204178570085566334894080, coefficient := (-5468204178570085566334894080) }, { argument := 7052335688897752690474352640, coefficient := (-7052335688897752690474352640) }, { argument := 94416591109873119099680194560, coefficient := (-94416591109873119099680194560) }, { argument := 165249715017883703926346219520, coefficient := (-165249715017883703926346219520) }, { argument := 831959958902552259014846054400, coefficient := (-831959958902552259014846054400) }, { argument := 94416591109873119099680194560, coefficient := (-94416591109873119099680194560) }, { argument := 5332692482754917552797777920, coefficient := (-5332692482754917552797777920) }, { argument := 5472454308404668247027220480, coefficient := (-5472454308404668247027220480) }, { argument := 5468204178570085566334894080, coefficient := (-5468204178570085566334894080) }, { argument := 5328442352920334872105451520, coefficient := (-5328442352920334872105451520) }, { argument := 165249715017883703926346219520, coefficient := (-165249715017883703926346219520) }, { argument := 5328442352920334872105451520, coefficient := (-5328442352920334872105451520) }, { argument := 11444927077996383709043884032, coefficient := (-11444927077996383709043884032) }, { argument := 7052335688897752690474352640, coefficient := (-7052335688897752690474352640) }, { argument := 31587389994040005200174907392, coefficient := (-31587389994040005200174907392) }, { argument := 4272550601666321862441736077312, coefficient := (-4272550601666321862441736077312) }, { argument := 197162430425639071500279480320, coefficient := (-197162430425639071500279480320) }] }

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

namespace Parent3

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-6827627298118105518933588158971904)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    37210326396717881, 1691170375, 202940445, 5344098385, 10620549955, 1691170375,
    163908232745, 10485256325, 1897396944374271, 5344098385, 202940445, 10485256325,
    202940445, 5344098385, 5344098385, 14027619063679, 1477733117430375, 4305,
    28879711953715203, 45045, 1995, 57759417194844351, 1995, 3885,
    73395, 3885, 45045, 73395, 369433879812405, 3885,
    3885, 4305, 131095839, 5371020795, 110593477365, 5371020795,
    131095839, 1263088071, 79089, 192289785237, 827541, 36651,
    48072463929, 36651, 71373, 1348371, 71373, 827541,
    1348371, 5052422763, 71373, 71373, 79089, 3065280410520925,
    11083180773846361, 1532591651840677, 1141393419, 2337, 173535258465, 24453,
    1083, 43383830517, 1083, 2109
  ]
def negativeCoefficients : Array ℕ := #[
    41895103023648294996127193759744, 124786348370657640190050304000, 7487180902239458411403018240, 197162430425639071500279480320, 195914566941932495098378977280, 124786348370657640190050304000,
    3023573221021034621804918865920, 193418839974519342294577971200, 4272558085828942301149903454208, 197162430425639071500279480320, 7487180902239458411403018240, 193418839974519342294577971200,
    7487180902239458411403018240, 197162430425639071500279480320, 197162430425639071500279480320, 31587389994040005200174907392, 831889789626559782193201152000, 162638301670030581159690240,
    32515664998329761813758237212672, 1701751985766905349207490560, 150737938133199075221176320, 32515661219479754814959766208512, 150737938133199075221176320, 146771150287588573241671680,
    5545569408163481767347486720, 146771150287588573241671680, 1701751985766905349207490560, 5545569408163481767347486720, 831891141730591881353955901440, 146771150287588573241671680,
    146771150287588573241671680, 162638301670030581159690240, 1209145695580615755706662912, 198155692039874029039323709440, 2040089573173745188228395171840, 198155692039874029039323709440,
    1209145695580615755706662912, 93199449553169917459713490944, 2987897942109418962448023552, 3547120456255512178156206292992, 31263615052803432558297612288, 2769271263418485867634753536,
    3547121756363587749131694637056, 2769271263418485867634753536, 2696395703854841502696996864, 101880032269974822182983827456, 2696395703854841502696996864, 31263615052803432558297612288,
    101880032269974822182983827456, 93200749661245488435201835008, 2696395703854841502696996864, 2696395703854841502696996864, 2987897942109418962448023552, 862799732163007427291958476800,
    3119638050198394806180895522816, 862772399017600734658480308224, 5263748071927333282985803776, 176578727527461773830520832, 200072531291805878188863651840, 1847616441689782950568132608,
    163658332830330424525848576, 200072604621072335698151866368, 163658332830330424525848576, 159351534597953308090957824
  ]
def negativeScales : Array ℕ := #[
    55, 30, 27, 32, 33, 30,
    37, 33, 50, 32, 27, 33,
    27, 32, 32, 43, 50, 12,
    54, 15, 10, 55, 10, 11,
    16, 11, 15, 16, 48, 11,
    11, 12, 26, 32, 36, 32,
    26, 30, 16, 37, 19, 15,
    35, 15, 16, 20, 16, 19,
    20, 32, 16, 16, 16, 51,
    53, 50, 30, 11, 37, 14,
    10, 35, 10, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    55046552563562343, 30655374863720606, 27596481174647752, 32315299422098570, 33306139422813094, 30655374863720606,
    37254097363372814, 33287643079195705, 50752942952470141, 32315299422098570, 27596481174647752, 33287643079195705,
    27596481174647752, 32315299422098570, 32315299422098570, 43673335391746344, 50392307161721199, 12071797522284207,
    54680905871098306, 15459079355165734, 10962173043893966, 55680905703433629, 10962173043893966, 11923698889934521,
    16163394163041560, 11923698889934521, 15459079355165734, 16163394163041560, 48392309506589739, 11923698889934521,
    11923698889934521, 12071797522284207, 26966046667679686, 32322549161177958, 36686475343937075, 32322549161177958,
    26966046667679686, 30234308091025518, 16271189432667188, 37484491170040939, 19658471265575042, 15161564941492690,
    35484491698824541, 15161564941492690, 16123090793678054, 20362786073424542, 16123090793678054, 19658471265575042,
    20362786073424542, 32234328216105654, 16123090793678054, 16123090793678054, 16271189432667188, 51444940480379386,
    53299221499594520, 50444894775661953, 30088149003904541, 11190442018782826, 37336437859560013, 14577723851667303,
    10080817527608328, 35336438388327001, 10080817527608328, 11042343379793692
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
noncomputable def negativeCeiling : ℝ := 84116618351 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 41895103023648294996127193759744, coefficient := (-41895103023648294996127193759744) }, { argument := 124786348370657640190050304000, coefficient := (-124786348370657640190050304000) }, { argument := 7487180902239458411403018240, coefficient := (-7487180902239458411403018240) }, { argument := 197162430425639071500279480320, coefficient := (-197162430425639071500279480320) }, { argument := 195914566941932495098378977280, coefficient := (-195914566941932495098378977280) }, { argument := 124786348370657640190050304000, coefficient := (-124786348370657640190050304000) }, { argument := 3023573221021034621804918865920, coefficient := (-3023573221021034621804918865920) }, { argument := 193418839974519342294577971200, coefficient := (-193418839974519342294577971200) }, { argument := 4272558085828942301149903454208, coefficient := (-4272558085828942301149903454208) }, { argument := 197162430425639071500279480320, coefficient := (-197162430425639071500279480320) }, { argument := 7487180902239458411403018240, coefficient := (-7487180902239458411403018240) }, { argument := 193418839974519342294577971200, coefficient := (-193418839974519342294577971200) }, { argument := 7487180902239458411403018240, coefficient := (-7487180902239458411403018240) }, { argument := 197162430425639071500279480320, coefficient := (-197162430425639071500279480320) }, { argument := 197162430425639071500279480320, coefficient := (-197162430425639071500279480320) }, { argument := 31587389994040005200174907392, coefficient := (-31587389994040005200174907392) }, { argument := 831889789626559782193201152000, coefficient := (-831889789626559782193201152000) }, { argument := 162638301670030581159690240, coefficient := (-162638301670030581159690240) }, { argument := 32515664998329761813758237212672, coefficient := (-32515664998329761813758237212672) }, { argument := 1701751985766905349207490560, coefficient := (-1701751985766905349207490560) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 32515661219479754814959766208512, coefficient := (-32515661219479754814959766208512) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 146771150287588573241671680, coefficient := (-146771150287588573241671680) }, { argument := 5545569408163481767347486720, coefficient := (-5545569408163481767347486720) }, { argument := 146771150287588573241671680, coefficient := (-146771150287588573241671680) }, { argument := 1701751985766905349207490560, coefficient := (-1701751985766905349207490560) }, { argument := 5545569408163481767347486720, coefficient := (-5545569408163481767347486720) }, { argument := 831891141730591881353955901440, coefficient := (-831891141730591881353955901440) }, { argument := 146771150287588573241671680, coefficient := (-146771150287588573241671680) }, { argument := 146771150287588573241671680, coefficient := (-146771150287588573241671680) }, { argument := 162638301670030581159690240, coefficient := (-162638301670030581159690240) }, { argument := 1209145695580615755706662912, coefficient := (-1209145695580615755706662912) }, { argument := 198155692039874029039323709440, coefficient := (-198155692039874029039323709440) }, { argument := 2040089573173745188228395171840, coefficient := (-2040089573173745188228395171840) }, { argument := 198155692039874029039323709440, coefficient := (-198155692039874029039323709440) }, { argument := 1209145695580615755706662912, coefficient := (-1209145695580615755706662912) }, { argument := 93199449553169917459713490944, coefficient := (-93199449553169917459713490944) }, { argument := 2987897942109418962448023552, coefficient := (-2987897942109418962448023552) }, { argument := 3547120456255512178156206292992, coefficient := (-3547120456255512178156206292992) }, { argument := 31263615052803432558297612288, coefficient := (-31263615052803432558297612288) }, { argument := 2769271263418485867634753536, coefficient := (-2769271263418485867634753536) }, { argument := 3547121756363587749131694637056, coefficient := (-3547121756363587749131694637056) }, { argument := 2769271263418485867634753536, coefficient := (-2769271263418485867634753536) }, { argument := 2696395703854841502696996864, coefficient := (-2696395703854841502696996864) }, { argument := 101880032269974822182983827456, coefficient := (-101880032269974822182983827456) }, { argument := 2696395703854841502696996864, coefficient := (-2696395703854841502696996864) }, { argument := 31263615052803432558297612288, coefficient := (-31263615052803432558297612288) }, { argument := 101880032269974822182983827456, coefficient := (-101880032269974822182983827456) }, { argument := 93200749661245488435201835008, coefficient := (-93200749661245488435201835008) }, { argument := 2696395703854841502696996864, coefficient := (-2696395703854841502696996864) }, { argument := 2696395703854841502696996864, coefficient := (-2696395703854841502696996864) }, { argument := 2987897942109418962448023552, coefficient := (-2987897942109418962448023552) }, { argument := 862799732163007427291958476800, coefficient := (-862799732163007427291958476800) }, { argument := 3119638050198394806180895522816, coefficient := (-3119638050198394806180895522816) }, { argument := 862772399017600734658480308224, coefficient := (-862772399017600734658480308224) }, { argument := 5263748071927333282985803776, coefficient := (-5263748071927333282985803776) }, { argument := 176578727527461773830520832, coefficient := (-176578727527461773830520832) }, { argument := 200072531291805878188863651840, coefficient := (-200072531291805878188863651840) }, { argument := 1847616441689782950568132608, coefficient := (-1847616441689782950568132608) }, { argument := 163658332830330424525848576, coefficient := (-163658332830330424525848576) }, { argument := 200072604621072335698151866368, coefficient := (-200072604621072335698151866368) }, { argument := 163658332830330424525848576, coefficient := (-163658332830330424525848576) }, { argument := 159351534597953308090957824, coefficient := (-159351534597953308090957824) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13
