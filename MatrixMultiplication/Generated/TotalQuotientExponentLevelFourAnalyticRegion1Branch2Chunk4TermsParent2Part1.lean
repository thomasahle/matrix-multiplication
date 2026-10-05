import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 4, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-10094398438171115753775103207276544)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1050503894213995, 2615459055, 17047370575526465, 64718699595, 2058978405, 17047378336548455,
    1057313235, 1057313235, 35781705795, 1947682275, 64718699595, 35781705795,
    1050494389279045, 2058978405, 1947682275, 2615459055, 54918175, 4055563525,
    42270460375, 4055563525, 54918175, 3821214627, 138482082909, 1107857070405,
    30569309883, 29824347088717, 14048505, 4584249, 811022811033647, 46286127,
    238594766116201, 92720133, 41553999, 14048505, 4584249, 117749018911853,
    1518427441503123, 3077792865, 2726045109, 127596498489, 34735090905, 759213975787251,
    127596498489, 3077792865, 3077792865, 1319054085, 3077792865, 34735090905,
    1319054085, 58874254420237, 2726045109, 294476381058175, 16988060845199805, 553304038545,
    132157677461505775, 567769503605, 18081831325, 553304038545, 314623865055, 567769503605,
    8863713715515, 10849098795, 8494035081473835, 553304038545
  ]
def negativeCoefficients : Array ℕ := #[
    295690559158337676935660830720, 24123351911425617107028541440, 9596816471448468213922351022080, 596924644106127504159025397760, 18990723845164847509788426240, 9596820840515435986200517672960,
    19503986651790924469512437760, 19503986651790924469512437760, 330027984660567485102539407360, 17964198231912693590340403200, 596924644106127504159025397760, 330027984660567485102539407360,
    295687883756993989385409003520, 18990723845164847509788426240, 17964198231912693590340403200, 24123351911425617107028541440, 126632689902524256852377600, 18702985605086592244488601600,
    194938091103876420210786304000, 18702985605086592244488601600, 126632689902524256852377600, 70488968274984504784670687232, 2554543542216550534072126930944, 2554544481001332404270986690560,
    70488029490202634585810927616, 67158459217657109203770146816, 518298352706458008850268160, 21141117018289734571524096, 228282626847506551315399442432, 426914169466108833605615616,
    67158456235842091795250937856, 427596140982827857301471232, 383267992396091317070856192, 518298352706458008850268160, 21141117018289734571524096, 66286804711832832148699611136,
    854798657467825044437782757376, 56775257292544292046074019840, 50286656459110658669379846144, 2353739952328050507395811508224, 640749332301571295948549652480, 854798944612484094032162586624,
    2353739952328050507395811508224, 56775257292544292046074019840, 56775257292544292046074019840, 48664506250752250325206302720, 56775257292544292046074019840, 640749332301571295948549652480,
    48664506250752250325206302720, 66286517567173782554319781888, 50286656459110658669379846144, 165775465000376139572156825600, 9563428061523644391171985244160, 2551664498497385017118482759680,
    74398158371223450752140496076800, 2618374681464636912990861393920, 83387728709064869840473292800, 2551664498497385017118482759680, 1450946479537728735224235294720, 2618374681464636912990861393920,
    40876664613183599195800008130560, 1601044391214045500937087221760, 9563433306949370984451318743040, 2551664498497385017118482759680
  ]
def negativeScales : Array ℕ := #[
    49, 31, 53, 35, 30, 53,
    29, 29, 35, 30, 35, 35,
    49, 30, 30, 31, 25, 31,
    35, 31, 25, 31, 37, 40,
    34, 44, 23, 22, 49, 25,
    47, 26, 25, 23, 22, 46,
    50, 31, 31, 36, 35, 49,
    36, 31, 31, 30, 31, 35,
    30, 45, 31, 48, 53, 39,
    56, 39, 34, 39, 38, 39,
    43, 33, 52, 39
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    49900002937764255, 31284417038794438, 53920398756372577, 35913463574139040, 30939281561434072, 53920399413176895,
    29977755717092648, 29977755717092648, 35058503114444748, 30859111206120832, 35913463574139040, 35058503114444748,
    49899989884232800, 30939281561434072, 30859111206120832, 31284417038794438, 25710780348016212, 31917255252347632,
    35298930773972696, 31917255252347632, 25710780348016212, 31831384147335099, 37010908373317385, 40010908903502084,
    34831364933134162, 44761555788771740, 23743913275719710, 22128253977578882, 49526735821044206, 25464076514124703,
    47761555724716521, 26466379299994130, 25308483987412933, 23743913275719710, 22128253977578882, 46742708367927028,
    50431499393860839, 31519248995759208, 31344162289200608, 36892797786716831, 35015674821878198, 49431499878492047,
    36892797786716831, 31519248995759208, 31519248995759208, 30296856574422251, 31519248995759208, 35015674821878198,
    30296856574422251, 45742702118371382, 31344162289200608, 48065145253491637, 53915370704964814, 39009281497756039,
    56875037854033513, 39046514403955014, 34073821749950749, 39009281497756039, 38194837150912115, 39046514403955014,
    43011048423930227, 33336856155784544, 52915371496265625, 39009281497756039
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
noncomputable def negativeCeiling : ℝ := 112182245931 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 295690559158337676935660830720, coefficient := (-295690559158337676935660830720) }, { argument := 24123351911425617107028541440, coefficient := (-24123351911425617107028541440) }, { argument := 9596816471448468213922351022080, coefficient := (-9596816471448468213922351022080) }, { argument := 596924644106127504159025397760, coefficient := (-596924644106127504159025397760) }, { argument := 18990723845164847509788426240, coefficient := (-18990723845164847509788426240) }, { argument := 9596820840515435986200517672960, coefficient := (-9596820840515435986200517672960) }, { argument := 19503986651790924469512437760, coefficient := (-19503986651790924469512437760) }, { argument := 19503986651790924469512437760, coefficient := (-19503986651790924469512437760) }, { argument := 330027984660567485102539407360, coefficient := (-330027984660567485102539407360) }, { argument := 17964198231912693590340403200, coefficient := (-17964198231912693590340403200) }, { argument := 596924644106127504159025397760, coefficient := (-596924644106127504159025397760) }, { argument := 330027984660567485102539407360, coefficient := (-330027984660567485102539407360) }, { argument := 295687883756993989385409003520, coefficient := (-295687883756993989385409003520) }, { argument := 18990723845164847509788426240, coefficient := (-18990723845164847509788426240) }, { argument := 17964198231912693590340403200, coefficient := (-17964198231912693590340403200) }, { argument := 24123351911425617107028541440, coefficient := (-24123351911425617107028541440) }, { argument := 126632689902524256852377600, coefficient := (-126632689902524256852377600) }, { argument := 18702985605086592244488601600, coefficient := (-18702985605086592244488601600) }, { argument := 194938091103876420210786304000, coefficient := (-194938091103876420210786304000) }, { argument := 18702985605086592244488601600, coefficient := (-18702985605086592244488601600) }, { argument := 126632689902524256852377600, coefficient := (-126632689902524256852377600) }, { argument := 70488968274984504784670687232, coefficient := (-70488968274984504784670687232) }, { argument := 2554543542216550534072126930944, coefficient := (-2554543542216550534072126930944) }, { argument := 2554544481001332404270986690560, coefficient := (-2554544481001332404270986690560) }, { argument := 70488029490202634585810927616, coefficient := (-70488029490202634585810927616) }, { argument := 67158459217657109203770146816, coefficient := (-67158459217657109203770146816) }, { argument := 518298352706458008850268160, coefficient := (-518298352706458008850268160) }, { argument := 21141117018289734571524096, coefficient := (-21141117018289734571524096) }, { argument := 228282626847506551315399442432, coefficient := (-228282626847506551315399442432) }, { argument := 426914169466108833605615616, coefficient := (-426914169466108833605615616) }, { argument := 67158456235842091795250937856, coefficient := (-67158456235842091795250937856) }, { argument := 427596140982827857301471232, coefficient := (-427596140982827857301471232) }, { argument := 383267992396091317070856192, coefficient := (-383267992396091317070856192) }, { argument := 518298352706458008850268160, coefficient := (-518298352706458008850268160) }, { argument := 21141117018289734571524096, coefficient := (-21141117018289734571524096) }, { argument := 66286804711832832148699611136, coefficient := (-66286804711832832148699611136) }, { argument := 854798657467825044437782757376, coefficient := (-854798657467825044437782757376) }, { argument := 56775257292544292046074019840, coefficient := (-56775257292544292046074019840) }, { argument := 50286656459110658669379846144, coefficient := (-50286656459110658669379846144) }, { argument := 2353739952328050507395811508224, coefficient := (-2353739952328050507395811508224) }, { argument := 640749332301571295948549652480, coefficient := (-640749332301571295948549652480) }, { argument := 854798944612484094032162586624, coefficient := (-854798944612484094032162586624) }, { argument := 2353739952328050507395811508224, coefficient := (-2353739952328050507395811508224) }, { argument := 56775257292544292046074019840, coefficient := (-56775257292544292046074019840) }, { argument := 56775257292544292046074019840, coefficient := (-56775257292544292046074019840) }, { argument := 48664506250752250325206302720, coefficient := (-48664506250752250325206302720) }, { argument := 56775257292544292046074019840, coefficient := (-56775257292544292046074019840) }, { argument := 640749332301571295948549652480, coefficient := (-640749332301571295948549652480) }, { argument := 48664506250752250325206302720, coefficient := (-48664506250752250325206302720) }, { argument := 66286517567173782554319781888, coefficient := (-66286517567173782554319781888) }, { argument := 50286656459110658669379846144, coefficient := (-50286656459110658669379846144) }, { argument := 165775465000376139572156825600, coefficient := (-165775465000376139572156825600) }, { argument := 9563428061523644391171985244160, coefficient := (-9563428061523644391171985244160) }, { argument := 2551664498497385017118482759680, coefficient := (-2551664498497385017118482759680) }, { argument := 74398158371223450752140496076800, coefficient := (-74398158371223450752140496076800) }, { argument := 2618374681464636912990861393920, coefficient := (-2618374681464636912990861393920) }, { argument := 83387728709064869840473292800, coefficient := (-83387728709064869840473292800) }, { argument := 2551664498497385017118482759680, coefficient := (-2551664498497385017118482759680) }, { argument := 1450946479537728735224235294720, coefficient := (-1450946479537728735224235294720) }, { argument := 2618374681464636912990861393920, coefficient := (-2618374681464636912990861393920) }, { argument := 40876664613183599195800008130560, coefficient := (-40876664613183599195800008130560) }, { argument := 1601044391214045500937087221760, coefficient := (-1601044391214045500937087221760) }, { argument := 9563433306949370984451318743040, coefficient := (-9563433306949370984451318743040) }, { argument := 2551664498497385017118482759680, coefficient := (-2551664498497385017118482759680) }] }

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

namespace Parent2

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-9892949136448197718286637046169600)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    18081831325, 10849098795, 18081831325, 278460202405, 314623865055, 294476381058175,
    8477537728195145, 27260492325, 132739313990143195, 674552182425, 21460387575, 132739378903061725,
    11020199025, 11020199025, 372946735425, 20300366625, 674552182425, 372946735425,
    8477472760779335, 21460387575, 20300366625, 27260492325, 28201225, 2082586675,
    21706452625, 2082586675, 28201225, 3921115663, 142102529521, 1136820653945,
    31368507527, 370499247775923, 1181328135, 385486023, 10236073758494673, 3892165329,
    2963993095219863, 7796765691, 3494244273, 1181328135, 385486023, 124876295,
    4525558265, 36204479425, 998997055, 12556305405, 21281242115, 12556305405,
    18058858232195, 18053411341949, 92720133, 7796765691, 3898381905, 46361007,
    28201225, 2082586675, 21706452625, 2082586675, 28201225, 41553999,
    3494244273, 1747121715, 20777421, 954388825
  ]
def negativeCoefficients : Array ℕ := #[
    83387728709064869840473292800, 1601044391214045500937087221760, 83387728709064869840473292800, 2568342044239197991086577418240, 1450946479537728735224235294720, 165775465000376139572156825600,
    2386214734607436013959768965120, 251433662621299233053579673600, 74725590627928019944335044771840, 6221645736778106554070492774400, 197937138659320672829413785600, 74725627170652482849255666483200,
    203286791055518528851830374400, 203286791055518528851830374400, 3439826490755221422413866598400, 187237833866924960784580608000, 6221645736778106554070492774400, 3439826490755221422413866598400,
    2386196447905583942705359093760, 197937138659320672829413785600, 187237833866924960784580608000, 251433662621299233053579673600, 130055195035024912442982400, 19208471702521365007853158400,
    200206688160737945081348096000, 19208471702521365007853158400, 130055195035024912442982400, 72331817118774949354204561408, 2621328994300643358492313255936, 2621329957628818218761731440640,
    72330853790600089084786376704, 834290137112347945842354683904, 43583315546835214284431032320, 1777740502568278477391265792, 2881198622780845111719638335488, 35898888858314268607965560832,
    834289887447556129724854960128, 35956235326139051784655601664, 32228714917528145299802947584, 43583315546835214284431032320, 1777740502568278477391265792, 2303561054738055711917342720,
    83481815105116030525232906240, 83481845784357268113430937600, 2303530375496818123719311360, 57905738079342740339026821120, 196284813433027187064092753920, 57905738079342740339026821120,
    5083116700328126008178769920, 5081583537022987658848108544, 427596140982827857301471232, 35956235326139051784655601664, 35956226651557651122738954240, 427604815564228519218118656,
    130055195035024912442982400, 19208471702521365007853158400, 200206688160737945081348096000, 19208471702521365007853158400, 130055195035024912442982400, 383267992396091317070856192,
    32228714917528145299802947584, 32228707142225518231226941440, 383275767698718385646862336, 2200670800197921544758886400
  ]
def negativeScales : Array ℕ := #[
    34, 33, 34, 38, 38, 48,
    52, 34, 56, 39, 34, 56,
    33, 33, 38, 34, 39, 38,
    52, 34, 34, 34, 24, 30,
    34, 30, 24, 31, 37, 40,
    34, 48, 30, 28, 53, 31,
    51, 32, 31, 30, 28, 26,
    32, 35, 29, 33, 34, 33,
    44, 44, 26, 32, 31, 25,
    24, 30, 34, 30, 24, 25,
    31, 30, 24, 29
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34073821749950749, 33336856155784544, 34073821749950749, 38018680195758288, 38194837150912115, 48065145253491637,
    52912566728566701, 34666092566383301, 56881373339573226, 39295139096146964, 34320957080302695, 56881374045087857,
    33359431228117332, 33359431228117332, 38440178642001725, 34240786731618712, 39295139096146964, 38440178642001725,
    52912555672462937, 34320957080302695, 34240786731618712, 34666092566383301, 24749254495959001, 30955729405709606,
    34337404921787332, 30955729405709606, 24749254495959001, 31868617054786071, 37048141279516360, 40048141809701060,
    34868597840584706, 48396463941855545, 30137762608715976, 28522103310772461, 53184511966411818, 31857925849331139,
    51396463510122992, 32860228635289971, 31702333320682418, 30137762608715976, 28522103310772461, 26895924402380042,
    32075448625512095, 35075449155696795, 29895905188178154, 33547692973774089, 34308863307459596, 33547692973774089,
    44037771915124045, 44037336705612240, 26466379299994130, 32860228635289971, 31860228287234134, 25466408567444016,
    24749254495959001, 30955729405709606, 34337404921787332, 30955729405709606, 24749254495959001, 25308483987412933,
    31702333320682418, 30702332972626595, 24308513254862818, 29830001910798741
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
noncomputable def negativeCeiling : ℝ := 15454531523 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 83387728709064869840473292800, coefficient := (-83387728709064869840473292800) }, { argument := 1601044391214045500937087221760, coefficient := (-1601044391214045500937087221760) }, { argument := 83387728709064869840473292800, coefficient := (-83387728709064869840473292800) }, { argument := 2568342044239197991086577418240, coefficient := (-2568342044239197991086577418240) }, { argument := 1450946479537728735224235294720, coefficient := (-1450946479537728735224235294720) }, { argument := 165775465000376139572156825600, coefficient := (-165775465000376139572156825600) }, { argument := 2386214734607436013959768965120, coefficient := (-2386214734607436013959768965120) }, { argument := 251433662621299233053579673600, coefficient := (-251433662621299233053579673600) }, { argument := 74725590627928019944335044771840, coefficient := (-74725590627928019944335044771840) }, { argument := 6221645736778106554070492774400, coefficient := (-6221645736778106554070492774400) }, { argument := 197937138659320672829413785600, coefficient := (-197937138659320672829413785600) }, { argument := 74725627170652482849255666483200, coefficient := (-74725627170652482849255666483200) }, { argument := 203286791055518528851830374400, coefficient := (-203286791055518528851830374400) }, { argument := 203286791055518528851830374400, coefficient := (-203286791055518528851830374400) }, { argument := 3439826490755221422413866598400, coefficient := (-3439826490755221422413866598400) }, { argument := 187237833866924960784580608000, coefficient := (-187237833866924960784580608000) }, { argument := 6221645736778106554070492774400, coefficient := (-6221645736778106554070492774400) }, { argument := 3439826490755221422413866598400, coefficient := (-3439826490755221422413866598400) }, { argument := 2386196447905583942705359093760, coefficient := (-2386196447905583942705359093760) }, { argument := 197937138659320672829413785600, coefficient := (-197937138659320672829413785600) }, { argument := 187237833866924960784580608000, coefficient := (-187237833866924960784580608000) }, { argument := 251433662621299233053579673600, coefficient := (-251433662621299233053579673600) }, { argument := 130055195035024912442982400, coefficient := (-130055195035024912442982400) }, { argument := 19208471702521365007853158400, coefficient := (-19208471702521365007853158400) }, { argument := 200206688160737945081348096000, coefficient := (-200206688160737945081348096000) }, { argument := 19208471702521365007853158400, coefficient := (-19208471702521365007853158400) }, { argument := 130055195035024912442982400, coefficient := (-130055195035024912442982400) }, { argument := 72331817118774949354204561408, coefficient := (-72331817118774949354204561408) }, { argument := 2621328994300643358492313255936, coefficient := (-2621328994300643358492313255936) }, { argument := 2621329957628818218761731440640, coefficient := (-2621329957628818218761731440640) }, { argument := 72330853790600089084786376704, coefficient := (-72330853790600089084786376704) }, { argument := 834290137112347945842354683904, coefficient := (-834290137112347945842354683904) }, { argument := 43583315546835214284431032320, coefficient := (-43583315546835214284431032320) }, { argument := 1777740502568278477391265792, coefficient := (-1777740502568278477391265792) }, { argument := 2881198622780845111719638335488, coefficient := (-2881198622780845111719638335488) }, { argument := 35898888858314268607965560832, coefficient := (-35898888858314268607965560832) }, { argument := 834289887447556129724854960128, coefficient := (-834289887447556129724854960128) }, { argument := 35956235326139051784655601664, coefficient := (-35956235326139051784655601664) }, { argument := 32228714917528145299802947584, coefficient := (-32228714917528145299802947584) }, { argument := 43583315546835214284431032320, coefficient := (-43583315546835214284431032320) }, { argument := 1777740502568278477391265792, coefficient := (-1777740502568278477391265792) }, { argument := 2303561054738055711917342720, coefficient := (-2303561054738055711917342720) }, { argument := 83481815105116030525232906240, coefficient := (-83481815105116030525232906240) }, { argument := 83481845784357268113430937600, coefficient := (-83481845784357268113430937600) }, { argument := 2303530375496818123719311360, coefficient := (-2303530375496818123719311360) }, { argument := 57905738079342740339026821120, coefficient := (-57905738079342740339026821120) }, { argument := 196284813433027187064092753920, coefficient := (-196284813433027187064092753920) }, { argument := 57905738079342740339026821120, coefficient := (-57905738079342740339026821120) }, { argument := 5083116700328126008178769920, coefficient := (-5083116700328126008178769920) }, { argument := 5081583537022987658848108544, coefficient := (-5081583537022987658848108544) }, { argument := 427596140982827857301471232, coefficient := (-427596140982827857301471232) }, { argument := 35956235326139051784655601664, coefficient := (-35956235326139051784655601664) }, { argument := 35956226651557651122738954240, coefficient := (-35956226651557651122738954240) }, { argument := 427604815564228519218118656, coefficient := (-427604815564228519218118656) }, { argument := 130055195035024912442982400, coefficient := (-130055195035024912442982400) }, { argument := 19208471702521365007853158400, coefficient := (-19208471702521365007853158400) }, { argument := 200206688160737945081348096000, coefficient := (-200206688160737945081348096000) }, { argument := 19208471702521365007853158400, coefficient := (-19208471702521365007853158400) }, { argument := 130055195035024912442982400, coefficient := (-130055195035024912442982400) }, { argument := 383267992396091317070856192, coefficient := (-383267992396091317070856192) }, { argument := 32228714917528145299802947584, coefficient := (-32228714917528145299802947584) }, { argument := 32228707142225518231226941440, coefficient := (-32228707142225518231226941440) }, { argument := 383275767698718385646862336, coefficient := (-383275767698718385646862336) }, { argument := 2200670800197921544758886400, coefficient := (-2200670800197921544758886400) }] }

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

end TermShard3


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4
