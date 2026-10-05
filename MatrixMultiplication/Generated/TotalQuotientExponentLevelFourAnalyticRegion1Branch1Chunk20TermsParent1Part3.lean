import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 20, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 12988970572217629899745320985690112
def positiveArguments : Array ℕ := #[
    1749, 31, 751, 569
  ]
def positiveCoefficients : Array ℕ := #[
    138570056237448326451108369137664, 599627206528856070654263296, 14526452648489384163269410816, 11006060661771584006525026304
  ]
def positiveScales : Array ℕ := #[
    10, 4, 9, 9
  ]
def negativeArguments : Array ℕ := #[
    10504953225, 2876084055, 172991775, 3373805325, 6747608175, 21624075,
    89877657, 10504953225, 2876084055, 2117937, 1001306223, 38008785837,
    4005227639, 2117937, 4555450075, 88843540225, 177687015275, 569433975,
    175024911, 20457014175, 5600795265, 4555450075, 88843540225, 177687015275,
    569433975, 5425772241, 634167439425, 173624653215, 175024911, 20457014175,
    5600795265, 201969039, 8250471, 3386684109, 86328099, 3823389,
    6773365743, 3823389, 7445547, 140660469, 7445547, 86328099,
    140660469, 25246233, 7445547, 7445547, 8250471, 454701249,
    2912805, 2413467, 6678066483, 16228485, 56837637, 64997163,
    64997163, 46521657, 2413467, 231789747, 27091721475, 7417269405
  ]
def negativeCoefficients : Array ℕ := #[
    24222772955983098995225395200, 6631798312132723262997135360, 797783750070436542126489600, 31117861692396738872711577600, 31117850278473843264926515200, 797787554711401744721510400,
    6631800546494599191066574848, 24222772955983098995225395200, 6631798312132723262997135360, 156276167212960746483744768, 18470839635093744727640506368, 175284586221893822378460315648,
    18470852303395237347675078656, 156276167212960746483744768, 21008305418521495609330892800, 819437024566447456981404876800, 819436723999811205976398233600, 21008405607400245944333107200,
    6457279479481583422880612352, 23585331562404596390087884800, 6457277303918704229760368640, 21008305418521495609330892800, 819437024566447456981404876800, 819436723999811205976398233600,
    21008405607400245944333107200, 200175663863929086109298982912, 731145278434542488092724428800, 200175596421479831122571427840, 6457279479481583422880612352, 23585331562404596390087884800,
    6457277303918704229760368640, 931417793311515826251104256, 152194327024562518030811136, 31236647508611031569711235072, 1592472348622861469151657984, 141058156754472577687093248,
    31236636094688135961926172672, 141058156754472577687093248, 137346099997775930905853952, 5189455345861912200172535808, 137346099997775930905853952, 1592472348622861469151657984,
    5189455345861912200172535808, 931421597952481028846125056, 137346099997775930905853952, 137346099997775930905853952, 152194327024562518030811136, 8387757570299081183025168384,
    214927073486486201979371520, 11130152019835892602503168, 30797145829779659530942021632, 299362709499034352756981760, 8387754747947237905463771136, 299746507844545935260516352,
    299746507844545935260516352, 214543275140974619475836928, 11130152019835892602503168, 8551532283637772641112162304, 31234628285346627651738009600, 8551529402486932628601569280
  ]
def negativeScales : Array ℕ := #[
    33, 31, 27, 31, 32, 24,
    26, 33, 31, 21, 29, 35,
    31, 21, 32, 36, 37, 29,
    27, 34, 32, 32, 36, 37,
    29, 32, 39, 37, 27, 34,
    32, 27, 22, 31, 26, 21,
    32, 21, 22, 27, 22, 26,
    27, 24, 22, 22, 22, 28,
    21, 21, 32, 23, 25, 25,
    25, 25, 21, 27, 34, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10772314573899120, 4954196309696329, 9552669097514181, 9152284842306581
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    33290350687066327, 31421458693866276, 27366128204771312, 31651729583781036, 32651729054605441, 24366135084986112,
    26421459179933871, 33290350687066327, 31421458693866276, 21014228244990891, 29899236110033063, 35145613888966518,
    31899237099511140, 21014228244990891, 32084946452227257, 36370547831214722, 37370547302039127, 29084953332442057,
    27382985032119223, 34251876539251692, 32382984546051628, 32084946452227257, 36370547831214722, 37370547302039127,
    29084953332442057, 32337181342506095, 39206072849638567, 37337180856438501, 27382985032119223, 34251876539251692,
    32382984546051628, 27589558909978022, 22976045067178793, 31657226280574445, 26363326883984466, 21866420562290529,
    32657225753411184, 21866420562290529, 22827946413243993, 27067641691860356, 22827946413243993, 26363326883984466,
    27067641691860356, 24589564803064328, 22827946413243993, 22827946413243993, 22976045067178793, 28760343726347414,
    21473977691691822, 21202675669874317, 32636783310118384, 23952024999282572, 25760343240902564, 25953873424015716,
    25953873424015716, 25471399147590036, 21202675669874317, 27788241511112828, 34657133017763469, 32788241025045228
  ]

abbrev PositiveTerm := Fin 4
abbrev NegativeTerm := Fin 60
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
noncomputable def positiveFloor : ℝ := 17970884859 / 1000000000000
noncomputable def negativeCeiling : ℝ := 44662897 / 20000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 24222772955983098995225395200, coefficient := (-24222772955983098995225395200) }, { argument := 6631798312132723262997135360, coefficient := (-6631798312132723262997135360) }, { argument := 797783750070436542126489600, coefficient := (-797783750070436542126489600) }, { argument := 31117861692396738872711577600, coefficient := (-31117861692396738872711577600) }, { argument := 31117850278473843264926515200, coefficient := (-31117850278473843264926515200) }, { argument := 797787554711401744721510400, coefficient := (-797787554711401744721510400) }, { argument := 6631800546494599191066574848, coefficient := (-6631800546494599191066574848) }, { argument := 24222772955983098995225395200, coefficient := (-24222772955983098995225395200) }, { argument := 6631798312132723262997135360, coefficient := (-6631798312132723262997135360) }, { argument := 156276167212960746483744768, coefficient := (-156276167212960746483744768) }, { argument := 18470839635093744727640506368, coefficient := (-18470839635093744727640506368) }, { argument := 175284586221893822378460315648, coefficient := (-175284586221893822378460315648) }, { argument := 18470852303395237347675078656, coefficient := (-18470852303395237347675078656) }, { argument := 156276167212960746483744768, coefficient := (-156276167212960746483744768) }, { argument := 21008305418521495609330892800, coefficient := (-21008305418521495609330892800) }, { argument := 819437024566447456981404876800, coefficient := (-819437024566447456981404876800) }, { argument := 819436723999811205976398233600, coefficient := (-819436723999811205976398233600) }, { argument := 21008405607400245944333107200, coefficient := (-21008405607400245944333107200) }, { argument := 6457279479481583422880612352, coefficient := (-6457279479481583422880612352) }, { argument := 23585331562404596390087884800, coefficient := (-23585331562404596390087884800) }, { argument := 6457277303918704229760368640, coefficient := (-6457277303918704229760368640) }, { argument := 21008305418521495609330892800, coefficient := (-21008305418521495609330892800) }, { argument := 819437024566447456981404876800, coefficient := (-819437024566447456981404876800) }, { argument := 819436723999811205976398233600, coefficient := (-819436723999811205976398233600) }, { argument := 21008405607400245944333107200, coefficient := (-21008405607400245944333107200) }, { argument := 200175663863929086109298982912, coefficient := (-200175663863929086109298982912) }, { argument := 731145278434542488092724428800, coefficient := (-731145278434542488092724428800) }, { argument := 200175596421479831122571427840, coefficient := (-200175596421479831122571427840) }, { argument := 6457279479481583422880612352, coefficient := (-6457279479481583422880612352) }, { argument := 23585331562404596390087884800, coefficient := (-23585331562404596390087884800) }, { argument := 6457277303918704229760368640, coefficient := (-6457277303918704229760368640) }, { argument := 931417793311515826251104256, coefficient := (-931417793311515826251104256) }, { argument := 152194327024562518030811136, coefficient := (-152194327024562518030811136) }, { argument := 31236647508611031569711235072, coefficient := (-31236647508611031569711235072) }, { argument := 1592472348622861469151657984, coefficient := (-1592472348622861469151657984) }, { argument := 141058156754472577687093248, coefficient := (-141058156754472577687093248) }, { argument := 31236636094688135961926172672, coefficient := (-31236636094688135961926172672) }, { argument := 141058156754472577687093248, coefficient := (-141058156754472577687093248) }, { argument := 137346099997775930905853952, coefficient := (-137346099997775930905853952) }, { argument := 5189455345861912200172535808, coefficient := (-5189455345861912200172535808) }, { argument := 137346099997775930905853952, coefficient := (-137346099997775930905853952) }, { argument := 1592472348622861469151657984, coefficient := (-1592472348622861469151657984) }, { argument := 5189455345861912200172535808, coefficient := (-5189455345861912200172535808) }, { argument := 931421597952481028846125056, coefficient := (-931421597952481028846125056) }, { argument := 137346099997775930905853952, coefficient := (-137346099997775930905853952) }, { argument := 137346099997775930905853952, coefficient := (-137346099997775930905853952) }, { argument := 152194327024562518030811136, coefficient := (-152194327024562518030811136) }, { argument := 8387757570299081183025168384, coefficient := (-8387757570299081183025168384) }, { argument := 214927073486486201979371520, coefficient := (-214927073486486201979371520) }, { argument := 11130152019835892602503168, coefficient := (-11130152019835892602503168) }, { argument := 30797145829779659530942021632, coefficient := (-30797145829779659530942021632) }, { argument := 299362709499034352756981760, coefficient := (-299362709499034352756981760) }, { argument := 8387754747947237905463771136, coefficient := (-8387754747947237905463771136) }, { argument := 299746507844545935260516352, coefficient := (-299746507844545935260516352) }, { argument := 299746507844545935260516352, coefficient := (-299746507844545935260516352) }, { argument := 214543275140974619475836928, coefficient := (-214543275140974619475836928) }, { argument := 11130152019835892602503168, coefficient := (-11130152019835892602503168) }, { argument := 8551532283637772641112162304, coefficient := (-8551532283637772641112162304) }, { argument := 31234628285346627651738009600, coefficient := (-31234628285346627651738009600) }, { argument := 8551529402486932628601569280, coefficient := (-8551529402486932628601569280) }, { argument := 138570056237448326451108369137664, coefficient := 138570056237448326451108369137664 }, { argument := 599627206528856070654263296, coefficient := 599627206528856070654263296 }, { argument := 14526452648489384163269410816, coefficient := 14526452648489384163269410816 }, { argument := 11006060661771584006525026304, coefficient := 11006060661771584006525026304 }] }

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


end Parent1

namespace Parent1

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1562104271293187789246723960864768)
def positiveArguments : Array ℕ := #[
    317, 31, 317, 633, 31, 751,
    31, 75, 225, 475, 1225, 1025,
    28675, 875, 1025, 925, 475, 475,
    925, 28675, 925, 75, 1225, 3315,
    49725, 87295, 3315, 27625, 3315, 87295,
    173485, 27625, 2677415, 171275, 49725, 87295,
    3315, 171275, 3315, 87295, 87295, 3315,
    4761, 21689, 529, 226941, 10051, 529,
    10051, 19573, 369771, 19573, 226941, 369771,
    4761, 19573, 19573, 21689, 49, 245
  ]
def positiveCoefficients : Array ℕ := #[
    12263343514170798348219449344, 599627206528856070654263296, 12263343514170798348219449344, 12244000701056964281424150528, 599627206528856070654263296, 14526452648489384163269410816,
    599627206528856070654263296, 92845502946403520617434316800, 69634127209802640463075737600, 73502689832569453822135500800, 94779784257786927296964198400, 1268888540267514781771602329600,
    2218620664156767461420774195200, 67699845898419233783545856000, 1268888540267514781771602329600, 71568408521186047142605619200, 73502689832569453822135500800, 73502689832569453822135500800,
    71568408521186047142605619200, 2218620664156767461420774195200, 71568408521186047142605619200, 92845502946403520617434316800, 94779784257786927296964198400, 128242850944719862852831150080,
    1923642764170797942792467251200, 3377061741544289721791220285440, 128242850944719862852831150080, 2137380849078664380880519168000, 128242850944719862852831150080, 3377061741544289721791220285440,
    3355687933053503077982415093760, 2137380849078664380880519168000, 51788737973176037948734979440640, 3312940316071929790364804710400, 1923642764170797942792467251200, 3377061741544289721791220285440,
    128242850944719862852831150080, 3312940316071929790364804710400, 128242850944719862852831150080, 3377061741544289721791220285440, 3377061741544289721791220285440, 128242850944719862852831150080,
    368364532939855968049670651904, 419526273625947074723236020224, 327435140390983082710818357248, 4389677350866616952591908601856, 388829229214292410719096799232, 327435140390983082710818357248,
    388829229214292410719096799232, 378596881077074189384383725568, 14304822695831073425928876982272, 378596881077074189384383725568, 4389677350866616952591908601856, 14304822695831073425928876982272,
    368364532939855968049670651904, 378596881077074189384383725568, 378596881077074189384383725568, 419526273625947074723236020224, 7582382740622954183757135872, 151647654812459083675142717440
  ]
def positiveScales : Array ℕ := #[
    8, 4, 8, 9, 4, 9,
    4, 6, 7, 8, 10, 10,
    14, 9, 10, 9, 8, 8,
    9, 14, 9, 6, 10, 11,
    15, 16, 11, 14, 11, 16,
    17, 14, 21, 17, 15, 16,
    11, 17, 11, 16, 16, 11,
    12, 14, 9, 17, 13, 9,
    13, 14, 18, 14, 17, 18,
    12, 14, 14, 14, 5, 7
  ]
def negativeArguments : Array ℕ := #[
    1, 25, 1105, 529
  ]
def negativeCoefficients : Array ℕ := #[
    79228162514264337593543950336, 7922816251426433759354395033600, 87547119578262093040866065121280, 41911697970045834586984749727744
  ]
def negativeScales : Array ℕ := #[
    0, 4, 10, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8308339030139406, 4954196309696329, 8308339030139406, 9306061689428341, 4954196309696329, 9552669097514181,
    4954196309696329, 6228818690495880, 7813781191164178, 8891783702985444, 10258566033889932, 10001408194392808,
    14807505865743947, 9773139206696762, 10001408194392808, 9853309555289512, 8891783702985444, 8891783702985444,
    9853309555289512, 14807505865743947, 9853309555289512, 6228818690495880, 10258566033889932, 11694793154995974,
    15601683750608099, 16413611402455895, 11694793154995974, 14753686844038404, 11694793154995974, 16413611402455895,
    17404451403170420, 14753686844038404, 21352409343730139, 17385955059553030, 15601683750608099, 16413611402455895,
    11694793154995974, 17385955059553030, 11694793154995974, 16413611402455895, 16413611402455895, 11694793154995974,
    12217048913556337, 14404675916732108, 9047123912114025, 17791957749579621, 13295051425557610, 9047123912114025,
    13295051425557610, 14256577277742975, 18496272557489446, 14256577277742975, 17791957749579621, 18496272557489446,
    12217048913556337, 14256577277742975, 14256577277742975, 14404675916732108, 5614709844114682, 7936637938489789
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 4643856189792934, 10109830654278794, 9047123912114026
  ]

abbrev PositiveTerm := Fin 60
abbrev NegativeTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 30503728479 / 1000000000000
noncomputable def negativeCeiling : ℝ := 15660931627 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 12263343514170798348219449344, coefficient := 12263343514170798348219449344 }, { argument := 599627206528856070654263296, coefficient := 599627206528856070654263296 }, { argument := 12263343514170798348219449344, coefficient := 12263343514170798348219449344 }, { argument := 12244000701056964281424150528, coefficient := 12244000701056964281424150528 }, { argument := 599627206528856070654263296, coefficient := 599627206528856070654263296 }, { argument := 14526452648489384163269410816, coefficient := 14526452648489384163269410816 }, { argument := 599627206528856070654263296, coefficient := 599627206528856070654263296 }, { argument := 79228162514264337593543950336, coefficient := (-79228162514264337593543950336) }, { argument := 92845502946403520617434316800, coefficient := 92845502946403520617434316800 }, { argument := 69634127209802640463075737600, coefficient := 69634127209802640463075737600 }, { argument := 73502689832569453822135500800, coefficient := 73502689832569453822135500800 }, { argument := 94779784257786927296964198400, coefficient := 94779784257786927296964198400 }, { argument := 1268888540267514781771602329600, coefficient := 1268888540267514781771602329600 }, { argument := 2218620664156767461420774195200, coefficient := 2218620664156767461420774195200 }, { argument := 67699845898419233783545856000, coefficient := 67699845898419233783545856000 }, { argument := 1268888540267514781771602329600, coefficient := 1268888540267514781771602329600 }, { argument := 71568408521186047142605619200, coefficient := 71568408521186047142605619200 }, { argument := 73502689832569453822135500800, coefficient := 73502689832569453822135500800 }, { argument := 73502689832569453822135500800, coefficient := 73502689832569453822135500800 }, { argument := 71568408521186047142605619200, coefficient := 71568408521186047142605619200 }, { argument := 2218620664156767461420774195200, coefficient := 2218620664156767461420774195200 }, { argument := 71568408521186047142605619200, coefficient := 71568408521186047142605619200 }, { argument := 92845502946403520617434316800, coefficient := 92845502946403520617434316800 }, { argument := 94779784257786927296964198400, coefficient := 94779784257786927296964198400 }, { argument := 7922816251426433759354395033600, coefficient := (-7922816251426433759354395033600) }, { argument := 128242850944719862852831150080, coefficient := 128242850944719862852831150080 }, { argument := 1923642764170797942792467251200, coefficient := 1923642764170797942792467251200 }, { argument := 3377061741544289721791220285440, coefficient := 3377061741544289721791220285440 }, { argument := 128242850944719862852831150080, coefficient := 128242850944719862852831150080 }, { argument := 2137380849078664380880519168000, coefficient := 2137380849078664380880519168000 }, { argument := 128242850944719862852831150080, coefficient := 128242850944719862852831150080 }, { argument := 3377061741544289721791220285440, coefficient := 3377061741544289721791220285440 }, { argument := 3355687933053503077982415093760, coefficient := 3355687933053503077982415093760 }, { argument := 2137380849078664380880519168000, coefficient := 2137380849078664380880519168000 }, { argument := 51788737973176037948734979440640, coefficient := 51788737973176037948734979440640 }, { argument := 3312940316071929790364804710400, coefficient := 3312940316071929790364804710400 }, { argument := 1923642764170797942792467251200, coefficient := 1923642764170797942792467251200 }, { argument := 3377061741544289721791220285440, coefficient := 3377061741544289721791220285440 }, { argument := 128242850944719862852831150080, coefficient := 128242850944719862852831150080 }, { argument := 3312940316071929790364804710400, coefficient := 3312940316071929790364804710400 }, { argument := 128242850944719862852831150080, coefficient := 128242850944719862852831150080 }, { argument := 3377061741544289721791220285440, coefficient := 3377061741544289721791220285440 }, { argument := 3377061741544289721791220285440, coefficient := 3377061741544289721791220285440 }, { argument := 128242850944719862852831150080, coefficient := 128242850944719862852831150080 }, { argument := 87547119578262093040866065121280, coefficient := (-87547119578262093040866065121280) }, { argument := 368364532939855968049670651904, coefficient := 368364532939855968049670651904 }, { argument := 419526273625947074723236020224, coefficient := 419526273625947074723236020224 }, { argument := 327435140390983082710818357248, coefficient := 327435140390983082710818357248 }, { argument := 4389677350866616952591908601856, coefficient := 4389677350866616952591908601856 }, { argument := 388829229214292410719096799232, coefficient := 388829229214292410719096799232 }, { argument := 327435140390983082710818357248, coefficient := 327435140390983082710818357248 }, { argument := 388829229214292410719096799232, coefficient := 388829229214292410719096799232 }, { argument := 378596881077074189384383725568, coefficient := 378596881077074189384383725568 }, { argument := 14304822695831073425928876982272, coefficient := 14304822695831073425928876982272 }, { argument := 378596881077074189384383725568, coefficient := 378596881077074189384383725568 }, { argument := 4389677350866616952591908601856, coefficient := 4389677350866616952591908601856 }, { argument := 14304822695831073425928876982272, coefficient := 14304822695831073425928876982272 }, { argument := 368364532939855968049670651904, coefficient := 368364532939855968049670651904 }, { argument := 378596881077074189384383725568, coefficient := 378596881077074189384383725568 }, { argument := 378596881077074189384383725568, coefficient := 378596881077074189384383725568 }, { argument := 419526273625947074723236020224, coefficient := 419526273625947074723236020224 }, { argument := 41911697970045834586984749727744, coefficient := (-41911697970045834586984749727744) }, { argument := 7582382740622954183757135872, coefficient := 7582382740622954183757135872 }, { argument := 151647654812459083675142717440, coefficient := 151647654812459083675142717440 }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk20
