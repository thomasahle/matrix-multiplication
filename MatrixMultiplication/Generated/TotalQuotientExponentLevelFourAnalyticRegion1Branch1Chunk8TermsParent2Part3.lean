import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 8, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8

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
def constantNumerator : ℤ := 4025820959061723382947988759379968
def positiveArguments : Array ℕ := #[
    563, 2115, 1575, 1665, 135, 28935,
    52335, 1575, 28935, 855, 855, 1665,
    1665, 52335, 1665, 2115, 135, 1767,
    5415, 16017, 35739, 1767, 17841, 36309,
    1767, 5415, 1767, 1799, 7175, 3563,
    7175, 9, 29, 29, 29, 29,
    1767, 42807, 32433, 18069, 1767, 18069,
    36081, 1767, 42807, 1767, 135, 405
  ]
def positiveCoefficients : Array ℕ := #[
    44605455495530822065165244039168, 40910049735759051272056995840, 30464930654288655202595635200, 32205783834533721214172528640, 41780476325881584277845442560, 559684297448788722721971240960,
    1012306124312505885731963535360, 30464930654288655202595635200, 559684297448788722721971240960, 33076210424656254219960975360, 33076210424656254219960975360, 32205783834533721214172528640,
    32205783834533721214172528640, 1012306124312505885731963535360, 32205783834533721214172528640, 40910049735759051272056995840, 41780476325881584277845442560, 34178750772144796027293007872,
    837930664091291773572344709120, 619627675288560495720602271744, 691292797875315713197184385024, 34178750772144796027293007872, 690190257527827171389852352512, 702318201350201131270504710144,
    34178750772144796027293007872, 837930664091291773572344709120, 34178750772144796027293007872, 556763532668599778635881119744, 555138736367037717025076019200, 551347544996726239933197451264,
    555138736367037717025076019200, 1426106925256758076683791106048, 574404178228416447553193639936, 574404178228416447553193639936, 574404178228416447553193639936, 574404178228416447553193639936,
    34178750772144796027293007872, 828007800963894897306356416512, 627345457720980288371926499328, 699010580307735505848508612608, 34178750772144796027293007872, 699010580307735505848508612608,
    697908039960246964041176580096, 34178750772144796027293007872, 828007800963894897306356416512, 34178750772144796027293007872, 41780476325881584277845442560, 31335357244411188208384081920
  ]
def positiveScales : Array ℕ := #[
    9, 11, 10, 10, 7, 14,
    15, 10, 14, 9, 9, 10,
    10, 15, 10, 11, 7, 10,
    12, 13, 15, 10, 14, 15,
    10, 12, 10, 10, 12, 11,
    12, 3, 4, 4, 4, 4,
    10, 15, 14, 14, 10, 14,
    15, 10, 15, 10, 7, 8
  ]
def negativeArguments : Array ℕ := #[
    25055787169, 2536256103, 9283973, 1552398735, 60753975665, 60753987185,
    1552410255, 13211469, 49077315, 825543, 45, 57,
    7, 9, 29, 57
  ]
def negativeCoefficients : Array ℕ := #[
    28887355841992410850807250944, 2924104202339058258467094528, 21407384239778685880631296, 7159175541223863671523901440, 280178260138158266289131356160, 280178313264781198572640010240,
    7159228667846795955032555520, 124778796790142697563486158848, 463522134850471364181601812480, 124752530987764976596807581696, 3565267313141895191709477765120, 4516005263313067242832005169152,
    2218388550399401452619230609408, 1426106925256758076683791106048, 2297616712913665790212774559744, 4516005263313067242832005169152
  ]
def negativeScales : Array ℕ := #[
    34, 31, 23, 30, 35, 35,
    30, 23, 25, 19, 5, 5,
    2, 3, 4, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    9136991112080229, 11046441948007312, 10621136113274016, 10701306461953989, 7076815597050830, 14820528023597167,
    15675488477800394, 10621136113274016, 14820528023597167, 9739780609762119, 9739780609762119, 10701306461953989,
    10701306461953989, 15675488477800394, 10701306461953989, 11046441948007312, 7076815597050830, 10787086324520917,
    12402745622495688, 13967316333526543, 15125211646966780, 10787086324520917, 14122908861097359, 15148039576421041,
    10787086324520917, 12402745622495688, 10787086324520917, 10812979471199464, 12808763116402615, 11798876768094178,
    12808763116402615, 3169925001442312, 4857980995002857, 4857980995002857, 4857980995002857, 4857980995002857,
    10787086324520917, 15385559111679012, 14985174855320818, 14141229044304148, 10787086324520917, 14141229044304148,
    15138951703593082, 10787086324520917, 15385559111679012, 10787086324520917, 7076815597050830, 8661778097770205
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    34544424812005373, 31240053285533397, 23146310896312608, 30531852016617525, 35822259769869925, 35822260043429728,
    30531862722491494, 23655287554831676, 25548552986112051, 19654983837111453, 5491853096329881, 5832890015409720,
    2807354922807594, 3169925001442313, 4857980997143165, 5832890015409720
  ]

abbrev PositiveTerm := Fin 48
abbrev NegativeTerm := Fin 16
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
noncomputable def positiveFloor : ℝ := 950166693 / 125000000000
noncomputable def negativeCeiling : ℝ := 1601158427 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 28887355841992410850807250944, coefficient := (-28887355841992410850807250944) }, { argument := 2924104202339058258467094528, coefficient := (-2924104202339058258467094528) }, { argument := 21407384239778685880631296, coefficient := (-21407384239778685880631296) }, { argument := 7159175541223863671523901440, coefficient := (-7159175541223863671523901440) }, { argument := 280178260138158266289131356160, coefficient := (-280178260138158266289131356160) }, { argument := 280178313264781198572640010240, coefficient := (-280178313264781198572640010240) }, { argument := 7159228667846795955032555520, coefficient := (-7159228667846795955032555520) }, { argument := 124778796790142697563486158848, coefficient := (-124778796790142697563486158848) }, { argument := 463522134850471364181601812480, coefficient := (-463522134850471364181601812480) }, { argument := 124752530987764976596807581696, coefficient := (-124752530987764976596807581696) }, { argument := 44605455495530822065165244039168, coefficient := 44605455495530822065165244039168 }, { argument := 40910049735759051272056995840, coefficient := 40910049735759051272056995840 }, { argument := 30464930654288655202595635200, coefficient := 30464930654288655202595635200 }, { argument := 32205783834533721214172528640, coefficient := 32205783834533721214172528640 }, { argument := 41780476325881584277845442560, coefficient := 41780476325881584277845442560 }, { argument := 559684297448788722721971240960, coefficient := 559684297448788722721971240960 }, { argument := 1012306124312505885731963535360, coefficient := 1012306124312505885731963535360 }, { argument := 30464930654288655202595635200, coefficient := 30464930654288655202595635200 }, { argument := 559684297448788722721971240960, coefficient := 559684297448788722721971240960 }, { argument := 33076210424656254219960975360, coefficient := 33076210424656254219960975360 }, { argument := 33076210424656254219960975360, coefficient := 33076210424656254219960975360 }, { argument := 32205783834533721214172528640, coefficient := 32205783834533721214172528640 }, { argument := 32205783834533721214172528640, coefficient := 32205783834533721214172528640 }, { argument := 1012306124312505885731963535360, coefficient := 1012306124312505885731963535360 }, { argument := 32205783834533721214172528640, coefficient := 32205783834533721214172528640 }, { argument := 40910049735759051272056995840, coefficient := 40910049735759051272056995840 }, { argument := 41780476325881584277845442560, coefficient := 41780476325881584277845442560 }, { argument := 3565267313141895191709477765120, coefficient := (-3565267313141895191709477765120) }, { argument := 34178750772144796027293007872, coefficient := 34178750772144796027293007872 }, { argument := 837930664091291773572344709120, coefficient := 837930664091291773572344709120 }, { argument := 619627675288560495720602271744, coefficient := 619627675288560495720602271744 }, { argument := 691292797875315713197184385024, coefficient := 691292797875315713197184385024 }, { argument := 34178750772144796027293007872, coefficient := 34178750772144796027293007872 }, { argument := 690190257527827171389852352512, coefficient := 690190257527827171389852352512 }, { argument := 702318201350201131270504710144, coefficient := 702318201350201131270504710144 }, { argument := 34178750772144796027293007872, coefficient := 34178750772144796027293007872 }, { argument := 837930664091291773572344709120, coefficient := 837930664091291773572344709120 }, { argument := 34178750772144796027293007872, coefficient := 34178750772144796027293007872 }, { argument := 4516005263313067242832005169152, coefficient := (-4516005263313067242832005169152) }, { argument := 556763532668599778635881119744, coefficient := 556763532668599778635881119744 }, { argument := 555138736367037717025076019200, coefficient := 555138736367037717025076019200 }, { argument := 551347544996726239933197451264, coefficient := 551347544996726239933197451264 }, { argument := 555138736367037717025076019200, coefficient := 555138736367037717025076019200 }, { argument := 2218388550399401452619230609408, coefficient := (-2218388550399401452619230609408) }, { argument := 1426106925256758076683791106048, coefficient := 1426106925256758076683791106048 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 574404178228416447553193639936, coefficient := 574404178228416447553193639936 }, { argument := 574404178228416447553193639936, coefficient := 574404178228416447553193639936 }, { argument := 574404178228416447553193639936, coefficient := 574404178228416447553193639936 }, { argument := 574404178228416447553193639936, coefficient := 574404178228416447553193639936 }, { argument := 2297616712913665790212774559744, coefficient := (-2297616712913665790212774559744) }, { argument := 34178750772144796027293007872, coefficient := 34178750772144796027293007872 }, { argument := 828007800963894897306356416512, coefficient := 828007800963894897306356416512 }, { argument := 627345457720980288371926499328, coefficient := 627345457720980288371926499328 }, { argument := 699010580307735505848508612608, coefficient := 699010580307735505848508612608 }, { argument := 34178750772144796027293007872, coefficient := 34178750772144796027293007872 }, { argument := 699010580307735505848508612608, coefficient := 699010580307735505848508612608 }, { argument := 697908039960246964041176580096, coefficient := 697908039960246964041176580096 }, { argument := 34178750772144796027293007872, coefficient := 34178750772144796027293007872 }, { argument := 828007800963894897306356416512, coefficient := 828007800963894897306356416512 }, { argument := 34178750772144796027293007872, coefficient := 34178750772144796027293007872 }, { argument := 4516005263313067242832005169152, coefficient := (-4516005263313067242832005169152) }, { argument := 41780476325881584277845442560, coefficient := 41780476325881584277845442560 }, { argument := 31335357244411188208384081920, coefficient := 31335357244411188208384081920 }] }

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
def constantNumerator : ℤ := (-1715615294605203177381359681273856)
def positiveArguments : Array ℕ := #[
    855, 2205, 1845, 51615, 1575, 1845,
    1665, 855, 855, 1665, 51615, 1665,
    135, 2205, 13211469, 49077315, 825543, 2978349,
    466237173, 116559315, 11913483, 815239, 76698393, 3141247787,
    306794069, 815239, 2453895, 456822393, 3654579363, 19630941,
    19548265, 883546015, 2456575
  ]
def positiveCoefficients : Array ℕ := #[
    33076210424656254219960975360, 42650902916004117283633889280, 570999843120381651797221048320, 998379298870545357639348387840, 30464930654288655202595635200, 570999843120381651797221048320,
    32205783834533721214172528640, 33076210424656254219960975360, 33076210424656254219960975360, 32205783834533721214172528640, 998379298870545357639348387840, 32205783834533721214172528640,
    41780476325881584277845442560, 42650902916004117283633889280, 249557593580285395126972317696, 927044269700942728363203624960, 249505061975529953193615163392, 56259421967553299810265071616,
    2201742798843096311946603921408, 2201743209688980321605737512960, 56259832813437309469398663168, 7699714658256333388736626688, 1448791681572655265482499162112, 14834123263717246436997702090752,
    1448794028588797251696170369024, 7699714658256333388736626688, 92705532003851264333300367360, 17258262058620038668652824756224, 17258263092818298417105126555648, 92704497805591515880998567936,
    184628142868507570186622074880, 8344856174618081586049848442880, 185613559082487979053364019200
  ]
def positiveScales : Array ℕ := #[
    9, 11, 10, 15, 10, 10,
    10, 9, 9, 10, 15, 10,
    7, 11, 23, 25, 19, 21,
    28, 26, 23, 19, 26, 31,
    28, 19, 21, 28, 31, 24,
    24, 29, 21
  ]
def negativeArguments : Array ℕ := #[
    45, 9, 57, 7, 219, 55
  ]
def negativeCoefficients : Array ℕ := #[
    3565267313141895191709477765120, 1426106925256758076683791106048, 4516005263313067242832005169152, 17747108403195211620953844875264, 34701935181247779865972250247168, 8715097876569077135289834536960
  ]
def negativeScales : Array ℕ := #[
    5, 3, 5, 2, 7, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    9739780609762119, 11106562940444882, 10849405100841772, 15655502772343977, 10621136113274016, 10849405100841772,
    10701306461953989, 9739780609762119, 9739780609762119, 10701306461953989, 15655502772343977, 10701306461953989,
    7076815597050830, 11106562940444882, 23655287554805800, 25548552986110697, 19654983837085775, 21506081386732502,
    28796488793911883, 26796489063119197, 23506091922268319, 19636863544291835, 26192693014622685, 31548690603717977,
    28192695351760487, 19636863544291835, 21226642087998928, 28767058131054078, 31767058217507317, 24226625993586968,
    24220537231489815, 29718730031258324, 21228216855014500
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    5491853096329881, 3169925001442313, 5832890015409720, 2807354922807594, 7774787059984115, 5781359713964302
  ]

abbrev PositiveTerm := Fin 33
abbrev NegativeTerm := Fin 6
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
noncomputable def positiveFloor : ℝ := 24785200191 / 1000000000000
noncomputable def negativeCeiling : ℝ := 5060978483 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 33076210424656254219960975360, coefficient := 33076210424656254219960975360 }, { argument := 42650902916004117283633889280, coefficient := 42650902916004117283633889280 }, { argument := 570999843120381651797221048320, coefficient := 570999843120381651797221048320 }, { argument := 998379298870545357639348387840, coefficient := 998379298870545357639348387840 }, { argument := 30464930654288655202595635200, coefficient := 30464930654288655202595635200 }, { argument := 570999843120381651797221048320, coefficient := 570999843120381651797221048320 }, { argument := 32205783834533721214172528640, coefficient := 32205783834533721214172528640 }, { argument := 33076210424656254219960975360, coefficient := 33076210424656254219960975360 }, { argument := 33076210424656254219960975360, coefficient := 33076210424656254219960975360 }, { argument := 32205783834533721214172528640, coefficient := 32205783834533721214172528640 }, { argument := 998379298870545357639348387840, coefficient := 998379298870545357639348387840 }, { argument := 32205783834533721214172528640, coefficient := 32205783834533721214172528640 }, { argument := 41780476325881584277845442560, coefficient := 41780476325881584277845442560 }, { argument := 42650902916004117283633889280, coefficient := 42650902916004117283633889280 }, { argument := 3565267313141895191709477765120, coefficient := (-3565267313141895191709477765120) }, { argument := 249557593580285395126972317696, coefficient := 249557593580285395126972317696 }, { argument := 927044269700942728363203624960, coefficient := 927044269700942728363203624960 }, { argument := 249505061975529953193615163392, coefficient := 249505061975529953193615163392 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 56259421967553299810265071616, coefficient := 56259421967553299810265071616 }, { argument := 2201742798843096311946603921408, coefficient := 2201742798843096311946603921408 }, { argument := 2201743209688980321605737512960, coefficient := 2201743209688980321605737512960 }, { argument := 56259832813437309469398663168, coefficient := 56259832813437309469398663168 }, { argument := 4516005263313067242832005169152, coefficient := (-4516005263313067242832005169152) }, { argument := 7699714658256333388736626688, coefficient := 7699714658256333388736626688 }, { argument := 1448791681572655265482499162112, coefficient := 1448791681572655265482499162112 }, { argument := 14834123263717246436997702090752, coefficient := 14834123263717246436997702090752 }, { argument := 1448794028588797251696170369024, coefficient := 1448794028588797251696170369024 }, { argument := 7699714658256333388736626688, coefficient := 7699714658256333388736626688 }, { argument := 17747108403195211620953844875264, coefficient := (-17747108403195211620953844875264) }, { argument := 92705532003851264333300367360, coefficient := 92705532003851264333300367360 }, { argument := 17258262058620038668652824756224, coefficient := 17258262058620038668652824756224 }, { argument := 17258263092818298417105126555648, coefficient := 17258263092818298417105126555648 }, { argument := 92704497805591515880998567936, coefficient := 92704497805591515880998567936 }, { argument := 34701935181247779865972250247168, coefficient := (-34701935181247779865972250247168) }, { argument := 184628142868507570186622074880, coefficient := 184628142868507570186622074880 }, { argument := 8344856174618081586049848442880, coefficient := 8344856174618081586049848442880 }, { argument := 185613559082487979053364019200, coefficient := 185613559082487979053364019200 }, { argument := 8715097876569077135289834536960, coefficient := (-8715097876569077135289834536960) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8
