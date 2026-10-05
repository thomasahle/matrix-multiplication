import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 9, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9

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
def constantNumerator : ℤ := (-152055858938692043847168073662464)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2101415121, 25097007, 94722921, 4831694931, 73437, 47485780977,
    2421, 5649, 73437, 73437, 2421, 906261,
    36315, 4831694931, 73437, 5649, 36315, 5649,
    73437, 73437, 101333865, 50195535, 4202828721, 2101415121,
    25097007, 42016681, 2380366611, 49049, 23850326577, 1617,
    3773, 49049, 49049, 1617, 605297, 24255,
    2380366611, 49049, 3773, 24255, 3773, 49049,
    49049, 44224425, 117308019, 4385801613, 35084511963, 940365093,
    274034919979, 97482503, 1550175313365, 51450173, 8545411, 205604311,
    89923991, 274437573163, 97482503, 8447107, 189005316867, 10836056759549,
    13117765, 123306991, 1456071915, 102318567
  ]
def negativeCoefficients : Array ℕ := #[
    620228270875366245247878168576, 7407329042321554125977812992, 436832370400302008666947584, 44564519917198365454655029248, 5548742838439970168931090432, 437979024411472255975126204416,
    2926809409287017231963652096, 213413186093845006497349632, 5548742838439970168931090432, 5548742838439970168931090432, 2926809409287017231963652096, 68475145138110840656149610496,
    5487767642413157309931847680, 44564519917198365454655029248, 5548742838439970168931090432, 213413186093845006497349632, 5487767642413157309931847680, 213413186093845006497349632,
    5548742838439970168931090432, 5548742838439970168931090432, 467319968413708438166568960, 231486046946982594493808640, 19382126450480761135939190784, 19382133464855195163996192768,
    231479032572548566436806656, 387535480616847358451253248, 43910013674720339578507493376, 3706037657892371649385201664, 439960870440312165885838098432, 1954833050316855375499886592,
    142539909918937371130200064, 3706037657892371649385201664, 3706037657892371649385201664, 1954833050316855375499886592, 45734948239704762222632763392, 3665311969344103829062287360,
    43910013674720339578507493376, 3706037657892371649385201664, 142539909918937371130200064, 3665311969344103829062287360, 142539909918937371130200064, 3706037657892371649385201664,
    3706037657892371649385201664, 407898324890981268612710400, 4327902008573714962902417408, 161807519826147084741919113216, 161798753283115529364729495552, 4336668551605270340092035072,
    154267945437991011193192448, 449558696126405896633843712, 1745342240907388966938869760, 474544086939540591197814784, 19704376215207801648054272, 474091263183548196765827072,
    414701212015890264032804864, 154494619029168754163449856, 449558696126405896633843712, 19477702624030058677796864, 851204274613263722486956032, 48801261184470420773408866304,
    241980053774064576354058240, 284326563184525877216018432, 3357473246115145996912558080, 7549777677750814782246617088
  ]
def negativeScales : Array ℕ := #[
    30, 24, 26, 32, 16, 35,
    11, 12, 16, 16, 11, 19,
    15, 32, 16, 12, 15, 12,
    16, 16, 26, 25, 31, 30,
    24, 25, 31, 15, 34, 10,
    11, 15, 15, 10, 19, 14,
    31, 15, 11, 14, 11, 15,
    15, 25, 26, 32, 35, 29,
    37, 26, 40, 25, 23, 27,
    26, 37, 26, 23, 37, 43,
    23, 26, 30, 26
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30968714053497423, 24581011986808319, 26497210234697627, 32169882221019373, 16164219503476477, 35466776530002572,
    11241387363998937, 12463779785335462, 16164219503476477, 16164219503476477, 11241387363998937, 19789567076199844,
    15148277959607456, 32169882221019373, 16164219503476477, 12463779785335462, 15148277959607456, 12463779785335462,
    16164219503476477, 16164219503476477, 26594541151434862, 25581055703294337, 31968713531387334, 30968714053497423,
    24581011986808319, 25324458868727121, 31148536640603430, 15581936102954605, 34473289969728950, 10659103963500476,
    11881496387932734, 15581936102954605, 15581936102954605, 10659103963500476, 19207283675153107, 14565994559084324,
    31148536640603430, 15581936102954605, 11881496387932734, 14565994559084324, 11881496387932734, 15581936102954605,
    15581936102954605, 25398340049523177, 26805726397028242, 32030193408721383, 35030115243066318, 29808645746019874,
    37995568811816402, 26538639958968101, 40495568521515738, 25616672592376086, 23026718450740203, 27615295273605803,
    26422202730777234, 37997687080542612, 26538639958968101, 23010025895170172, 37459635862915140, 43300905089082463,
    23645018599270986, 26877679358953490, 30439434465602364, 26608492723234253
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
noncomputable def negativeCeiling : ℝ := 446461719 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 620228270875366245247878168576, coefficient := (-620228270875366245247878168576) }, { argument := 7407329042321554125977812992, coefficient := (-7407329042321554125977812992) }, { argument := 436832370400302008666947584, coefficient := (-436832370400302008666947584) }, { argument := 44564519917198365454655029248, coefficient := (-44564519917198365454655029248) }, { argument := 5548742838439970168931090432, coefficient := (-5548742838439970168931090432) }, { argument := 437979024411472255975126204416, coefficient := (-437979024411472255975126204416) }, { argument := 2926809409287017231963652096, coefficient := (-2926809409287017231963652096) }, { argument := 213413186093845006497349632, coefficient := (-213413186093845006497349632) }, { argument := 5548742838439970168931090432, coefficient := (-5548742838439970168931090432) }, { argument := 5548742838439970168931090432, coefficient := (-5548742838439970168931090432) }, { argument := 2926809409287017231963652096, coefficient := (-2926809409287017231963652096) }, { argument := 68475145138110840656149610496, coefficient := (-68475145138110840656149610496) }, { argument := 5487767642413157309931847680, coefficient := (-5487767642413157309931847680) }, { argument := 44564519917198365454655029248, coefficient := (-44564519917198365454655029248) }, { argument := 5548742838439970168931090432, coefficient := (-5548742838439970168931090432) }, { argument := 213413186093845006497349632, coefficient := (-213413186093845006497349632) }, { argument := 5487767642413157309931847680, coefficient := (-5487767642413157309931847680) }, { argument := 213413186093845006497349632, coefficient := (-213413186093845006497349632) }, { argument := 5548742838439970168931090432, coefficient := (-5548742838439970168931090432) }, { argument := 5548742838439970168931090432, coefficient := (-5548742838439970168931090432) }, { argument := 467319968413708438166568960, coefficient := (-467319968413708438166568960) }, { argument := 231486046946982594493808640, coefficient := (-231486046946982594493808640) }, { argument := 19382126450480761135939190784, coefficient := (-19382126450480761135939190784) }, { argument := 19382133464855195163996192768, coefficient := (-19382133464855195163996192768) }, { argument := 231479032572548566436806656, coefficient := (-231479032572548566436806656) }, { argument := 387535480616847358451253248, coefficient := (-387535480616847358451253248) }, { argument := 43910013674720339578507493376, coefficient := (-43910013674720339578507493376) }, { argument := 3706037657892371649385201664, coefficient := (-3706037657892371649385201664) }, { argument := 439960870440312165885838098432, coefficient := (-439960870440312165885838098432) }, { argument := 1954833050316855375499886592, coefficient := (-1954833050316855375499886592) }, { argument := 142539909918937371130200064, coefficient := (-142539909918937371130200064) }, { argument := 3706037657892371649385201664, coefficient := (-3706037657892371649385201664) }, { argument := 3706037657892371649385201664, coefficient := (-3706037657892371649385201664) }, { argument := 1954833050316855375499886592, coefficient := (-1954833050316855375499886592) }, { argument := 45734948239704762222632763392, coefficient := (-45734948239704762222632763392) }, { argument := 3665311969344103829062287360, coefficient := (-3665311969344103829062287360) }, { argument := 43910013674720339578507493376, coefficient := (-43910013674720339578507493376) }, { argument := 3706037657892371649385201664, coefficient := (-3706037657892371649385201664) }, { argument := 142539909918937371130200064, coefficient := (-142539909918937371130200064) }, { argument := 3665311969344103829062287360, coefficient := (-3665311969344103829062287360) }, { argument := 142539909918937371130200064, coefficient := (-142539909918937371130200064) }, { argument := 3706037657892371649385201664, coefficient := (-3706037657892371649385201664) }, { argument := 3706037657892371649385201664, coefficient := (-3706037657892371649385201664) }, { argument := 407898324890981268612710400, coefficient := (-407898324890981268612710400) }, { argument := 4327902008573714962902417408, coefficient := (-4327902008573714962902417408) }, { argument := 161807519826147084741919113216, coefficient := (-161807519826147084741919113216) }, { argument := 161798753283115529364729495552, coefficient := (-161798753283115529364729495552) }, { argument := 4336668551605270340092035072, coefficient := (-4336668551605270340092035072) }, { argument := 154267945437991011193192448, coefficient := (-154267945437991011193192448) }, { argument := 449558696126405896633843712, coefficient := (-449558696126405896633843712) }, { argument := 1745342240907388966938869760, coefficient := (-1745342240907388966938869760) }, { argument := 474544086939540591197814784, coefficient := (-474544086939540591197814784) }, { argument := 19704376215207801648054272, coefficient := (-19704376215207801648054272) }, { argument := 474091263183548196765827072, coefficient := (-474091263183548196765827072) }, { argument := 414701212015890264032804864, coefficient := (-414701212015890264032804864) }, { argument := 154494619029168754163449856, coefficient := (-154494619029168754163449856) }, { argument := 449558696126405896633843712, coefficient := (-449558696126405896633843712) }, { argument := 19477702624030058677796864, coefficient := (-19477702624030058677796864) }, { argument := 851204274613263722486956032, coefficient := (-851204274613263722486956032) }, { argument := 48801261184470420773408866304, coefficient := (-48801261184470420773408866304) }, { argument := 241980053774064576354058240, coefficient := (-241980053774064576354058240) }, { argument := 284326563184525877216018432, coefficient := (-284326563184525877216018432) }, { argument := 3357473246115145996912558080, coefficient := (-3357473246115145996912558080) }, { argument := 7549777677750814782246617088, coefficient := (-7549777677750814782246617088) }] }

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
def constantNumerator : ℤ := (-88306523126739949508782509260800)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    5418028575895, 1456071915, 13117765, 102318567, 102318567, 102318567,
    102318567, 102318567, 94502462313, 123306991, 139215589283, 21456712425087,
    1183, 856715572865181, 39, 91, 1183, 1183,
    39, 14599, 585, 21456712425087, 1183, 91,
    585, 91, 1183, 1183, 560296027359, 60492055,
    5064947433, 2532474633, 30245111, 45841977, 2713788483, 45591,
    27393196353, 1503, 3507, 45591, 45591, 1503,
    562623, 22545, 2713788483, 45591, 3507, 22545,
    3507, 45591, 45591, 47894073, 120487309, 4503208563,
    36023767333, 965799643, 3956157, 227814447, 273, 2288994789,
    9, 21, 273, 273
  ]
def negativeCoefficients : Array ℕ := #[
    48801262950966842212839587840, 3357473246115145996912558080, 241980053774064576354058240, 235930552429712961945206784, 235930552429712961945206784, 235930552429712961945206784,
    7549777677750814782246617088, 235930552429712961945206784, 851202508116842283056234496, 284326563184525877216018432, 156742819004770704101998592, 24158110520554426192298508288,
    178769905575513289209675776, 241143995919883135360734068736, 94296213929941075627081728, 6875765599058203431141376, 178769905575513289209675776, 178769905575513289209675776,
    94296213929941075627081728, 2206138505069246415191932928, 176805401118639516800778240, 24158110520554426192298508288, 178769905575513289209675776, 6875765599058203431141376,
    176805401118639516800778240, 6875765599058203431141376, 178769905575513289209675776, 178769905575513289209675776, 157709311251947602002837504, 278970364269440562595102720,
    23357947260835789061260050432, 23357955714056260838662078464, 278961911048968785193074688, 422817608775939784930492416, 50060561616081484262594838528, 3444758565128159919001829376,
    505315282484664852508676456448, 1817015506880787649583382528, 132490714043390766115454976, 3444758565128159919001829376, 3444758565128159919001829376, 1817015506880787649583382528,
    42510591963065094385044553728, 3406904075401476842968842240, 50060561616081484262594838528, 3444758565128159919001829376, 132490714043390766115454976, 3406904075401476842968842240,
    132490714043390766115454976, 3444758565128159919001829376, 3444758565128159919001829376, 441744853639281322946985984, 4445197106505923043616882688, 166139071744396712024123375616,
    166130304140677372408634540032, 4453964710225262659105718272, 18244553923603639648124928, 2101217400051334370008498176, 165018374377396882347393024, 21112250529368897774275264512,
    87042659012253300578844672, 6346860552976803167207424, 165018374377396882347393024, 165018374377396882347393024
  ]
def negativeScales : Array ℕ := #[
    42, 30, 23, 26, 26, 26,
    26, 26, 36, 26, 37, 44,
    10, 49, 5, 6, 10, 10,
    5, 13, 9, 44, 10, 6,
    9, 6, 10, 10, 39, 25,
    32, 31, 24, 25, 31, 15,
    34, 10, 11, 15, 15, 10,
    19, 14, 31, 15, 11, 14,
    11, 15, 15, 25, 26, 32,
    35, 29, 21, 27, 8, 31,
    3, 4, 8, 8
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    42300905141304793, 30439434465602364, 23645018599270986, 26608492723234253, 26608492723234253, 26608492723234253,
    26608492723234253, 26608492723234253, 36459632868900251, 26877679358953490, 37018529816168797, 44286494278345837,
    10208234358339789, 49605809641605890, 5285402218862249, 6507794640199048, 10208234358339789, 10208234358339789,
    5285402218862249, 13833581931803590, 9192292814470767, 44286494278345837, 10208234358339789, 6507794640199048,
    9192292814470767, 6507794640199048, 10208234358339789, 10208234358339789, 39027398307291452, 25850242337846561,
    32237900149953690, 31237900672063656, 24850198621359096, 25450165927909198, 31337661133173844, 15476461433394026,
    34673098564482965, 10553629293917849, 11776021715645854, 15476461433394026, 15476461433394026, 10553629293917849,
    19101809005595810, 14460519889524952, 31337661133173844, 15476461433394026, 11776021715645854, 14460519889524952,
    11776021715645854, 15476461433394026, 15476461433394026, 25513343794441069, 26844305955182006, 32068306150639567,
    35068230013749878, 29847148690969260, 21915668255645692, 27763283998781733, 8092757140919853, 31092067032523192,
    3169925001442313, 4392317422778766, 8092757140919853, 8092757140919853
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
noncomputable def negativeCeiling : ℝ := 628007107 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 48801262950966842212839587840, coefficient := (-48801262950966842212839587840) }, { argument := 3357473246115145996912558080, coefficient := (-3357473246115145996912558080) }, { argument := 241980053774064576354058240, coefficient := (-241980053774064576354058240) }, { argument := 235930552429712961945206784, coefficient := (-235930552429712961945206784) }, { argument := 235930552429712961945206784, coefficient := (-235930552429712961945206784) }, { argument := 235930552429712961945206784, coefficient := (-235930552429712961945206784) }, { argument := 7549777677750814782246617088, coefficient := (-7549777677750814782246617088) }, { argument := 235930552429712961945206784, coefficient := (-235930552429712961945206784) }, { argument := 851202508116842283056234496, coefficient := (-851202508116842283056234496) }, { argument := 284326563184525877216018432, coefficient := (-284326563184525877216018432) }, { argument := 156742819004770704101998592, coefficient := (-156742819004770704101998592) }, { argument := 24158110520554426192298508288, coefficient := (-24158110520554426192298508288) }, { argument := 178769905575513289209675776, coefficient := (-178769905575513289209675776) }, { argument := 241143995919883135360734068736, coefficient := (-241143995919883135360734068736) }, { argument := 94296213929941075627081728, coefficient := (-94296213929941075627081728) }, { argument := 6875765599058203431141376, coefficient := (-6875765599058203431141376) }, { argument := 178769905575513289209675776, coefficient := (-178769905575513289209675776) }, { argument := 178769905575513289209675776, coefficient := (-178769905575513289209675776) }, { argument := 94296213929941075627081728, coefficient := (-94296213929941075627081728) }, { argument := 2206138505069246415191932928, coefficient := (-2206138505069246415191932928) }, { argument := 176805401118639516800778240, coefficient := (-176805401118639516800778240) }, { argument := 24158110520554426192298508288, coefficient := (-24158110520554426192298508288) }, { argument := 178769905575513289209675776, coefficient := (-178769905575513289209675776) }, { argument := 6875765599058203431141376, coefficient := (-6875765599058203431141376) }, { argument := 176805401118639516800778240, coefficient := (-176805401118639516800778240) }, { argument := 6875765599058203431141376, coefficient := (-6875765599058203431141376) }, { argument := 178769905575513289209675776, coefficient := (-178769905575513289209675776) }, { argument := 178769905575513289209675776, coefficient := (-178769905575513289209675776) }, { argument := 157709311251947602002837504, coefficient := (-157709311251947602002837504) }, { argument := 278970364269440562595102720, coefficient := (-278970364269440562595102720) }, { argument := 23357947260835789061260050432, coefficient := (-23357947260835789061260050432) }, { argument := 23357955714056260838662078464, coefficient := (-23357955714056260838662078464) }, { argument := 278961911048968785193074688, coefficient := (-278961911048968785193074688) }, { argument := 422817608775939784930492416, coefficient := (-422817608775939784930492416) }, { argument := 50060561616081484262594838528, coefficient := (-50060561616081484262594838528) }, { argument := 3444758565128159919001829376, coefficient := (-3444758565128159919001829376) }, { argument := 505315282484664852508676456448, coefficient := (-505315282484664852508676456448) }, { argument := 1817015506880787649583382528, coefficient := (-1817015506880787649583382528) }, { argument := 132490714043390766115454976, coefficient := (-132490714043390766115454976) }, { argument := 3444758565128159919001829376, coefficient := (-3444758565128159919001829376) }, { argument := 3444758565128159919001829376, coefficient := (-3444758565128159919001829376) }, { argument := 1817015506880787649583382528, coefficient := (-1817015506880787649583382528) }, { argument := 42510591963065094385044553728, coefficient := (-42510591963065094385044553728) }, { argument := 3406904075401476842968842240, coefficient := (-3406904075401476842968842240) }, { argument := 50060561616081484262594838528, coefficient := (-50060561616081484262594838528) }, { argument := 3444758565128159919001829376, coefficient := (-3444758565128159919001829376) }, { argument := 132490714043390766115454976, coefficient := (-132490714043390766115454976) }, { argument := 3406904075401476842968842240, coefficient := (-3406904075401476842968842240) }, { argument := 132490714043390766115454976, coefficient := (-132490714043390766115454976) }, { argument := 3444758565128159919001829376, coefficient := (-3444758565128159919001829376) }, { argument := 3444758565128159919001829376, coefficient := (-3444758565128159919001829376) }, { argument := 441744853639281322946985984, coefficient := (-441744853639281322946985984) }, { argument := 4445197106505923043616882688, coefficient := (-4445197106505923043616882688) }, { argument := 166139071744396712024123375616, coefficient := (-166139071744396712024123375616) }, { argument := 166130304140677372408634540032, coefficient := (-166130304140677372408634540032) }, { argument := 4453964710225262659105718272, coefficient := (-4453964710225262659105718272) }, { argument := 18244553923603639648124928, coefficient := (-18244553923603639648124928) }, { argument := 2101217400051334370008498176, coefficient := (-2101217400051334370008498176) }, { argument := 165018374377396882347393024, coefficient := (-165018374377396882347393024) }, { argument := 21112250529368897774275264512, coefficient := (-21112250529368897774275264512) }, { argument := 87042659012253300578844672, coefficient := (-87042659012253300578844672) }, { argument := 6346860552976803167207424, coefficient := (-6346860552976803167207424) }, { argument := 165018374377396882347393024, coefficient := (-165018374377396882347393024) }, { argument := 165018374377396882347393024, coefficient := (-165018374377396882347393024) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9
