import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 4, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-241740695063833916125206835888128)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2155871485, 8598320125, 4269799945, 8598320125, 752927070997, 11701152565,
    20801194294483, 77227606929, 3818270837, 38552218451, 78459307199, 94292140547,
    11701152565, 3818270837, 28667410146519, 892801987025705, 581919387, 47182653,
    10112815293, 18291141813, 892801993374505, 10112815293, 298823469, 298823469,
    581919387, 581919387, 18291141813, 581919387, 28667403797719, 47182653,
    41612375, 7298419625, 1824605125, 10402875, 11810928293, 491728505945,
    5274115, 10060078999031, 205485, 342475, 10479735, 342475,
    205485, 167881245, 10753715, 491729325401, 10479735, 342475,
    10753715, 342475, 10479735, 342475, 11810928293, 2155873027,
    8598326275, 4269802999, 8598326275, 5428414961741, 41941550855, 150513260305115,
    276814235643, 13686190279, 138186372817, 281229135733
  ]
def negativeCoefficients : Array ℕ := #[
    9942202384900790125267517440, 9913188175606332566536192000, 9845488353919264929496432640, 9913188175606332566536192000, 6781764152758496372430209024, 107924083366992534478279147520,
    187360501746989852478339547136, 89037368777768840944580296704, 4402166558390484958982438912, 88895363404917534978161508352, 90457422506281900608768180224, 6794464784502970189969620992,
    107924083366992534478279147520, 4402166558390484958982438912, 8069158603346259033628606464, 251301418505287715149819412480, 5367259001759472546213789696, 6962930596877153573466537984,
    93274257787333536411228831744, 168706005920169366790449659904, 251301420292316047290432225280, 93274257787333536411228831744, 5512320055861079912327675904, 5512320055861079912327675904,
    5367259001759472546213789696, 5367259001759472546213789696, 168706005920169366790449659904, 5367259001759472546213789696, 8069156816317926893015793664, 6962930596877153573466537984,
    95951603990528687865856000, 16829009870614279758020608000, 16829011888226912820002816000, 95949586377895625883648000, 106383384518508896799686656, 17716386529130821816428789760,
    778321996962501214569758720, 181226272125415055961047957504, 485187738366234523368161280, 25270194706574714758758400, 773267958021186271618007040, 808646230610390872280268800,
    485187738366234523368161280, 12387449445162925174743367680, 793484113786446043425013760, 17716416053144711788566151168, 773267958021186271618007040, 25270194706574714758758400,
    793484113786446043425013760, 25270194706574714758758400, 773267958021186271618007040, 808646230610390872280268800, 106383384518508896799686656, 9942209496120630540299665408,
    9913195266073585898645094400, 9845495395963815068117762048, 9913195266073585898645094400, 24447407598909192900272193536, 386842527338329513800855715840, 677851463024434381082108887040,
    319145085054121848885705965568, 15779103088800282799771746304, 318636081728676678472810102784, 324235118308573553014664593408
  ]
def negativeScales : Array ℕ := #[
    31, 33, 31, 33, 39, 33,
    44, 36, 31, 35, 36, 36,
    33, 31, 44, 49, 29, 25,
    33, 34, 49, 33, 28, 28,
    29, 29, 34, 29, 44, 25,
    25, 32, 30, 23, 33, 38,
    22, 43, 17, 18, 23, 18,
    17, 27, 23, 38, 23, 18,
    23, 18, 23, 18, 33, 31,
    33, 31, 33, 42, 35, 47,
    38, 33, 37, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31005624033245834, 33001407678444764, 31991521350796885, 33001407678444764, 39453719175050855, 33445931591324576,
    44241731596193626, 36168397615795627, 31830272294563334, 35166094829926207, 36191225545249889, 36456418473046478,
    33445931591324576, 31830272294563334, 44704476809016208, 49665333566496206, 29116244070255744, 25491753205348156,
    33235465631954742, 34090426086100013, 49665333576755348, 33235465631954742, 28154718218070380, 28154718218070380,
    29116244070255744, 29116244070255744, 34090426086100013, 29116244070255744, 44704476489511123, 25491753205348156,
    25310509295851609, 32764936955822540, 30764937128785751, 23310478959408832, 33459403308280779, 38839071037080442,
    22330497598266673, 43193706867810639, 17648673558313525, 18385639152459137, 23321098900264423, 18385639152459137,
    17648673558313525, 27322865826438611, 23358331806463399, 38839073441301756, 23321098900264423, 18385639152459137,
    23358331806463399, 18385639152459137, 23321098900264423, 18385639152459137, 33459403308280779, 31005625065141739,
    33001408710340669, 31991522382693134, 33001408710340669, 42303668146870785, 35287661157219222, 47096883923273153,
    38010127181690313, 33672001859312080, 37007824395820893, 38032955111144575
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
noncomputable def negativeCeiling : ℝ := 402835209 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 9942202384900790125267517440, coefficient := (-9942202384900790125267517440) }, { argument := 9913188175606332566536192000, coefficient := (-9913188175606332566536192000) }, { argument := 9845488353919264929496432640, coefficient := (-9845488353919264929496432640) }, { argument := 9913188175606332566536192000, coefficient := (-9913188175606332566536192000) }, { argument := 6781764152758496372430209024, coefficient := (-6781764152758496372430209024) }, { argument := 107924083366992534478279147520, coefficient := (-107924083366992534478279147520) }, { argument := 187360501746989852478339547136, coefficient := (-187360501746989852478339547136) }, { argument := 89037368777768840944580296704, coefficient := (-89037368777768840944580296704) }, { argument := 4402166558390484958982438912, coefficient := (-4402166558390484958982438912) }, { argument := 88895363404917534978161508352, coefficient := (-88895363404917534978161508352) }, { argument := 90457422506281900608768180224, coefficient := (-90457422506281900608768180224) }, { argument := 6794464784502970189969620992, coefficient := (-6794464784502970189969620992) }, { argument := 107924083366992534478279147520, coefficient := (-107924083366992534478279147520) }, { argument := 4402166558390484958982438912, coefficient := (-4402166558390484958982438912) }, { argument := 8069158603346259033628606464, coefficient := (-8069158603346259033628606464) }, { argument := 251301418505287715149819412480, coefficient := (-251301418505287715149819412480) }, { argument := 5367259001759472546213789696, coefficient := (-5367259001759472546213789696) }, { argument := 6962930596877153573466537984, coefficient := (-6962930596877153573466537984) }, { argument := 93274257787333536411228831744, coefficient := (-93274257787333536411228831744) }, { argument := 168706005920169366790449659904, coefficient := (-168706005920169366790449659904) }, { argument := 251301420292316047290432225280, coefficient := (-251301420292316047290432225280) }, { argument := 93274257787333536411228831744, coefficient := (-93274257787333536411228831744) }, { argument := 5512320055861079912327675904, coefficient := (-5512320055861079912327675904) }, { argument := 5512320055861079912327675904, coefficient := (-5512320055861079912327675904) }, { argument := 5367259001759472546213789696, coefficient := (-5367259001759472546213789696) }, { argument := 5367259001759472546213789696, coefficient := (-5367259001759472546213789696) }, { argument := 168706005920169366790449659904, coefficient := (-168706005920169366790449659904) }, { argument := 5367259001759472546213789696, coefficient := (-5367259001759472546213789696) }, { argument := 8069156816317926893015793664, coefficient := (-8069156816317926893015793664) }, { argument := 6962930596877153573466537984, coefficient := (-6962930596877153573466537984) }, { argument := 95951603990528687865856000, coefficient := (-95951603990528687865856000) }, { argument := 16829009870614279758020608000, coefficient := (-16829009870614279758020608000) }, { argument := 16829011888226912820002816000, coefficient := (-16829011888226912820002816000) }, { argument := 95949586377895625883648000, coefficient := (-95949586377895625883648000) }, { argument := 106383384518508896799686656, coefficient := (-106383384518508896799686656) }, { argument := 17716386529130821816428789760, coefficient := (-17716386529130821816428789760) }, { argument := 778321996962501214569758720, coefficient := (-778321996962501214569758720) }, { argument := 181226272125415055961047957504, coefficient := (-181226272125415055961047957504) }, { argument := 485187738366234523368161280, coefficient := (-485187738366234523368161280) }, { argument := 25270194706574714758758400, coefficient := (-25270194706574714758758400) }, { argument := 773267958021186271618007040, coefficient := (-773267958021186271618007040) }, { argument := 808646230610390872280268800, coefficient := (-808646230610390872280268800) }, { argument := 485187738366234523368161280, coefficient := (-485187738366234523368161280) }, { argument := 12387449445162925174743367680, coefficient := (-12387449445162925174743367680) }, { argument := 793484113786446043425013760, coefficient := (-793484113786446043425013760) }, { argument := 17716416053144711788566151168, coefficient := (-17716416053144711788566151168) }, { argument := 773267958021186271618007040, coefficient := (-773267958021186271618007040) }, { argument := 25270194706574714758758400, coefficient := (-25270194706574714758758400) }, { argument := 793484113786446043425013760, coefficient := (-793484113786446043425013760) }, { argument := 25270194706574714758758400, coefficient := (-25270194706574714758758400) }, { argument := 773267958021186271618007040, coefficient := (-773267958021186271618007040) }, { argument := 808646230610390872280268800, coefficient := (-808646230610390872280268800) }, { argument := 106383384518508896799686656, coefficient := (-106383384518508896799686656) }, { argument := 9942209496120630540299665408, coefficient := (-9942209496120630540299665408) }, { argument := 9913195266073585898645094400, coefficient := (-9913195266073585898645094400) }, { argument := 9845495395963815068117762048, coefficient := (-9845495395963815068117762048) }, { argument := 9913195266073585898645094400, coefficient := (-9913195266073585898645094400) }, { argument := 24447407598909192900272193536, coefficient := (-24447407598909192900272193536) }, { argument := 386842527338329513800855715840, coefficient := (-386842527338329513800855715840) }, { argument := 677851463024434381082108887040, coefficient := (-677851463024434381082108887040) }, { argument := 319145085054121848885705965568, coefficient := (-319145085054121848885705965568) }, { argument := 15779103088800282799771746304, coefficient := (-15779103088800282799771746304) }, { argument := 318636081728676678472810102784, coefficient := (-318636081728676678472810102784) }, { argument := 324235118308573553014664593408, coefficient := (-324235118308573553014664593408) }] }

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


end Parent3

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4011756937995852561576862951669760)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    679835991963, 41941550855, 13686190279, 278475594276427, 8403232232583605, 91096216337,
    7386179703, 1583104516343, 2863375664863, 8403232234119605, 1583104516343, 46779138119,
    46779138119, 91096216337, 91096216337, 2863375664863, 91096216337, 278475592740427,
    7386179703, 469625375, 82367878625, 20591972125, 117403875, 490998483545,
    10475477811965, 3397810185, 196244696475763, 132382215, 220637025, 6751492965,
    220637025, 132382215, 108156269655, 6928002585, 10475480782493, 6751492965,
    220637025, 6928002585, 220637025, 6751492965, 220637025, 490998483545,
    41612375, 7298419625, 1824605125, 10402875, 42311885, 27259123815,
    289912245007, 13629602987, 42311885, 14484876110151, 21638435, 140660145943547,
    244205195, 21638435, 281320369674947, 21638435, 21638435, 897067691,
    5564169, 244205195, 897067691, 14485051969863
  ]
def negativeCoefficients : Array ℕ := #[
    24493672960620946507834589184, 386842527338329513800855715840, 15779103088800282799771746304, 313535645653773516467442024448, 9461198387842816163389657579520, 210053573606489748514300493824,
    272501933327338052126660100096, 3650390481864132656613384257536, 6602494759576961554652202008576, 9461198389572198420299928043520, 3650390481864132656613384257536, 215730697217475957933605912576,
    215730697217475957933605912576, 210053573606489748514300493824, 210053573606489748514300493824, 6602494759576961554652202008576, 210053573606489748514300493824, 313535643924391259557171560448,
    272501933327338052126660100096, 1082882387893109477343232000, 189927397111218300126232576000, 189927419881418016111460352000, 1082859617693393492115456000, 17690084700261924894995906560,
    1509675455055791128463257108480, 250714139574954820850512035840, 14140920670746917382494164615168, 156289333761010797413306204160, 8140069466719312365276364800, 249086125681610958377456762880,
    260482222935017995688843673600, 156289333761010797413306204160, 3990262052585806921458474024960, 255598181254986408269677854720, 1509675883153992533059248848896, 249086125681610958377456762880,
    8140069466719312365276364800, 255598181254986408269677854720, 8140069466719312365276364800, 249086125681610958377456762880, 260482222935017995688843673600, 17690084700261924894995906560,
    95951603990528687865856000, 16829009870614279758020608000, 16829011888226912820002816000, 95949586377895625883648000, 780516513871230071377756160, 251421040344433076924338667520,
    2673968493739354397726952390656, 251421798127456252875864276992, 780516513871230071377756160, 8154260331522980396622938112, 99789668150149835380490240, 316738490428618926844234694656,
    1126197683408833856436961280, 99789668150149835380490240, 316738578009955373031964540928, 99789668150149835380490240, 99789668150149835380490240, 4136994528167640318202609664,
    102640801525868402105647104, 1126197683408833856436961280, 4136994528167640318202609664, 8154359331739659481965920256
  ]
def negativeScales : Array ℕ := #[
    39, 35, 33, 47, 52, 36,
    32, 40, 41, 52, 40, 35,
    35, 36, 36, 41, 36, 47,
    32, 28, 36, 34, 26, 38,
    43, 31, 47, 26, 27, 32,
    27, 26, 36, 32, 43, 32,
    27, 32, 27, 32, 27, 38,
    25, 32, 30, 23, 25, 34,
    38, 33, 25, 43, 24, 46,
    27, 24, 47, 24, 24, 29,
    22, 27, 29, 43
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    39306395787005659, 35287661157219222, 33672001859312080, 47984544241565846, 52899865782819459, 36406672082097365,
    32782181217636819, 40525893643796984, 41380854097941628, 52899865783083165, 40525893643796984, 35445146229912031,
    35445146229912031, 36406672082097365, 36406672082097365, 41380854097941628, 36406672082097365, 47984544233608308,
    32782181217636819, 28806935122714766, 36261362781631420, 34261362954594630, 26806904786271533, 38836927613872800,
    43252081283783104, 31661958114186377, 47479646994037642, 26980134091370798, 27717099668457718, 32652559416178065,
    27717099668457718, 26980134091370798, 36654326342353292, 32689792322411132, 43252081692887633, 32652559416178065,
    27717099668457718, 32689792322411132, 27717099668457718, 32652559416178065, 27717099668457718, 38836927613872800,
    25310509295851609, 32764936955822540, 30764937128785751, 23310478959408832, 25334559623589908, 34666020139512675,
    38076825313475558, 33666024487789022, 25334559623589908, 43719612578870083, 24367092824217978, 46999206971105860,
    27863518652574562, 24367092824217978, 47999207370025452, 24367092824217978, 24367092824217978, 29740641611522788,
    22407734808715331, 27863518652574562, 29740641611522788, 43719630094407875
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
noncomputable def negativeCeiling : ℝ := 18893374679 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 24493672960620946507834589184, coefficient := (-24493672960620946507834589184) }, { argument := 386842527338329513800855715840, coefficient := (-386842527338329513800855715840) }, { argument := 15779103088800282799771746304, coefficient := (-15779103088800282799771746304) }, { argument := 313535645653773516467442024448, coefficient := (-313535645653773516467442024448) }, { argument := 9461198387842816163389657579520, coefficient := (-9461198387842816163389657579520) }, { argument := 210053573606489748514300493824, coefficient := (-210053573606489748514300493824) }, { argument := 272501933327338052126660100096, coefficient := (-272501933327338052126660100096) }, { argument := 3650390481864132656613384257536, coefficient := (-3650390481864132656613384257536) }, { argument := 6602494759576961554652202008576, coefficient := (-6602494759576961554652202008576) }, { argument := 9461198389572198420299928043520, coefficient := (-9461198389572198420299928043520) }, { argument := 3650390481864132656613384257536, coefficient := (-3650390481864132656613384257536) }, { argument := 215730697217475957933605912576, coefficient := (-215730697217475957933605912576) }, { argument := 215730697217475957933605912576, coefficient := (-215730697217475957933605912576) }, { argument := 210053573606489748514300493824, coefficient := (-210053573606489748514300493824) }, { argument := 210053573606489748514300493824, coefficient := (-210053573606489748514300493824) }, { argument := 6602494759576961554652202008576, coefficient := (-6602494759576961554652202008576) }, { argument := 210053573606489748514300493824, coefficient := (-210053573606489748514300493824) }, { argument := 313535643924391259557171560448, coefficient := (-313535643924391259557171560448) }, { argument := 272501933327338052126660100096, coefficient := (-272501933327338052126660100096) }, { argument := 1082882387893109477343232000, coefficient := (-1082882387893109477343232000) }, { argument := 189927397111218300126232576000, coefficient := (-189927397111218300126232576000) }, { argument := 189927419881418016111460352000, coefficient := (-189927419881418016111460352000) }, { argument := 1082859617693393492115456000, coefficient := (-1082859617693393492115456000) }, { argument := 17690084700261924894995906560, coefficient := (-17690084700261924894995906560) }, { argument := 1509675455055791128463257108480, coefficient := (-1509675455055791128463257108480) }, { argument := 250714139574954820850512035840, coefficient := (-250714139574954820850512035840) }, { argument := 14140920670746917382494164615168, coefficient := (-14140920670746917382494164615168) }, { argument := 156289333761010797413306204160, coefficient := (-156289333761010797413306204160) }, { argument := 8140069466719312365276364800, coefficient := (-8140069466719312365276364800) }, { argument := 249086125681610958377456762880, coefficient := (-249086125681610958377456762880) }, { argument := 260482222935017995688843673600, coefficient := (-260482222935017995688843673600) }, { argument := 156289333761010797413306204160, coefficient := (-156289333761010797413306204160) }, { argument := 3990262052585806921458474024960, coefficient := (-3990262052585806921458474024960) }, { argument := 255598181254986408269677854720, coefficient := (-255598181254986408269677854720) }, { argument := 1509675883153992533059248848896, coefficient := (-1509675883153992533059248848896) }, { argument := 249086125681610958377456762880, coefficient := (-249086125681610958377456762880) }, { argument := 8140069466719312365276364800, coefficient := (-8140069466719312365276364800) }, { argument := 255598181254986408269677854720, coefficient := (-255598181254986408269677854720) }, { argument := 8140069466719312365276364800, coefficient := (-8140069466719312365276364800) }, { argument := 249086125681610958377456762880, coefficient := (-249086125681610958377456762880) }, { argument := 260482222935017995688843673600, coefficient := (-260482222935017995688843673600) }, { argument := 17690084700261924894995906560, coefficient := (-17690084700261924894995906560) }, { argument := 95951603990528687865856000, coefficient := (-95951603990528687865856000) }, { argument := 16829009870614279758020608000, coefficient := (-16829009870614279758020608000) }, { argument := 16829011888226912820002816000, coefficient := (-16829011888226912820002816000) }, { argument := 95949586377895625883648000, coefficient := (-95949586377895625883648000) }, { argument := 780516513871230071377756160, coefficient := (-780516513871230071377756160) }, { argument := 251421040344433076924338667520, coefficient := (-251421040344433076924338667520) }, { argument := 2673968493739354397726952390656, coefficient := (-2673968493739354397726952390656) }, { argument := 251421798127456252875864276992, coefficient := (-251421798127456252875864276992) }, { argument := 780516513871230071377756160, coefficient := (-780516513871230071377756160) }, { argument := 8154260331522980396622938112, coefficient := (-8154260331522980396622938112) }, { argument := 99789668150149835380490240, coefficient := (-99789668150149835380490240) }, { argument := 316738490428618926844234694656, coefficient := (-316738490428618926844234694656) }, { argument := 1126197683408833856436961280, coefficient := (-1126197683408833856436961280) }, { argument := 99789668150149835380490240, coefficient := (-99789668150149835380490240) }, { argument := 316738578009955373031964540928, coefficient := (-316738578009955373031964540928) }, { argument := 99789668150149835380490240, coefficient := (-99789668150149835380490240) }, { argument := 99789668150149835380490240, coefficient := (-99789668150149835380490240) }, { argument := 4136994528167640318202609664, coefficient := (-4136994528167640318202609664) }, { argument := 102640801525868402105647104, coefficient := (-102640801525868402105647104) }, { argument := 1126197683408833856436961280, coefficient := (-1126197683408833856436961280) }, { argument := 4136994528167640318202609664, coefficient := (-4136994528167640318202609664) }, { argument := 8154359331739659481965920256, coefficient := (-8154359331739659481965920256) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4
