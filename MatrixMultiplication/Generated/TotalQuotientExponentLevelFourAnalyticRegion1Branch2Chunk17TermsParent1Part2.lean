import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 17, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-10239789726278076545775681360887808)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    116957113875, 5425234143, 103487331, 9757554937, 353617020679, 2828937205055,
    78059399873, 1464926925, 2514418995, 1464926925, 25160785473, 911835193791,
    7294684231095, 201283603017, 548370978925, 941230843795, 548370978925, 253734480975,
    253734359985, 21973903875, 37716284925, 21973903875, 17829990555, 17829982053,
    1113, 42569882486171, 4917498243, 1506539667359589, 77385893403, 2329341273,
    3012970143125019, 2329341273, 2329341273, 199546902387, 2329341273, 77385893403,
    199546902387, 85248956566501, 2329341273, 2329341273, 4917498243, 4975607845122221,
    5075219037, 285124665, 17982577569897805, 15415740221, 2487803754773763, 15415740221,
    15415740221, 5075219037, 285124665, 546560645863, 546560638233, 44436116725,
    76270709515, 44436116725, 253734480975, 253734359985, 10362869, 2285896225,
    2285895135, 483, 5813895, 609576405
  ]
def negativeCoefficients : Array ℕ := #[
    269684743406478677753462784000, 25019476443967992023086006272, 238625538728533595743322112, 89997559354000063637378564096, 3261541340286585607017444933632, 3261542538890298990901518663680,
    89996360750286679753304834048, 432370113154580908671290572800, 1484250998234847254278507069440, 432370113154580908671290572800, 464134570313940127521196474368, 16820390457263929786023077216256,
    16820396638691776066789771837440, 464128388886093846754501853184, 10115659105679049175788735692800, 34725288979536113886557571645440, 10115659105679049175788735692800, 1170143758305337555546433126400,
    1170143200337446186016770621440, 810693962164839203758669824000, 2782970621690338601772200755200, 810693962164839203758669824000, 2631242180837948233012519895040, 2631240926164203315583657181184,
    43057101991394632686335164416, 191717706901925519439813410816, 11338978946442172820499726336, 6784851484539516015871361286144, 89219860657531833508668899328, 10742190580839953198368161792,
    6784605606928132784457580019712, 10742190580839953198368161792, 10742190580839953198368161792, 460123829879311328663436263424, 10742190580839953198368161792, 89219860657531833508668899328,
    460123829879311328663436263424, 191963584513308750853594677248, 10742190580839953198368161792, 10742190580839953198368161792, 11338978946442172820499726336, 5602036409308537767299492347904,
    23405316673389411892564328448, 1314905431089292802953052160, 20246582410738198521363898040320, 35546276820447215439830843392, 5602036031485019928057530548224, 35546276820447215439830843392,
    35546276820447215439830843392, 23405316673389411892564328448, 1314905431089292802953052160, 2520566088749040052378273841152, 2520566053561875731777304133632, 819701672855559639355988377600,
    2813892517486897919569669652480, 819701672855559639355988377600, 1170143758305337555546433126400, 1170143200337446186016770621440, 97874530463937754852017307648, 84334685283267571570914099200,
    84334645069365490884091576320, 37370314935927417048517312512, 13405929142052449199063040, 1405587492050865436030402560
  ]
def negativeScales : Array ℕ := #[
    36, 32, 26, 33, 38, 41,
    36, 30, 31, 30, 34, 39,
    42, 37, 38, 39, 38, 37,
    37, 34, 35, 34, 34, 34,
    10, 45, 32, 50, 36, 31,
    51, 31, 31, 37, 31, 36,
    37, 46, 31, 31, 32, 52,
    32, 28, 53, 33, 51, 33,
    33, 32, 28, 38, 38, 35,
    36, 35, 37, 37, 23, 31,
    31, 8, 22, 29
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36767188659860633, 32337038256917667, 26624878921789179, 33183872534337073, 38363396761528247, 41363397291712947,
    36183853320136589, 30448181554422547, 31227577930014115, 30448181554422547, 34550457910055350, 39729982137389450,
    42729982667574152, 37550438695854866, 38996361288441160, 39775757642084420, 38996361288441160, 37884528633280532,
    37884527945349887, 34355072150031023, 35134468525622634, 34355072150031023, 34053586887604436, 34053586199673832,
    10120237877341960, 45274898341112406, 32195277391021711, 50420160083066291, 36171351551776231, 31117274879020438,
    51420107800000247, 31117274879020438, 31117274879020438, 37537936927494079, 31117274879020438, 36171351551776231,
    37537936927494079, 46276747409425634, 31117274879020438, 31117274879020438, 32195277391021711, 52143794206569915,
    32240822941658363, 28087017605579328, 53997449368277026, 33843685115722757, 51143794109268846, 33843685115722757,
    33843685115722757, 32240822941658363, 28087017605579328, 38991590649337703, 38991590629197638, 35371013693900046,
    36150410069491655, 35371013693900046, 37884528633280532, 37884527945349887, 23304920138187517, 31090112763629550,
    31090112075698947, 8915879384625971, 22471073585699149, 29183231820315493
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
noncomputable def negativeCeiling : ℝ := 43599928943 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 269684743406478677753462784000, coefficient := (-269684743406478677753462784000) }, { argument := 25019476443967992023086006272, coefficient := (-25019476443967992023086006272) }, { argument := 238625538728533595743322112, coefficient := (-238625538728533595743322112) }, { argument := 89997559354000063637378564096, coefficient := (-89997559354000063637378564096) }, { argument := 3261541340286585607017444933632, coefficient := (-3261541340286585607017444933632) }, { argument := 3261542538890298990901518663680, coefficient := (-3261542538890298990901518663680) }, { argument := 89996360750286679753304834048, coefficient := (-89996360750286679753304834048) }, { argument := 432370113154580908671290572800, coefficient := (-432370113154580908671290572800) }, { argument := 1484250998234847254278507069440, coefficient := (-1484250998234847254278507069440) }, { argument := 432370113154580908671290572800, coefficient := (-432370113154580908671290572800) }, { argument := 464134570313940127521196474368, coefficient := (-464134570313940127521196474368) }, { argument := 16820390457263929786023077216256, coefficient := (-16820390457263929786023077216256) }, { argument := 16820396638691776066789771837440, coefficient := (-16820396638691776066789771837440) }, { argument := 464128388886093846754501853184, coefficient := (-464128388886093846754501853184) }, { argument := 10115659105679049175788735692800, coefficient := (-10115659105679049175788735692800) }, { argument := 34725288979536113886557571645440, coefficient := (-34725288979536113886557571645440) }, { argument := 10115659105679049175788735692800, coefficient := (-10115659105679049175788735692800) }, { argument := 1170143758305337555546433126400, coefficient := (-1170143758305337555546433126400) }, { argument := 1170143200337446186016770621440, coefficient := (-1170143200337446186016770621440) }, { argument := 810693962164839203758669824000, coefficient := (-810693962164839203758669824000) }, { argument := 2782970621690338601772200755200, coefficient := (-2782970621690338601772200755200) }, { argument := 810693962164839203758669824000, coefficient := (-810693962164839203758669824000) }, { argument := 2631242180837948233012519895040, coefficient := (-2631242180837948233012519895040) }, { argument := 2631240926164203315583657181184, coefficient := (-2631240926164203315583657181184) }, { argument := 43057101991394632686335164416, coefficient := (-43057101991394632686335164416) }, { argument := 191717706901925519439813410816, coefficient := (-191717706901925519439813410816) }, { argument := 11338978946442172820499726336, coefficient := (-11338978946442172820499726336) }, { argument := 6784851484539516015871361286144, coefficient := (-6784851484539516015871361286144) }, { argument := 89219860657531833508668899328, coefficient := (-89219860657531833508668899328) }, { argument := 10742190580839953198368161792, coefficient := (-10742190580839953198368161792) }, { argument := 6784605606928132784457580019712, coefficient := (-6784605606928132784457580019712) }, { argument := 10742190580839953198368161792, coefficient := (-10742190580839953198368161792) }, { argument := 10742190580839953198368161792, coefficient := (-10742190580839953198368161792) }, { argument := 460123829879311328663436263424, coefficient := (-460123829879311328663436263424) }, { argument := 10742190580839953198368161792, coefficient := (-10742190580839953198368161792) }, { argument := 89219860657531833508668899328, coefficient := (-89219860657531833508668899328) }, { argument := 460123829879311328663436263424, coefficient := (-460123829879311328663436263424) }, { argument := 191963584513308750853594677248, coefficient := (-191963584513308750853594677248) }, { argument := 10742190580839953198368161792, coefficient := (-10742190580839953198368161792) }, { argument := 10742190580839953198368161792, coefficient := (-10742190580839953198368161792) }, { argument := 11338978946442172820499726336, coefficient := (-11338978946442172820499726336) }, { argument := 5602036409308537767299492347904, coefficient := (-5602036409308537767299492347904) }, { argument := 23405316673389411892564328448, coefficient := (-23405316673389411892564328448) }, { argument := 1314905431089292802953052160, coefficient := (-1314905431089292802953052160) }, { argument := 20246582410738198521363898040320, coefficient := (-20246582410738198521363898040320) }, { argument := 35546276820447215439830843392, coefficient := (-35546276820447215439830843392) }, { argument := 5602036031485019928057530548224, coefficient := (-5602036031485019928057530548224) }, { argument := 35546276820447215439830843392, coefficient := (-35546276820447215439830843392) }, { argument := 35546276820447215439830843392, coefficient := (-35546276820447215439830843392) }, { argument := 23405316673389411892564328448, coefficient := (-23405316673389411892564328448) }, { argument := 1314905431089292802953052160, coefficient := (-1314905431089292802953052160) }, { argument := 2520566088749040052378273841152, coefficient := (-2520566088749040052378273841152) }, { argument := 2520566053561875731777304133632, coefficient := (-2520566053561875731777304133632) }, { argument := 819701672855559639355988377600, coefficient := (-819701672855559639355988377600) }, { argument := 2813892517486897919569669652480, coefficient := (-2813892517486897919569669652480) }, { argument := 819701672855559639355988377600, coefficient := (-819701672855559639355988377600) }, { argument := 1170143758305337555546433126400, coefficient := (-1170143758305337555546433126400) }, { argument := 1170143200337446186016770621440, coefficient := (-1170143200337446186016770621440) }, { argument := 97874530463937754852017307648, coefficient := (-97874530463937754852017307648) }, { argument := 84334685283267571570914099200, coefficient := (-84334685283267571570914099200) }, { argument := 84334645069365490884091576320, coefficient := (-84334645069365490884091576320) }, { argument := 37370314935927417048517312512, coefficient := (-37370314935927417048517312512) }, { argument := 13405929142052449199063040, coefficient := (-13405929142052449199063040) }, { argument := 1405587492050865436030402560, coefficient := (-1405587492050865436030402560) }] }

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

end TermShard4


end Parent1

namespace Parent1

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 206124600532366551552647912174387200
def positiveArguments : Array ℕ := #[
    27295, 93, 1113, 1665
  ]
def positiveCoefficients : Array ℕ := #[
    2162532695826845094615782124421120, 3597763239173136423925579776, 86114203982789265372670328832, 64411567669067442428345057280
  ]
def positiveScales : Array ℕ := #[
    14, 6, 10, 10
  ]
def negativeArguments : Array ℕ := #[
    6570624375, 304788435, 5813895, 293705667, 10643990589, 85151956005,
    2349614043, 3418162825, 5866977655, 3418162825, 293705667, 10643990589,
    85151956005, 2349614043, 21973903875, 37716284925, 21973903875, 17829990555,
    17829982053, 3418162825, 5866977655, 3418162825, 17829990555, 17829982053,
    93, 620045297, 22470646799, 179765240455, 4960296313, 44436116725,
    76270709515, 44436116725, 17829990555, 17829982053, 44436116725, 76270709515,
    44436116725, 17829990555, 17829982053, 1929, 17829990555, 17829982053,
    969, 53575791038251, 96810729, 5438805, 379376642130425, 294058057,
    107151577532337, 294058057, 294058057, 96810729, 5438805, 26884605737,
    26884595927, 1816587, 21487424515, 21487414269, 1113, 93
  ]
def negativeCoefficients : Array ℕ := #[
    15150828281262847064801280000, 1405588564267864720398090240, 13405929142052449199063040, 10835826544294322043296415744, 392693940636511979440227483648, 392694084950002554088477163520,
    10835682230803747395046735872, 31526987417521524590614937600, 108226635287957612291141140480, 31526987417521524590614937600, 10835826544294322043296415744, 392693940636511979440227483648,
    392694084950002554088477163520, 10835682230803747395046735872, 810693962164839203758669824000, 2782970621690338601772200755200, 810693962164839203758669824000, 82226318151185882281641246720,
    82226278942631353611989286912, 31526987417521524590614937600, 108226635287957612291141140480, 31526987417521524590614937600, 82226318151185882281641246720, 82226278942631353611989286912,
    1798881619586568211962789888, 11437816907866228823479549952, 414510270671873756075795677184, 414510423002780473760059228160, 11437664576959511139215998976, 819701672855559639355988377600,
    2813892517486897919569669652480, 819701672855559639355988377600, 82226318151185882281641246720, 82226278942631353611989286912, 819701672855559639355988377600, 2813892517486897919569669652480,
    819701672855559639355988377600, 2631242180837948233012519895040, 2631240926164203315583657181184, 37312286496585914848131416064, 82226318151185882281641246720, 82226278942631353611989286912,
    37486371814610421449289105408, 60320978138986690652221210624, 223230342681531428276011008, 12541030487726484734607360, 213570063016456505469278617600, 339025857518205970658885632,
    60320975580849215563464966144, 339025857518205970658885632, 339025857518205970658885632, 223230342681531428276011008, 12541030487726484734607360, 123983360388255640561802805248,
    123983315147615799789127467008, 8578589562016720189812375552, 99093255207839396595824066560, 99093207956504451788807602176, 43057101991394632686335164416, 1798881619586568211962789888
  ]
def negativeScales : Array ℕ := #[
    32, 28, 22, 28, 33, 36,
    31, 31, 32, 31, 28, 33,
    36, 31, 34, 35, 34, 34,
    34, 31, 32, 31, 34, 34,
    6, 29, 34, 37, 32, 35,
    36, 35, 34, 34, 35, 36,
    35, 34, 34, 10, 34, 34,
    9, 45, 26, 22, 48, 28,
    46, 28, 28, 26, 22, 34,
    34, 20, 34, 34, 10, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    14736349076623456, 6539158811107971, 10120237877341959, 10701306461953989
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    32613383323463827, 28183232920838631, 22471073585699149, 28129795861581280, 33309320088772453, 36309320618957153,
    31129776647380797, 31670573975794607, 32449970351350610, 31670573975794607, 28129795861581280, 33309320088772453,
    36309320618957153, 31129776647380797, 34355072150031023, 35134468525622634, 34355072150031023, 34053586887604436,
    34053586199673832, 31670573975794607, 32449970351350610, 31670573975794607, 34053586887604436, 34053586199673832,
    6539158811108986, 29207798373582553, 34387322600773730, 37387323130958430, 32207779159382070, 35371013693900046,
    36150410069491655, 35371013693900046, 34053586887604436, 34053586199673832, 35371013693900046, 36150410069491655,
    35371013693900046, 34053586887604436, 34053586199673832, 10913637433615165, 34053586887604436, 34053586199673832,
    9920352861677847, 45606646479770255, 26528663606519469, 22374858270439748, 48430624184505203, 28131525779048500,
    46606646418587356, 28131525779048500, 28131525779048500, 26528663606519469, 22374858270439748, 34646061263524847,
    34646060737095668, 20792799030852688, 34322773520419825, 34322772832489222, 10120237877341960, 6539158811108986
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
noncomputable def positiveFloor : ℝ := 5993971897 / 15625000000
noncomputable def negativeCeiling : ℝ := 9692653649 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 15150828281262847064801280000, coefficient := (-15150828281262847064801280000) }, { argument := 1405588564267864720398090240, coefficient := (-1405588564267864720398090240) }, { argument := 13405929142052449199063040, coefficient := (-13405929142052449199063040) }, { argument := 10835826544294322043296415744, coefficient := (-10835826544294322043296415744) }, { argument := 392693940636511979440227483648, coefficient := (-392693940636511979440227483648) }, { argument := 392694084950002554088477163520, coefficient := (-392694084950002554088477163520) }, { argument := 10835682230803747395046735872, coefficient := (-10835682230803747395046735872) }, { argument := 31526987417521524590614937600, coefficient := (-31526987417521524590614937600) }, { argument := 108226635287957612291141140480, coefficient := (-108226635287957612291141140480) }, { argument := 31526987417521524590614937600, coefficient := (-31526987417521524590614937600) }, { argument := 10835826544294322043296415744, coefficient := (-10835826544294322043296415744) }, { argument := 392693940636511979440227483648, coefficient := (-392693940636511979440227483648) }, { argument := 392694084950002554088477163520, coefficient := (-392694084950002554088477163520) }, { argument := 10835682230803747395046735872, coefficient := (-10835682230803747395046735872) }, { argument := 810693962164839203758669824000, coefficient := (-810693962164839203758669824000) }, { argument := 2782970621690338601772200755200, coefficient := (-2782970621690338601772200755200) }, { argument := 810693962164839203758669824000, coefficient := (-810693962164839203758669824000) }, { argument := 82226318151185882281641246720, coefficient := (-82226318151185882281641246720) }, { argument := 82226278942631353611989286912, coefficient := (-82226278942631353611989286912) }, { argument := 31526987417521524590614937600, coefficient := (-31526987417521524590614937600) }, { argument := 108226635287957612291141140480, coefficient := (-108226635287957612291141140480) }, { argument := 31526987417521524590614937600, coefficient := (-31526987417521524590614937600) }, { argument := 82226318151185882281641246720, coefficient := (-82226318151185882281641246720) }, { argument := 82226278942631353611989286912, coefficient := (-82226278942631353611989286912) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 11437816907866228823479549952, coefficient := (-11437816907866228823479549952) }, { argument := 414510270671873756075795677184, coefficient := (-414510270671873756075795677184) }, { argument := 414510423002780473760059228160, coefficient := (-414510423002780473760059228160) }, { argument := 11437664576959511139215998976, coefficient := (-11437664576959511139215998976) }, { argument := 819701672855559639355988377600, coefficient := (-819701672855559639355988377600) }, { argument := 2813892517486897919569669652480, coefficient := (-2813892517486897919569669652480) }, { argument := 819701672855559639355988377600, coefficient := (-819701672855559639355988377600) }, { argument := 82226318151185882281641246720, coefficient := (-82226318151185882281641246720) }, { argument := 82226278942631353611989286912, coefficient := (-82226278942631353611989286912) }, { argument := 819701672855559639355988377600, coefficient := (-819701672855559639355988377600) }, { argument := 2813892517486897919569669652480, coefficient := (-2813892517486897919569669652480) }, { argument := 819701672855559639355988377600, coefficient := (-819701672855559639355988377600) }, { argument := 2631242180837948233012519895040, coefficient := (-2631242180837948233012519895040) }, { argument := 2631240926164203315583657181184, coefficient := (-2631240926164203315583657181184) }, { argument := 37312286496585914848131416064, coefficient := (-37312286496585914848131416064) }, { argument := 82226318151185882281641246720, coefficient := (-82226318151185882281641246720) }, { argument := 82226278942631353611989286912, coefficient := (-82226278942631353611989286912) }, { argument := 37486371814610421449289105408, coefficient := (-37486371814610421449289105408) }, { argument := 60320978138986690652221210624, coefficient := (-60320978138986690652221210624) }, { argument := 223230342681531428276011008, coefficient := (-223230342681531428276011008) }, { argument := 12541030487726484734607360, coefficient := (-12541030487726484734607360) }, { argument := 213570063016456505469278617600, coefficient := (-213570063016456505469278617600) }, { argument := 339025857518205970658885632, coefficient := (-339025857518205970658885632) }, { argument := 60320975580849215563464966144, coefficient := (-60320975580849215563464966144) }, { argument := 339025857518205970658885632, coefficient := (-339025857518205970658885632) }, { argument := 339025857518205970658885632, coefficient := (-339025857518205970658885632) }, { argument := 223230342681531428276011008, coefficient := (-223230342681531428276011008) }, { argument := 12541030487726484734607360, coefficient := (-12541030487726484734607360) }, { argument := 123983360388255640561802805248, coefficient := (-123983360388255640561802805248) }, { argument := 123983315147615799789127467008, coefficient := (-123983315147615799789127467008) }, { argument := 8578589562016720189812375552, coefficient := (-8578589562016720189812375552) }, { argument := 99093255207839396595824066560, coefficient := (-99093255207839396595824066560) }, { argument := 99093207956504451788807602176, coefficient := (-99093207956504451788807602176) }, { argument := 43057101991394632686335164416, coefficient := (-43057101991394632686335164416) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 2162532695826845094615782124421120, coefficient := 2162532695826845094615782124421120 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 86114203982789265372670328832, coefficient := 86114203982789265372670328832 }, { argument := 64411567669067442428345057280, coefficient := 64411567669067442428345057280 }] }

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

end TermShard5


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17
