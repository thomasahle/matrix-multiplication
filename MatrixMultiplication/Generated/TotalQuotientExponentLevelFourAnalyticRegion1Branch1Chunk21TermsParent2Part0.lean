import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 21, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21

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
def constantNumerator : ℤ := (-1312896003933266088746749551181824)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    60357, 2122811, 19, 49, 41, 1147,
    16974297, 41, 37, 19, 19, 37,
    1147, 37, 482855, 49, 854337177, 26588106063,
    19218298637, 150828930513, 6081740075, 729808809, 19218298637, 38193327671,
    6081740075, 589442248069, 37706788465, 26588120183, 19218298637, 729808809,
    37706788465, 729808809, 19218298637, 19218298637, 854337177, 1005984284213,
    11429669589, 13499191766191, 119593372041, 5296676151, 26998373793317, 5296676151,
    10314579873, 194861927871, 10314579873, 119593372041, 194861927871, 125748441321,
    10314579873, 10314579873, 11429669589, 310545, 200066355, 2127789819,
    100033479, 310545, 40234425, 1574572615, 1574572615, 40234425,
    16352917685711, 318217725, 263666115, 1933245152000607
  ]
def negativeCoefficients : Array ℕ := #[
    2280222990452505409304395776, 80197532126935955405849755648, 1470053796651389076442710016, 1895595685155738545939283968, 25377770805350295635432046592, 44372413283135349228415483904,
    80158851223074770141904371712, 25377770805350295635432046592, 1431368170423720942852112384, 1470053796651389076442710016, 1470053796651389076442710016, 1431368170423720942852112384,
    44372413283135349228415483904, 1431368170423720942852112384, 2280218268086022539659182080, 1895595685155738545939283968, 7879869628387249122774614016, 245231993974403124111190523904,
    177257518244430051677826973696, 1391151340042316255417025429504, 112188302686348133973308211200, 6731298161180888038398492672, 177257518244430051677826973696, 176135635217566570338093891584,
    112188302686348133973308211200, 2718322574090215286173257957376, 173891869163839607658627727360, 245232124208416284500624932864, 177257518244430051677826973696, 6731298161180888038398492672,
    173891869163839607658627727360, 6731298161180888038398492672, 177257518244430051677826973696, 177257518244430051677826973696, 7879869628387249122774614016, 144977614320711742141272948736,
    52710047438836009131055251456, 3890877120513321943255276847104, 551527081738064583346895192064, 48853214699408984072685355008, 3890875716966137785270008807424, 48853214699408984072685355008,
    47567603786266642386562056192, 1797284056572993677200371744768, 47567603786266642386562056192, 551527081738064583346895192064, 1797284056572993677200371744768, 144978082169773128136362295296,
    47567603786266642386562056192, 47567603786266642386562056192, 52710047438836009131055251456, 45828353106961061652725760, 14762291393779685281989918720, 157003176934951077966319190016,
    14762335887326391069428416512, 45828353106961061652725760, 11875106254845782820441292800, 464731808870025623015721533440, 464731808870025623015721533440, 11875106254845782820441292800,
    147293987991576906841364365312, 11740161865586171652027187200, 607972668039283889122836480, 544160134135359474050575368192
  ]
def negativeScales : Array ℕ := #[
    15, 21, 4, 5, 5, 10,
    24, 5, 5, 4, 4, 5,
    10, 5, 18, 5, 29, 34,
    34, 37, 32, 29, 34, 35,
    32, 39, 35, 34, 34, 29,
    35, 29, 34, 34, 29, 39,
    33, 43, 36, 32, 44, 32,
    33, 37, 33, 36, 37, 36,
    33, 33, 33, 18, 27, 30,
    26, 18, 25, 30, 30, 25,
    43, 28, 27, 50
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15881233482214770, 21017544498975078, 4247927513443586, 5614709844123661, 5357552004618085, 10163649676015826,
    24016848489897121, 5357552004618085, 5209453365628950, 4247927513443586, 4247927513443586, 5209453365628950,
    10163649676015826, 5209453365628950, 18881230494374467, 5614709844123661, 29670230322635801, 34630061962981805,
    34161761571322015, 37134122222397426, 32501837012919924, 29442943323866103, 34161761571322015, 35152601572036539,
    32501837012919924, 39100559512596258, 35134105228419149, 34630062729145763, 34161761571322015, 29442943323866103,
    35134105228419149, 29442943323866103, 34161761571322015, 34161761571322015, 29670230322635801, 39871744908363275,
    33412064647334066, 43617938265279237, 36799346480852997, 32302440156159557, 44617937744859069, 32302440156159557,
    33263966008344922, 37503661288091714, 33263966008344922, 36799346480852997, 37503661288091714, 36871749563995578,
    33263966008344922, 33263966008344922, 33412064647334066, 18244442813970666, 27575903329864433, 30986708522980638,
    26575907678140777, 18244442813970666, 25261927079144744, 30552313146160727, 30552313146160727, 25261927079144744,
    43894613301674090, 28245438956356175, 27974136950119248, 50779946018942794
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
noncomputable def negativeCeiling : ℝ := 5108892491 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2280222990452505409304395776, coefficient := (-2280222990452505409304395776) }, { argument := 80197532126935955405849755648, coefficient := (-80197532126935955405849755648) }, { argument := 1470053796651389076442710016, coefficient := (-1470053796651389076442710016) }, { argument := 1895595685155738545939283968, coefficient := (-1895595685155738545939283968) }, { argument := 25377770805350295635432046592, coefficient := (-25377770805350295635432046592) }, { argument := 44372413283135349228415483904, coefficient := (-44372413283135349228415483904) }, { argument := 80158851223074770141904371712, coefficient := (-80158851223074770141904371712) }, { argument := 25377770805350295635432046592, coefficient := (-25377770805350295635432046592) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 1470053796651389076442710016, coefficient := (-1470053796651389076442710016) }, { argument := 1470053796651389076442710016, coefficient := (-1470053796651389076442710016) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 44372413283135349228415483904, coefficient := (-44372413283135349228415483904) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 2280218268086022539659182080, coefficient := (-2280218268086022539659182080) }, { argument := 1895595685155738545939283968, coefficient := (-1895595685155738545939283968) }, { argument := 7879869628387249122774614016, coefficient := (-7879869628387249122774614016) }, { argument := 245231993974403124111190523904, coefficient := (-245231993974403124111190523904) }, { argument := 177257518244430051677826973696, coefficient := (-177257518244430051677826973696) }, { argument := 1391151340042316255417025429504, coefficient := (-1391151340042316255417025429504) }, { argument := 112188302686348133973308211200, coefficient := (-112188302686348133973308211200) }, { argument := 6731298161180888038398492672, coefficient := (-6731298161180888038398492672) }, { argument := 177257518244430051677826973696, coefficient := (-177257518244430051677826973696) }, { argument := 176135635217566570338093891584, coefficient := (-176135635217566570338093891584) }, { argument := 112188302686348133973308211200, coefficient := (-112188302686348133973308211200) }, { argument := 2718322574090215286173257957376, coefficient := (-2718322574090215286173257957376) }, { argument := 173891869163839607658627727360, coefficient := (-173891869163839607658627727360) }, { argument := 245232124208416284500624932864, coefficient := (-245232124208416284500624932864) }, { argument := 177257518244430051677826973696, coefficient := (-177257518244430051677826973696) }, { argument := 6731298161180888038398492672, coefficient := (-6731298161180888038398492672) }, { argument := 173891869163839607658627727360, coefficient := (-173891869163839607658627727360) }, { argument := 6731298161180888038398492672, coefficient := (-6731298161180888038398492672) }, { argument := 177257518244430051677826973696, coefficient := (-177257518244430051677826973696) }, { argument := 177257518244430051677826973696, coefficient := (-177257518244430051677826973696) }, { argument := 7879869628387249122774614016, coefficient := (-7879869628387249122774614016) }, { argument := 144977614320711742141272948736, coefficient := (-144977614320711742141272948736) }, { argument := 52710047438836009131055251456, coefficient := (-52710047438836009131055251456) }, { argument := 3890877120513321943255276847104, coefficient := (-3890877120513321943255276847104) }, { argument := 551527081738064583346895192064, coefficient := (-551527081738064583346895192064) }, { argument := 48853214699408984072685355008, coefficient := (-48853214699408984072685355008) }, { argument := 3890875716966137785270008807424, coefficient := (-3890875716966137785270008807424) }, { argument := 48853214699408984072685355008, coefficient := (-48853214699408984072685355008) }, { argument := 47567603786266642386562056192, coefficient := (-47567603786266642386562056192) }, { argument := 1797284056572993677200371744768, coefficient := (-1797284056572993677200371744768) }, { argument := 47567603786266642386562056192, coefficient := (-47567603786266642386562056192) }, { argument := 551527081738064583346895192064, coefficient := (-551527081738064583346895192064) }, { argument := 1797284056572993677200371744768, coefficient := (-1797284056572993677200371744768) }, { argument := 144978082169773128136362295296, coefficient := (-144978082169773128136362295296) }, { argument := 47567603786266642386562056192, coefficient := (-47567603786266642386562056192) }, { argument := 47567603786266642386562056192, coefficient := (-47567603786266642386562056192) }, { argument := 52710047438836009131055251456, coefficient := (-52710047438836009131055251456) }, { argument := 45828353106961061652725760, coefficient := (-45828353106961061652725760) }, { argument := 14762291393779685281989918720, coefficient := (-14762291393779685281989918720) }, { argument := 157003176934951077966319190016, coefficient := (-157003176934951077966319190016) }, { argument := 14762335887326391069428416512, coefficient := (-14762335887326391069428416512) }, { argument := 45828353106961061652725760, coefficient := (-45828353106961061652725760) }, { argument := 11875106254845782820441292800, coefficient := (-11875106254845782820441292800) }, { argument := 464731808870025623015721533440, coefficient := (-464731808870025623015721533440) }, { argument := 464731808870025623015721533440, coefficient := (-464731808870025623015721533440) }, { argument := 11875106254845782820441292800, coefficient := (-11875106254845782820441292800) }, { argument := 147293987991576906841364365312, coefficient := (-147293987991576906841364365312) }, { argument := 11740161865586171652027187200, coefficient := (-11740161865586171652027187200) }, { argument := 607972668039283889122836480, coefficient := (-607972668039283889122836480) }, { argument := 544160134135359474050575368192, coefficient := (-544160134135359474050575368192) }] }

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
def constantNumerator : ℤ := (-4514140886878315221441748825800704)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1772927325, 523293302369217, 7100801235, 7100801235, 5082391665, 263666115,
    33337095, 1304645881, 1304645881, 33337095, 23228038197, 83550562641,
    11614022973, 851179161, 310545, 851179335, 310545, 854337351,
    26588108673, 19218303219, 150828930687, 6081741525, 729808983, 19218303219,
    38193336777, 6081741525, 589442388603, 37706797455, 26588122793, 19218303219,
    729808983, 37706797455, 729808983, 19218303219, 19218303219, 854337351,
    118980804038373, 41112181617, 1616119372447295, 430173802773, 19051986603, 3232237606586965,
    19051986603, 37101237069, 700912559763, 37101237069, 430173802773, 700912559763,
    14872647934281, 37101237069, 37101237069, 41112181617, 219423032335901, 12453437955,
    10318562877, 26252427500864205, 69383440035, 7021534732618131, 277889572653, 277889572653,
    198899194767, 10318562877, 224163225, 8772618855
  ]
def negativeCoefficients : Array ℕ := #[
    16352368312780739086752153600, 147293970097217623302290276352, 16373332887540714393273630720, 16373332887540714393273630720, 11719197290826196345505710080, 607972668039283889122836480,
    614960859625942324629995520, 24066468673626326906171293696, 24066468673626326906171293696, 614960859625942324629995520, 53560209494301106052523884544, 192654480781620676691578847232,
    53560227362278584449438318592, 7850742071920909151096537088, 45828353106961061652725760, 7850743676787643563827527680, 45828353106961061652725760, 7879871233253983535505604608,
    245232018047404140302155382784, 177257560505920724546409725952, 1391151341647182989829756420096, 112188329434127040852158054400, 6731299766047622451129483264, 177257560505920724546409725952,
    176135677211579454137888145408, 112188329434127040852158054400, 2718323222188898199847789658112, 173891910622896913320844984320, 245232148281417300691589791744, 177257560505920724546409725952,
    6731299766047622451129483264, 173891910622896913320844984320, 6731299766047622451129483264, 177257560505920724546409725952, 177257560505920724546409725952, 7879871233253983535505604608,
    535841904731458648459872043008, 189596473150166380236156960768, 14556709207079755204346396016640, 1983826511741984807836861857792, 175723560480642010950584500224, 14556704080597959421352099184640,
    175723560480642010950584500224, 171099256257467221188727013376, 6464777303998356087076766613504, 171099256257467221188727013376, 1983826511741984807836861857792, 6464777303998356087076766613504,
    535843613558723909457970987008, 171099256257467221188727013376, 171099256257467221188727013376, 189596473150166380236156960768, 3952773946657872152388995907584, 459450765587411695481451970560,
    23792986075062391373146619904, 14778802838807874399376464936960, 639949280639609147277736673280, 3952772650673501254666653007872, 640769728435300953876810694656, 640769728435300953876810694656,
    458630317791719888882377949184, 23792986075062391373146619904, 16540326569249483214186086400, 647305019497535689200469278720
  ]
def negativeScales : Array ℕ := #[
    30, 48, 32, 32, 32, 27,
    24, 30, 30, 24, 34, 36,
    33, 29, 18, 29, 18, 29,
    34, 34, 37, 32, 29, 34,
    35, 32, 39, 35, 34, 34,
    29, 35, 29, 34, 34, 29,
    46, 35, 50, 38, 34, 51,
    34, 35, 39, 35, 38, 39,
    43, 35, 35, 35, 47, 33,
    33, 54, 36, 52, 38, 38,
    37, 33, 27, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30723486253285392, 48894613126404840, 32725334677683094, 32725334677683094, 32242860412254399, 27974136950119248,
    24990625077700368, 30281011124341907, 30281011124341907, 24990625077700368, 34435148260447123, 36281930492499972,
    33435148741737963, 29664887589609512, 18244442813970666, 29664887884528517, 18244442813970666, 29670230616464653,
    34630062104602794, 34161761915287316, 37134122224061755, 32501837356885226, 29442943667831405, 34161761915287316,
    35152601916001840, 32501837356885226, 39100559856561560, 35134105572384451, 34630062870766677, 34161761915287316,
    29442943667831405, 35134105572384451, 29442943667831405, 34161761915287316, 34161761915287316, 29670230616464653,
    46757722161444571, 35258846879386931, 50521455188032652, 38646128712287694, 34149222388212433, 51521454679954139,
    34149222388212433, 35110748240397797, 39350443520144284, 35110748240397797, 38646128712287694, 39350443520144284,
    43757726762265602, 35110748240397797, 35110748240397797, 35258846879386931, 47640708298541754, 33535825023371593,
    33264523001553338, 54543300349798062, 36013872320175376, 52640707825529496, 38015720744567745, 38015720744567745,
    37533246479269750, 33264523001553338, 27739974376129735, 33030360442963945
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
noncomputable def negativeCeiling : ℝ := 46095216569 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 16352368312780739086752153600, coefficient := (-16352368312780739086752153600) }, { argument := 147293970097217623302290276352, coefficient := (-147293970097217623302290276352) }, { argument := 16373332887540714393273630720, coefficient := (-16373332887540714393273630720) }, { argument := 16373332887540714393273630720, coefficient := (-16373332887540714393273630720) }, { argument := 11719197290826196345505710080, coefficient := (-11719197290826196345505710080) }, { argument := 607972668039283889122836480, coefficient := (-607972668039283889122836480) }, { argument := 614960859625942324629995520, coefficient := (-614960859625942324629995520) }, { argument := 24066468673626326906171293696, coefficient := (-24066468673626326906171293696) }, { argument := 24066468673626326906171293696, coefficient := (-24066468673626326906171293696) }, { argument := 614960859625942324629995520, coefficient := (-614960859625942324629995520) }, { argument := 53560209494301106052523884544, coefficient := (-53560209494301106052523884544) }, { argument := 192654480781620676691578847232, coefficient := (-192654480781620676691578847232) }, { argument := 53560227362278584449438318592, coefficient := (-53560227362278584449438318592) }, { argument := 7850742071920909151096537088, coefficient := (-7850742071920909151096537088) }, { argument := 45828353106961061652725760, coefficient := (-45828353106961061652725760) }, { argument := 7850743676787643563827527680, coefficient := (-7850743676787643563827527680) }, { argument := 45828353106961061652725760, coefficient := (-45828353106961061652725760) }, { argument := 7879871233253983535505604608, coefficient := (-7879871233253983535505604608) }, { argument := 245232018047404140302155382784, coefficient := (-245232018047404140302155382784) }, { argument := 177257560505920724546409725952, coefficient := (-177257560505920724546409725952) }, { argument := 1391151341647182989829756420096, coefficient := (-1391151341647182989829756420096) }, { argument := 112188329434127040852158054400, coefficient := (-112188329434127040852158054400) }, { argument := 6731299766047622451129483264, coefficient := (-6731299766047622451129483264) }, { argument := 177257560505920724546409725952, coefficient := (-177257560505920724546409725952) }, { argument := 176135677211579454137888145408, coefficient := (-176135677211579454137888145408) }, { argument := 112188329434127040852158054400, coefficient := (-112188329434127040852158054400) }, { argument := 2718323222188898199847789658112, coefficient := (-2718323222188898199847789658112) }, { argument := 173891910622896913320844984320, coefficient := (-173891910622896913320844984320) }, { argument := 245232148281417300691589791744, coefficient := (-245232148281417300691589791744) }, { argument := 177257560505920724546409725952, coefficient := (-177257560505920724546409725952) }, { argument := 6731299766047622451129483264, coefficient := (-6731299766047622451129483264) }, { argument := 173891910622896913320844984320, coefficient := (-173891910622896913320844984320) }, { argument := 6731299766047622451129483264, coefficient := (-6731299766047622451129483264) }, { argument := 177257560505920724546409725952, coefficient := (-177257560505920724546409725952) }, { argument := 177257560505920724546409725952, coefficient := (-177257560505920724546409725952) }, { argument := 7879871233253983535505604608, coefficient := (-7879871233253983535505604608) }, { argument := 535841904731458648459872043008, coefficient := (-535841904731458648459872043008) }, { argument := 189596473150166380236156960768, coefficient := (-189596473150166380236156960768) }, { argument := 14556709207079755204346396016640, coefficient := (-14556709207079755204346396016640) }, { argument := 1983826511741984807836861857792, coefficient := (-1983826511741984807836861857792) }, { argument := 175723560480642010950584500224, coefficient := (-175723560480642010950584500224) }, { argument := 14556704080597959421352099184640, coefficient := (-14556704080597959421352099184640) }, { argument := 175723560480642010950584500224, coefficient := (-175723560480642010950584500224) }, { argument := 171099256257467221188727013376, coefficient := (-171099256257467221188727013376) }, { argument := 6464777303998356087076766613504, coefficient := (-6464777303998356087076766613504) }, { argument := 171099256257467221188727013376, coefficient := (-171099256257467221188727013376) }, { argument := 1983826511741984807836861857792, coefficient := (-1983826511741984807836861857792) }, { argument := 6464777303998356087076766613504, coefficient := (-6464777303998356087076766613504) }, { argument := 535843613558723909457970987008, coefficient := (-535843613558723909457970987008) }, { argument := 171099256257467221188727013376, coefficient := (-171099256257467221188727013376) }, { argument := 171099256257467221188727013376, coefficient := (-171099256257467221188727013376) }, { argument := 189596473150166380236156960768, coefficient := (-189596473150166380236156960768) }, { argument := 3952773946657872152388995907584, coefficient := (-3952773946657872152388995907584) }, { argument := 459450765587411695481451970560, coefficient := (-459450765587411695481451970560) }, { argument := 23792986075062391373146619904, coefficient := (-23792986075062391373146619904) }, { argument := 14778802838807874399376464936960, coefficient := (-14778802838807874399376464936960) }, { argument := 639949280639609147277736673280, coefficient := (-639949280639609147277736673280) }, { argument := 3952772650673501254666653007872, coefficient := (-3952772650673501254666653007872) }, { argument := 640769728435300953876810694656, coefficient := (-640769728435300953876810694656) }, { argument := 640769728435300953876810694656, coefficient := (-640769728435300953876810694656) }, { argument := 458630317791719888882377949184, coefficient := (-458630317791719888882377949184) }, { argument := 23792986075062391373146619904, coefficient := (-23792986075062391373146619904) }, { argument := 16540326569249483214186086400, coefficient := (-16540326569249483214186086400) }, { argument := 647305019497535689200469278720, coefficient := (-647305019497535689200469278720) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21
