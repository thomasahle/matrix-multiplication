import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-27709585102706306551176264383725568)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    161395210994337, 14377273413534609, 601025571477, 139626787810663435, 616738658313, 19641358545,
    601025571477, 341759638683, 616738658313, 9628193958759, 11784815127, 7188640083843985,
    601025571477, 19641358545, 11784815127, 19641358545, 302476921593, 341759638683,
    161395207016097, 42255, 32865, 4695, 44133, 521145,
    36621, 32865, 521145, 4695, 36621, 36621,
    36621, 36621, 36621, 42255, 44133, 267553965,
    42714239505, 1704895506195, 42714239505, 1070093745, 810524813525239, 1693318867,
    7165449292846951, 41900634943, 1333038257, 114646456812765647, 684533159, 684533159,
    23166043223, 1260982135, 41900634943, 23166043223, 3242839418110949, 1333038257,
    1260982135, 1693318867, 8512035, 1358922495, 54240011805, 1358922495,
    34044255, 1988111223, 74698445961, 149385592719
  ]
def negativeCoefficients : Array ℕ := #[
    363429706046739346202428440576, 32374741593899102067305880748032, 2771741224697811567829957214208, 314411574777521579432619152506880, 2844205047565728210126165245952, 90579778584895802870260039680,
    2771741224697811567829957214208, 1576088147377186969942524690432, 2844205047565728210126165245952, 44402207462315922567001471451136, 1739131748829999415108992761856, 32374756802900381968697456066560,
    2771741224697811567829957214208, 90579778584895802870260039680, 1739131748829999415108992761856, 90579778584895802870260039680, 2789857180414790728404009222144, 1576088147377186969942524690432,
    363429697088539255407227437056, 399087191467313717009448960, 310401148919021779896238080, 354744170193167748452843520, 416824399976972104432091136, 4922075361430202509783203840,
    11068018110026833751728717824, 310401148919021779896238080, 4922075361430202509783203840, 354744170193167748452843520, 345875565938338554741522432, 345875565938338554741522432,
    345875565938338554741522432, 11068018110026833751728717824, 345875565938338554741522432, 399087191467313717009448960, 416824399976972104432091136, 2467749759130621396616478720,
    393969322225934580765991895040, 3931221384399582799220850032640, 393969322225934580765991895040, 2467468181111551266379530240, 912569812041701779199424987136, 15618109887366411214741569536,
    32270314765207712592889900957696, 386465144659726303037115858944, 12295107783671430105222086656, 32270108761332439395682255634432, 12627407994040928216174034944, 12627407994040928216174034944,
    213669035267587285342102749184, 11630507362932433883318190080, 386465144659726303037115858944, 213669035267587285342102749184, 912778149689176624629278572544, 12295107783671430105222086656,
    11630507362932433883318190080, 15618109887366411214741569536, 78509665595729141594849280, 12533847740635923893673000960, 125068952040227483724137103360, 12533847740635923893673000960,
    78500707395638346393845760, 73348357841501397620134772736, 2755886230692779884394632445952, 2755677797186801993207884283904
  ]
def negativeScales : Array ℕ := #[
    47, 53, 39, 56, 39, 34,
    39, 38, 39, 43, 33, 52,
    39, 34, 33, 34, 38, 38,
    47, 15, 15, 12, 15, 18,
    15, 15, 18, 12, 15, 15,
    15, 15, 15, 15, 15, 27,
    35, 40, 35, 29, 49, 30,
    52, 35, 30, 56, 29, 29,
    34, 30, 35, 34, 51, 30,
    30, 30, 23, 30, 35, 30,
    25, 30, 36, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    47197591099249271, 53674639619205877, 39128635417489855, 56954353377698875, 39165868323688831, 34193175669684566,
    39128635417489855, 38314191070645932, 39165868323688831, 43130402343664043, 33456210075518418, 52674640296954779,
    39128635417489855, 34193175669684566, 33456210075518418, 34193175669684566, 38138034115492105, 38314191070645932,
    47197591063688196, 15366834443983451, 15004264364598741, 12196909442541137, 15429570199331434, 18991325329495353,
    15160383566516023, 15004264364598741, 18991325329495353, 12196909442541137, 15160383566516023, 15160383566516023,
    15160383566516023, 15160383566516023, 15160383566516023, 15366834443983451, 15429570199331434, 27995254690076254,
    35313998045385613, 40632820457199430, 35313998045385613, 29995090064578523, 49525849681719678, 30657206525132694,
    52669978591509207, 35286253054902709, 30312071039058440, 56669969381753421, 29350545186873076, 29350545186873076,
    34431292600757460, 30231900690374457, 35286253054902709, 34431292600757460, 51526179008180666, 30312071039058440,
    30231900690374457, 30657206525132694, 23021072652285295, 30339816029541345, 35658638441367988, 30339816029541345,
    25020908026845408, 30888751326917220, 36120359178130707, 37120250059926127
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
noncomputable def negativeCeiling : ℝ := 340214575529 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 363429706046739346202428440576, coefficient := (-363429706046739346202428440576) }, { argument := 32374741593899102067305880748032, coefficient := (-32374741593899102067305880748032) }, { argument := 2771741224697811567829957214208, coefficient := (-2771741224697811567829957214208) }, { argument := 314411574777521579432619152506880, coefficient := (-314411574777521579432619152506880) }, { argument := 2844205047565728210126165245952, coefficient := (-2844205047565728210126165245952) }, { argument := 90579778584895802870260039680, coefficient := (-90579778584895802870260039680) }, { argument := 2771741224697811567829957214208, coefficient := (-2771741224697811567829957214208) }, { argument := 1576088147377186969942524690432, coefficient := (-1576088147377186969942524690432) }, { argument := 2844205047565728210126165245952, coefficient := (-2844205047565728210126165245952) }, { argument := 44402207462315922567001471451136, coefficient := (-44402207462315922567001471451136) }, { argument := 1739131748829999415108992761856, coefficient := (-1739131748829999415108992761856) }, { argument := 32374756802900381968697456066560, coefficient := (-32374756802900381968697456066560) }, { argument := 2771741224697811567829957214208, coefficient := (-2771741224697811567829957214208) }, { argument := 90579778584895802870260039680, coefficient := (-90579778584895802870260039680) }, { argument := 1739131748829999415108992761856, coefficient := (-1739131748829999415108992761856) }, { argument := 90579778584895802870260039680, coefficient := (-90579778584895802870260039680) }, { argument := 2789857180414790728404009222144, coefficient := (-2789857180414790728404009222144) }, { argument := 1576088147377186969942524690432, coefficient := (-1576088147377186969942524690432) }, { argument := 363429697088539255407227437056, coefficient := (-363429697088539255407227437056) }, { argument := 399087191467313717009448960, coefficient := (-399087191467313717009448960) }, { argument := 310401148919021779896238080, coefficient := (-310401148919021779896238080) }, { argument := 354744170193167748452843520, coefficient := (-354744170193167748452843520) }, { argument := 416824399976972104432091136, coefficient := (-416824399976972104432091136) }, { argument := 4922075361430202509783203840, coefficient := (-4922075361430202509783203840) }, { argument := 11068018110026833751728717824, coefficient := (-11068018110026833751728717824) }, { argument := 310401148919021779896238080, coefficient := (-310401148919021779896238080) }, { argument := 4922075361430202509783203840, coefficient := (-4922075361430202509783203840) }, { argument := 354744170193167748452843520, coefficient := (-354744170193167748452843520) }, { argument := 345875565938338554741522432, coefficient := (-345875565938338554741522432) }, { argument := 345875565938338554741522432, coefficient := (-345875565938338554741522432) }, { argument := 345875565938338554741522432, coefficient := (-345875565938338554741522432) }, { argument := 11068018110026833751728717824, coefficient := (-11068018110026833751728717824) }, { argument := 345875565938338554741522432, coefficient := (-345875565938338554741522432) }, { argument := 399087191467313717009448960, coefficient := (-399087191467313717009448960) }, { argument := 416824399976972104432091136, coefficient := (-416824399976972104432091136) }, { argument := 2467749759130621396616478720, coefficient := (-2467749759130621396616478720) }, { argument := 393969322225934580765991895040, coefficient := (-393969322225934580765991895040) }, { argument := 3931221384399582799220850032640, coefficient := (-3931221384399582799220850032640) }, { argument := 393969322225934580765991895040, coefficient := (-393969322225934580765991895040) }, { argument := 2467468181111551266379530240, coefficient := (-2467468181111551266379530240) }, { argument := 912569812041701779199424987136, coefficient := (-912569812041701779199424987136) }, { argument := 15618109887366411214741569536, coefficient := (-15618109887366411214741569536) }, { argument := 32270314765207712592889900957696, coefficient := (-32270314765207712592889900957696) }, { argument := 386465144659726303037115858944, coefficient := (-386465144659726303037115858944) }, { argument := 12295107783671430105222086656, coefficient := (-12295107783671430105222086656) }, { argument := 32270108761332439395682255634432, coefficient := (-32270108761332439395682255634432) }, { argument := 12627407994040928216174034944, coefficient := (-12627407994040928216174034944) }, { argument := 12627407994040928216174034944, coefficient := (-12627407994040928216174034944) }, { argument := 213669035267587285342102749184, coefficient := (-213669035267587285342102749184) }, { argument := 11630507362932433883318190080, coefficient := (-11630507362932433883318190080) }, { argument := 386465144659726303037115858944, coefficient := (-386465144659726303037115858944) }, { argument := 213669035267587285342102749184, coefficient := (-213669035267587285342102749184) }, { argument := 912778149689176624629278572544, coefficient := (-912778149689176624629278572544) }, { argument := 12295107783671430105222086656, coefficient := (-12295107783671430105222086656) }, { argument := 11630507362932433883318190080, coefficient := (-11630507362932433883318190080) }, { argument := 15618109887366411214741569536, coefficient := (-15618109887366411214741569536) }, { argument := 78509665595729141594849280, coefficient := (-78509665595729141594849280) }, { argument := 12533847740635923893673000960, coefficient := (-12533847740635923893673000960) }, { argument := 125068952040227483724137103360, coefficient := (-125068952040227483724137103360) }, { argument := 12533847740635923893673000960, coefficient := (-12533847740635923893673000960) }, { argument := 78500707395638346393845760, coefficient := (-78500707395638346393845760) }, { argument := 73348357841501397620134772736, coefficient := (-73348357841501397620134772736) }, { argument := 2755886230692779884394632445952, coefficient := (-2755886230692779884394632445952) }, { argument := 2755677797186801993207884283904, coefficient := (-2755677797186801993207884283904) }] }

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
def constantNumerator : ℤ := (-57229726908444786743949237053030400)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3987521649, 47415389902095, 12825, 4185, 648997234520991, 42255,
    189661557094437, 84645, 37935, 12825, 4185, 93827639966071,
    2621177962235529, 1932243155, 1711484239, 80098713755, 21811485371, 163823668118499,
    80098713755, 1932243155, 1932237203, 828118239, 1932237203, 21811485371,
    828118239, 5864182019101, 1711484239, 1291132842149039, 115017451098794077, 1201960229283,
    1117014731738266575, 1233384026127, 39279746055, 1201960229283, 683467581357, 1233384026127,
    19254931516161, 23567847633, 57508752566020411, 1201960229283, 39279746055, 23567847633,
    39279746055, 604908089247, 683467581357, 1291132810323119, 7907074703291741, 67587103513,
    69603802698838741, 1672421306077, 53206868723, 1113661271302702421, 27322446101, 27322446101,
    924649096997, 50330821765, 1672421306077, 924649096997, 31627957109929959, 53206868723,
    50330821765, 67587103513, 4371045, 697825065
  ]
def negativeCoefficients : Array ℕ := #[
    73556791347479288806882934784, 213539932294701820815731589120, 484514801142425598925209600, 19763103730809465219317760, 730705925888304367667861520384, 399087191467313717009448960,
    213539929464253631308064882688, 399724710942501119113297920, 358285945055319982363115520, 484514801142425598925209600, 19763103730809465219317760, 211281062194125206776193220608,
    5902368046997842220422048776192, 142574379873848386272540753920, 126285246972082207418163920896, 5910241893087215983597526712320, 1609403554025187323101413638144, 5902369685543519215544835244032,
    5910241893087215983597526712320, 142574379873848386272540753920, 142573940693765479395535880192, 122208681740832320653772193792, 142573940693765479395535880192, 1609403554025187323101413638144,
    122208681740832320653772193792, 211279423648448211653406752768, 126285246972082207418163920896, 363421586674263842018331459584, 32374534369352078180581755584512, 2771531592045094264089310396416,
    314411695601488243677916771123200, 2843989934320783003019749883904, 90572927844610923663049359360, 2771531592045094264089310396416, 1575968944496230071737058852864, 2843989934320783003019749883904,
    44398849229428274779626795958272, 1739000214616529734330547699712, 32374549578358947330585874399232, 2771531592045094264089310396416, 90572927844610923663049359360, 1739000214616529734330547699712,
    90572927844610923663049359360, 2789646177614016448821920268288, 1575968944496230071737058852864, 363421577716063751223130456064, 8902574671833839997262845968384, 155845250148453345870926053376,
    313467659898059677785458565185536, 3856340977077685983997595746304, 122686686287080293557963063296, 313467780403487717105010187698176, 126002542673217598789259362304, 126002542673217598789259362304,
    2132095656286287263723520262144, 116054973514805683095370465280, 3856340977077685983997595746304, 2132095656286287263723520262144, 8902478490923162059120368943104, 122686686287080293557963063296,
    116054973514805683095370465280, 155845250148453345870926053376, 80631548449667767043358720, 12872600382274732647556055040
  ]
def negativeScales : Array ℕ := #[
    31, 45, 13, 12, 49, 15,
    47, 16, 15, 13, 12, 46,
    51, 30, 30, 36, 34, 47,
    36, 30, 30, 29, 30, 34,
    29, 42, 30, 50, 56, 40,
    59, 40, 35, 40, 39, 40,
    44, 34, 55, 40, 35, 34,
    35, 39, 39, 50, 52, 35,
    55, 40, 35, 59, 34, 34,
    39, 35, 40, 39, 54, 35,
    35, 35, 22, 29
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31892845209385586, 45430420632991995, 13646671205401350, 12031011907437707, 49205205659110735, 15366834443983451,
    47430420613869232, 16369137229852872, 15211241917271758, 13646671205401350, 12031011907437707, 46415078211372486,
    51219136730627562, 30847629511119346, 30672600860703224, 36221060024539044, 34344368970315217, 47219137131131458,
    36221060024539044, 30847629511119346, 30847625067095643, 29625261530023625, 30847625067095643, 34344368970315217,
    29625261530023625, 42415067022812260, 30672600860703224, 50197558867681346, 56674630384760481, 40128526299285276,
    59954353932106381, 40165759205484251, 35193066551479987, 40128526299285276, 39314081952441353, 40165759205484251,
    44130293225459464, 34456100957313839, 55674631062513971, 40128526299285276, 35193066551479987, 34456100957313839,
    35193066551479987, 39137924997287526, 39314081952441353, 50197558832119477, 52812065478930436, 35976028952978815,
    55950015656320598, 40605075466709353, 35630893450871584, 59950016210931497, 34669367598707828, 34669367598707828,
    39750115012783025, 35550723102175957, 40605075466709353, 39750115012783025, 54812049892374879, 35630893450871584,
    35550723102175957, 35976028952978815, 22059546800099931, 29378290177355982
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
noncomputable def negativeCeiling : ℝ := 193936064579 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 73556791347479288806882934784, coefficient := (-73556791347479288806882934784) }, { argument := 213539932294701820815731589120, coefficient := (-213539932294701820815731589120) }, { argument := 484514801142425598925209600, coefficient := (-484514801142425598925209600) }, { argument := 19763103730809465219317760, coefficient := (-19763103730809465219317760) }, { argument := 730705925888304367667861520384, coefficient := (-730705925888304367667861520384) }, { argument := 399087191467313717009448960, coefficient := (-399087191467313717009448960) }, { argument := 213539929464253631308064882688, coefficient := (-213539929464253631308064882688) }, { argument := 399724710942501119113297920, coefficient := (-399724710942501119113297920) }, { argument := 358285945055319982363115520, coefficient := (-358285945055319982363115520) }, { argument := 484514801142425598925209600, coefficient := (-484514801142425598925209600) }, { argument := 19763103730809465219317760, coefficient := (-19763103730809465219317760) }, { argument := 211281062194125206776193220608, coefficient := (-211281062194125206776193220608) }, { argument := 5902368046997842220422048776192, coefficient := (-5902368046997842220422048776192) }, { argument := 142574379873848386272540753920, coefficient := (-142574379873848386272540753920) }, { argument := 126285246972082207418163920896, coefficient := (-126285246972082207418163920896) }, { argument := 5910241893087215983597526712320, coefficient := (-5910241893087215983597526712320) }, { argument := 1609403554025187323101413638144, coefficient := (-1609403554025187323101413638144) }, { argument := 5902369685543519215544835244032, coefficient := (-5902369685543519215544835244032) }, { argument := 5910241893087215983597526712320, coefficient := (-5910241893087215983597526712320) }, { argument := 142574379873848386272540753920, coefficient := (-142574379873848386272540753920) }, { argument := 142573940693765479395535880192, coefficient := (-142573940693765479395535880192) }, { argument := 122208681740832320653772193792, coefficient := (-122208681740832320653772193792) }, { argument := 142573940693765479395535880192, coefficient := (-142573940693765479395535880192) }, { argument := 1609403554025187323101413638144, coefficient := (-1609403554025187323101413638144) }, { argument := 122208681740832320653772193792, coefficient := (-122208681740832320653772193792) }, { argument := 211279423648448211653406752768, coefficient := (-211279423648448211653406752768) }, { argument := 126285246972082207418163920896, coefficient := (-126285246972082207418163920896) }, { argument := 363421586674263842018331459584, coefficient := (-363421586674263842018331459584) }, { argument := 32374534369352078180581755584512, coefficient := (-32374534369352078180581755584512) }, { argument := 2771531592045094264089310396416, coefficient := (-2771531592045094264089310396416) }, { argument := 314411695601488243677916771123200, coefficient := (-314411695601488243677916771123200) }, { argument := 2843989934320783003019749883904, coefficient := (-2843989934320783003019749883904) }, { argument := 90572927844610923663049359360, coefficient := (-90572927844610923663049359360) }, { argument := 2771531592045094264089310396416, coefficient := (-2771531592045094264089310396416) }, { argument := 1575968944496230071737058852864, coefficient := (-1575968944496230071737058852864) }, { argument := 2843989934320783003019749883904, coefficient := (-2843989934320783003019749883904) }, { argument := 44398849229428274779626795958272, coefficient := (-44398849229428274779626795958272) }, { argument := 1739000214616529734330547699712, coefficient := (-1739000214616529734330547699712) }, { argument := 32374549578358947330585874399232, coefficient := (-32374549578358947330585874399232) }, { argument := 2771531592045094264089310396416, coefficient := (-2771531592045094264089310396416) }, { argument := 90572927844610923663049359360, coefficient := (-90572927844610923663049359360) }, { argument := 1739000214616529734330547699712, coefficient := (-1739000214616529734330547699712) }, { argument := 90572927844610923663049359360, coefficient := (-90572927844610923663049359360) }, { argument := 2789646177614016448821920268288, coefficient := (-2789646177614016448821920268288) }, { argument := 1575968944496230071737058852864, coefficient := (-1575968944496230071737058852864) }, { argument := 363421577716063751223130456064, coefficient := (-363421577716063751223130456064) }, { argument := 8902574671833839997262845968384, coefficient := (-8902574671833839997262845968384) }, { argument := 155845250148453345870926053376, coefficient := (-155845250148453345870926053376) }, { argument := 313467659898059677785458565185536, coefficient := (-313467659898059677785458565185536) }, { argument := 3856340977077685983997595746304, coefficient := (-3856340977077685983997595746304) }, { argument := 122686686287080293557963063296, coefficient := (-122686686287080293557963063296) }, { argument := 313467780403487717105010187698176, coefficient := (-313467780403487717105010187698176) }, { argument := 126002542673217598789259362304, coefficient := (-126002542673217598789259362304) }, { argument := 126002542673217598789259362304, coefficient := (-126002542673217598789259362304) }, { argument := 2132095656286287263723520262144, coefficient := (-2132095656286287263723520262144) }, { argument := 116054973514805683095370465280, coefficient := (-116054973514805683095370465280) }, { argument := 3856340977077685983997595746304, coefficient := (-3856340977077685983997595746304) }, { argument := 2132095656286287263723520262144, coefficient := (-2132095656286287263723520262144) }, { argument := 8902478490923162059120368943104, coefficient := (-8902478490923162059120368943104) }, { argument := 122686686287080293557963063296, coefficient := (-122686686287080293557963063296) }, { argument := 116054973514805683095370465280, coefficient := (-116054973514805683095370465280) }, { argument := 155845250148453345870926053376, coefficient := (-155845250148453345870926053376) }, { argument := 80631548449667767043358720, coefficient := (-80631548449667767043358720) }, { argument := 12872600382274732647556055040, coefficient := (-12872600382274732647556055040) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7
