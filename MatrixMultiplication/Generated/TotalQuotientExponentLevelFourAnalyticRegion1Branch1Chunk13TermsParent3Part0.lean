import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
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

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-262800227426096163359478408806400)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    12893291519, 51548000255, 25744640003, 51548000255, 10956247996489, 20714986587,
    401217842278079, 8724919883, 854114511, 8723621341, 17450855609, 1374506562847,
    20714986587, 854114511, 20330210524909, 1478103496130835, 148213905, 382302555,
    319891395, 8958080265, 738927675716325, 319891395, 289081815, 148329105,
    148213905, 288851415, 8958080265, 288851415, 10165045955867, 382302555,
    48175, 35875, 37925, 3075, 659075, 1192075,
    35875, 659075, 19475, 19475, 37925, 37925,
    1192075, 37925, 48175, 3075, 5493103167, 54829428705,
    130438717, 70865613155643, 41278075, 4953369, 130438717, 259226311,
    41278075, 4000671029, 255924065, 7018179282517, 130438717, 4953369,
    255924065, 4953369, 130438717, 130438717
  ]
def negativeCoefficients : Array ℕ := #[
    59459812229680718179966386176, 59430798013468731593593978880, 59363098175640762892058361856, 59430798013468731593593978880, 24671277197183301883655094272, 191062028030357550529612087296,
    903462262488975510184596078592, 160946364145320884461453180928, 7877815897029290817264549888, 160922410273377921512878637056, 160955733643240919127474307072, 24760908977024201766310248448,
    191062028030357550529612087296, 7877815897029290817264549888, 11444891068042988535947460608, 832098294298731985262629355520, 5468127947400200961612840960, 7052237390810269910701178880,
    94415275119150900660267909120, 165247414040203239673288458240, 831958601252446993988242636800, 94415275119150900660267909120, 5332618257668450963989463040, 5472378077234783642305167360,
    5468127947400200961612840960, 5328368127833868283297136640, 165247414040203239673288458240, 5328368127833868283297136640, 11444824294761647132018475008, 7052237390810269910701178880,
    227500005312245158169804800, 169414897572948522041344000, 179095748862831294729420800, 232340430957186544513843200, 3112393689697311419216691200, 5629415025066832318116659200,
    169414897572948522041344000, 3112393689697311419216691200, 183936174507772681073459200, 183936174507772681073459200, 179095748862831294729420800, 179095748862831294729420800,
    5629415025066832318116659200, 179095748862831294729420800, 227500005312245158169804800, 232340430957186544513843200, 197909899008071131679686656, 31607013719651222662718423040,
    1203084814901013671718158336, 319150349001135533956874108928, 761446085380388399821619200, 45686765122823303989297152, 1203084814901013671718158336, 1195470354047209787719942144,
    761446085380388399821619200, 18449838648766810927677833216, 1180241432339602019723509760, 31607069601562896172614418432, 1203084814901013671718158336, 45686765122823303989297152,
    1180241432339602019723509760, 45686765122823303989297152, 1203084814901013671718158336, 1203084814901013671718158336
  ]
def negativeScales : Array ℕ := #[
    33, 35, 34, 35, 43, 34,
    48, 33, 29, 33, 34, 40,
    34, 29, 44, 50, 27, 28,
    28, 33, 49, 28, 28, 27,
    27, 28, 33, 28, 43, 28,
    15, 15, 15, 11, 19, 20,
    15, 19, 14, 14, 15, 15,
    20, 15, 15, 11, 32, 35,
    26, 46, 25, 22, 26, 27,
    25, 31, 27, 42, 26, 22,
    27, 22, 26, 26
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33585901564163185, 35585197409872209, 34583553045405338, 35585197409872209, 43316819060702553, 34269955835042791,
    48511379092882385, 33022494737752188, 29669854263847217, 33022280003456273, 34022578721847238, 40322050933941716,
    34269955835042791, 29669854263847217, 44208690388298761, 50392668713178238, 27143105562569211, 28510139601106818,
    28253006943931988, 33060542446882113, 49392426492535261, 28253006943931988, 28106902616497451, 27144226468956928,
    27143105562569211, 28105752321142293, 33060542446882113, 28105752321142293, 43208681971113984, 28510139601106818,
    15555997046072039, 15130691211337775, 15210861560021759, 11586370695117825, 19330083121720757, 20185043575866027,
    15130691211337775, 19330083121720757, 14249335707836394, 14249335707836394, 15210861560021759, 15210861560021759,
    20185043575866027, 15210861560021759, 15555997046072039, 11586370695117825, 32354974241623043, 35674231390470791,
    26958796927050616, 46010150977161336, 25298872356564039, 22239978667510471, 26958796927050616, 27949636926041265,
    25298872356564039, 31897594860423681, 27931140579617666, 42674233941185843, 26958796927050616, 22239978667510471,
    27931140579617666, 22239978667510471, 26958796927050616, 26958796927050616
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
noncomputable def negativeCeiling : ℝ := 2453942207 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 59459812229680718179966386176, coefficient := (-59459812229680718179966386176) }, { argument := 59430798013468731593593978880, coefficient := (-59430798013468731593593978880) }, { argument := 59363098175640762892058361856, coefficient := (-59363098175640762892058361856) }, { argument := 59430798013468731593593978880, coefficient := (-59430798013468731593593978880) }, { argument := 24671277197183301883655094272, coefficient := (-24671277197183301883655094272) }, { argument := 191062028030357550529612087296, coefficient := (-191062028030357550529612087296) }, { argument := 903462262488975510184596078592, coefficient := (-903462262488975510184596078592) }, { argument := 160946364145320884461453180928, coefficient := (-160946364145320884461453180928) }, { argument := 7877815897029290817264549888, coefficient := (-7877815897029290817264549888) }, { argument := 160922410273377921512878637056, coefficient := (-160922410273377921512878637056) }, { argument := 160955733643240919127474307072, coefficient := (-160955733643240919127474307072) }, { argument := 24760908977024201766310248448, coefficient := (-24760908977024201766310248448) }, { argument := 191062028030357550529612087296, coefficient := (-191062028030357550529612087296) }, { argument := 7877815897029290817264549888, coefficient := (-7877815897029290817264549888) }, { argument := 11444891068042988535947460608, coefficient := (-11444891068042988535947460608) }, { argument := 832098294298731985262629355520, coefficient := (-832098294298731985262629355520) }, { argument := 5468127947400200961612840960, coefficient := (-5468127947400200961612840960) }, { argument := 7052237390810269910701178880, coefficient := (-7052237390810269910701178880) }, { argument := 94415275119150900660267909120, coefficient := (-94415275119150900660267909120) }, { argument := 165247414040203239673288458240, coefficient := (-165247414040203239673288458240) }, { argument := 831958601252446993988242636800, coefficient := (-831958601252446993988242636800) }, { argument := 94415275119150900660267909120, coefficient := (-94415275119150900660267909120) }, { argument := 5332618257668450963989463040, coefficient := (-5332618257668450963989463040) }, { argument := 5472378077234783642305167360, coefficient := (-5472378077234783642305167360) }, { argument := 5468127947400200961612840960, coefficient := (-5468127947400200961612840960) }, { argument := 5328368127833868283297136640, coefficient := (-5328368127833868283297136640) }, { argument := 165247414040203239673288458240, coefficient := (-165247414040203239673288458240) }, { argument := 5328368127833868283297136640, coefficient := (-5328368127833868283297136640) }, { argument := 11444824294761647132018475008, coefficient := (-11444824294761647132018475008) }, { argument := 7052237390810269910701178880, coefficient := (-7052237390810269910701178880) }, { argument := 227500005312245158169804800, coefficient := (-227500005312245158169804800) }, { argument := 169414897572948522041344000, coefficient := (-169414897572948522041344000) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 232340430957186544513843200, coefficient := (-232340430957186544513843200) }, { argument := 3112393689697311419216691200, coefficient := (-3112393689697311419216691200) }, { argument := 5629415025066832318116659200, coefficient := (-5629415025066832318116659200) }, { argument := 169414897572948522041344000, coefficient := (-169414897572948522041344000) }, { argument := 3112393689697311419216691200, coefficient := (-3112393689697311419216691200) }, { argument := 183936174507772681073459200, coefficient := (-183936174507772681073459200) }, { argument := 183936174507772681073459200, coefficient := (-183936174507772681073459200) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 5629415025066832318116659200, coefficient := (-5629415025066832318116659200) }, { argument := 179095748862831294729420800, coefficient := (-179095748862831294729420800) }, { argument := 227500005312245158169804800, coefficient := (-227500005312245158169804800) }, { argument := 232340430957186544513843200, coefficient := (-232340430957186544513843200) }, { argument := 197909899008071131679686656, coefficient := (-197909899008071131679686656) }, { argument := 31607013719651222662718423040, coefficient := (-31607013719651222662718423040) }, { argument := 1203084814901013671718158336, coefficient := (-1203084814901013671718158336) }, { argument := 319150349001135533956874108928, coefficient := (-319150349001135533956874108928) }, { argument := 761446085380388399821619200, coefficient := (-761446085380388399821619200) }, { argument := 45686765122823303989297152, coefficient := (-45686765122823303989297152) }, { argument := 1203084814901013671718158336, coefficient := (-1203084814901013671718158336) }, { argument := 1195470354047209787719942144, coefficient := (-1195470354047209787719942144) }, { argument := 761446085380388399821619200, coefficient := (-761446085380388399821619200) }, { argument := 18449838648766810927677833216, coefficient := (-18449838648766810927677833216) }, { argument := 1180241432339602019723509760, coefficient := (-1180241432339602019723509760) }, { argument := 31607069601562896172614418432, coefficient := (-31607069601562896172614418432) }, { argument := 1203084814901013671718158336, coefficient := (-1203084814901013671718158336) }, { argument := 45686765122823303989297152, coefficient := (-45686765122823303989297152) }, { argument := 1180241432339602019723509760, coefficient := (-1180241432339602019723509760) }, { argument := 45686765122823303989297152, coefficient := (-45686765122823303989297152) }, { argument := 1203084814901013671718158336, coefficient := (-1203084814901013671718158336) }, { argument := 1203084814901013671718158336, coefficient := (-1203084814901013671718158336) }] }

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
def constantNumerator : ℤ := (-8076616662438744013997259924439040)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    5493103167, 12893289473, 51547992065, 25744635901, 51547992065, 39800825658069,
    38414089735, 1450350933823379, 517763748565, 25342497985, 258843930695, 517781007555,
    4993000160435, 38414089735, 25342497985, 781751077303049, 57773288039288055, 22549955955,
    58155386705, 48660649545, 1361343069915, 902555884749345, 48660649545, 43914688965,
    22550365555, 22549955955, 43913869765, 1361343069915, 43913869765, 12214788052831,
    58155386705, 504075, 375375, 396825, 32175, 6896175,
    12473175, 375375, 6896175, 203775, 203775, 396825,
    396825, 12473175, 396825, 504075, 32175, 3506898554715,
    948695147145315, 5344098385, 18605130925377927, 1691170375, 202940445, 5344098385,
    10620549955, 1691170375, 163908232745, 10485256325, 1897393617922779, 5344098385,
    202940445, 10485256325, 202940445, 5344098385
  ]
def negativeCoefficients : Array ℕ := #[
    197909899008071131679686656, 59459802794171124477530734592, 59430788571041608863517245440, 59363088717072739097485770752, 59430788571041608863517245440, 89623491801358812321637466112,
    708614882166058170103638261760, 3265899962561710283928729812992, 596940960026441006859094589440, 29217910907362187706483343360, 596853468070459643756428656640, 596960858287159801384984903680,
    89945894647983570980742103040, 708614882166058170103638261760, 29217910907362187706483343360, 440086732554811911187399180288, 32523469810713252246119944028160, 207986633187653831201799536640,
    268194383763686499520159416320, 3590522194468344557221057658880, 6278086801810023509745897308160, 32518002769905587804563266600960, 3590522194468344557221057658880, 202520757103477998241563279360,
    207990411080840126917970493440, 207986633187653831201799536640, 202516979210291702525392322560, 6278086801810023509745897308160, 202516979210291702525392322560, 440084119385114224067669393408,
    268194383763686499520159416320, 2380426884852516411093811200, 1772658318507193072091136000, 1873953079564746961924915200, 2431074265381293356010700800, 32566265680003575581560012800,
    58902903554967586938342604800, 1772658318507193072091136000, 32566265680003575581560012800, 1924600460093523906841804800, 1924600460093523906841804800, 1873953079564746961924915200,
    1873953079564746961924915200, 58902903554967586938342604800, 1873953079564746961924915200, 2380426884852516411093811200, 2431074265381293356010700800, 31587334048481209956465377280,
    4272543111171838506034255626240, 197162430425639071500279480320, 41895030351355661729281024720896, 124786348370657640190050304000, 7487180902239458411403018240, 197162430425639071500279480320,
    195914566941932495098378977280, 124786348370657640190050304000, 3023573221021034621804918865920, 193418839974519342294577971200, 4272550595326092382534675464192, 197162430425639071500279480320,
    7487180902239458411403018240, 193418839974519342294577971200, 7487180902239458411403018240, 197162430425639071500279480320
  ]
def negativeScales : Array ℕ := #[
    32, 33, 35, 34, 35, 45,
    35, 50, 38, 34, 37, 38,
    42, 35, 34, 49, 55, 34,
    35, 35, 40, 49, 35, 35,
    34, 34, 35, 40, 35, 43,
    35, 18, 18, 18, 14, 22,
    23, 18, 22, 17, 17, 18,
    18, 23, 18, 18, 14, 41,
    49, 32, 54, 30, 27, 32,
    33, 30, 37, 33, 50, 32,
    27, 33, 27, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32354974241623043, 33585901335225968, 35585197180655299, 34583552815534750, 35585197180655299, 45177863592959063,
    35160916516655879, 50365323447157198, 38913503007220198, 34560839685388633, 37913291539951451, 38913551096810877,
    42183044091673009, 35160916516655879, 34560839685388633, 49473702630701027, 55681252123065538, 34392405564457827,
    35759193778209764, 35502036527043719, 40308167822606070, 49681009592496164, 35502036527043719, 35353984534474236,
    34392431769498899, 34392405564457827, 35353957621684259, 40308167822606070, 35353957621684259, 43473694064166574,
    35759193778209764, 18943278888253396, 18517973044219726, 18598143392908592, 14973652543452428, 22717364954710554,
    23572325408750069, 18517973044219726, 22717364954710554, 17636617540732957, 17636617540732957, 18598143392908592,
    18598143392908592, 23572325408750069, 18598143392908592, 18943278888253396, 14973652543452428, 41673332836535173,
    49752937896037652, 32315299422098570, 54046550061025303, 30655374863720606, 27596481174647752, 32315299422098570,
    33306139422813094, 30655374863720606, 37254097363372814, 33287643079195705, 50752940423184259, 32315299422098570,
    27596481174647752, 33287643079195705, 27596481174647752, 32315299422098570
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
noncomputable def negativeCeiling : ℝ := 89767819171 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 197909899008071131679686656, coefficient := (-197909899008071131679686656) }, { argument := 59459802794171124477530734592, coefficient := (-59459802794171124477530734592) }, { argument := 59430788571041608863517245440, coefficient := (-59430788571041608863517245440) }, { argument := 59363088717072739097485770752, coefficient := (-59363088717072739097485770752) }, { argument := 59430788571041608863517245440, coefficient := (-59430788571041608863517245440) }, { argument := 89623491801358812321637466112, coefficient := (-89623491801358812321637466112) }, { argument := 708614882166058170103638261760, coefficient := (-708614882166058170103638261760) }, { argument := 3265899962561710283928729812992, coefficient := (-3265899962561710283928729812992) }, { argument := 596940960026441006859094589440, coefficient := (-596940960026441006859094589440) }, { argument := 29217910907362187706483343360, coefficient := (-29217910907362187706483343360) }, { argument := 596853468070459643756428656640, coefficient := (-596853468070459643756428656640) }, { argument := 596960858287159801384984903680, coefficient := (-596960858287159801384984903680) }, { argument := 89945894647983570980742103040, coefficient := (-89945894647983570980742103040) }, { argument := 708614882166058170103638261760, coefficient := (-708614882166058170103638261760) }, { argument := 29217910907362187706483343360, coefficient := (-29217910907362187706483343360) }, { argument := 440086732554811911187399180288, coefficient := (-440086732554811911187399180288) }, { argument := 32523469810713252246119944028160, coefficient := (-32523469810713252246119944028160) }, { argument := 207986633187653831201799536640, coefficient := (-207986633187653831201799536640) }, { argument := 268194383763686499520159416320, coefficient := (-268194383763686499520159416320) }, { argument := 3590522194468344557221057658880, coefficient := (-3590522194468344557221057658880) }, { argument := 6278086801810023509745897308160, coefficient := (-6278086801810023509745897308160) }, { argument := 32518002769905587804563266600960, coefficient := (-32518002769905587804563266600960) }, { argument := 3590522194468344557221057658880, coefficient := (-3590522194468344557221057658880) }, { argument := 202520757103477998241563279360, coefficient := (-202520757103477998241563279360) }, { argument := 207990411080840126917970493440, coefficient := (-207990411080840126917970493440) }, { argument := 207986633187653831201799536640, coefficient := (-207986633187653831201799536640) }, { argument := 202516979210291702525392322560, coefficient := (-202516979210291702525392322560) }, { argument := 6278086801810023509745897308160, coefficient := (-6278086801810023509745897308160) }, { argument := 202516979210291702525392322560, coefficient := (-202516979210291702525392322560) }, { argument := 440084119385114224067669393408, coefficient := (-440084119385114224067669393408) }, { argument := 268194383763686499520159416320, coefficient := (-268194383763686499520159416320) }, { argument := 2380426884852516411093811200, coefficient := (-2380426884852516411093811200) }, { argument := 1772658318507193072091136000, coefficient := (-1772658318507193072091136000) }, { argument := 1873953079564746961924915200, coefficient := (-1873953079564746961924915200) }, { argument := 2431074265381293356010700800, coefficient := (-2431074265381293356010700800) }, { argument := 32566265680003575581560012800, coefficient := (-32566265680003575581560012800) }, { argument := 58902903554967586938342604800, coefficient := (-58902903554967586938342604800) }, { argument := 1772658318507193072091136000, coefficient := (-1772658318507193072091136000) }, { argument := 32566265680003575581560012800, coefficient := (-32566265680003575581560012800) }, { argument := 1924600460093523906841804800, coefficient := (-1924600460093523906841804800) }, { argument := 1924600460093523906841804800, coefficient := (-1924600460093523906841804800) }, { argument := 1873953079564746961924915200, coefficient := (-1873953079564746961924915200) }, { argument := 1873953079564746961924915200, coefficient := (-1873953079564746961924915200) }, { argument := 58902903554967586938342604800, coefficient := (-58902903554967586938342604800) }, { argument := 1873953079564746961924915200, coefficient := (-1873953079564746961924915200) }, { argument := 2380426884852516411093811200, coefficient := (-2380426884852516411093811200) }, { argument := 2431074265381293356010700800, coefficient := (-2431074265381293356010700800) }, { argument := 31587334048481209956465377280, coefficient := (-31587334048481209956465377280) }, { argument := 4272543111171838506034255626240, coefficient := (-4272543111171838506034255626240) }, { argument := 197162430425639071500279480320, coefficient := (-197162430425639071500279480320) }, { argument := 41895030351355661729281024720896, coefficient := (-41895030351355661729281024720896) }, { argument := 124786348370657640190050304000, coefficient := (-124786348370657640190050304000) }, { argument := 7487180902239458411403018240, coefficient := (-7487180902239458411403018240) }, { argument := 197162430425639071500279480320, coefficient := (-197162430425639071500279480320) }, { argument := 195914566941932495098378977280, coefficient := (-195914566941932495098378977280) }, { argument := 124786348370657640190050304000, coefficient := (-124786348370657640190050304000) }, { argument := 3023573221021034621804918865920, coefficient := (-3023573221021034621804918865920) }, { argument := 193418839974519342294577971200, coefficient := (-193418839974519342294577971200) }, { argument := 4272550595326092382534675464192, coefficient := (-4272550595326092382534675464192) }, { argument := 197162430425639071500279480320, coefficient := (-197162430425639071500279480320) }, { argument := 7487180902239458411403018240, coefficient := (-7487180902239458411403018240) }, { argument := 193418839974519342294577971200, coefficient := (-193418839974519342294577971200) }, { argument := 7487180902239458411403018240, coefficient := (-7487180902239458411403018240) }, { argument := 197162430425639071500279480320, coefficient := (-197162430425639071500279480320) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13
