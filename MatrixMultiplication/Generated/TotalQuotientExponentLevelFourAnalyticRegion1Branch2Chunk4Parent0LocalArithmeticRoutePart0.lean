import MatrixMultiplication.BetaFourShardedContributions
import MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalyticRegion1Branch2Chunk4Parent0LocalData

/-! Line-budgeted sparse route chunks, part 0, for region 1, branch 2,
parent 18; untrusted certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent0

open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace RouteChunk0

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot0.Left0.expected,
    Slot1.Left0.expected,
    Slot1.Left1.expected,
    Slot1.Left2.expected,
    Slot1.Left3.expected,
    Slot2.Left0.expected,
    Slot2.Left1.expected,
    Slot2.Left2.expected,
    Slot2.Left3.expected,
    Slot2.Left4.expected,
    Slot2.Left5.expected,
    Slot2.Left6.expected,
    Slot2.Left7.expected,
    Slot2.Left8.expected,
    Slot2.Left9.expected,
    Slot3.Left0.expected,
    Slot3.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 141533750710180957346856960 }, { target := 122, numerator := 20903794306225679814214287360 }, { target := 124, numerator := 217876752136058136185693798400 }, { target := 132, numerator := 20903794306225679814214287360 }, { target := 139, numerator := 141533750710180957346856960 }, { target := 196, numerator := 145577572159043270413910016 }, { target := 197, numerator := 21501045572117842094620409856 }, { target := 199, numerator := 224101802197088368648142192640 }, { target := 207, numerator := 21501045572117842094620409856 }, { target := 214, numerator := 145577572159043270413910016 }, { target := 250, numerator := 506419848561353848730419200 }, { target := 252, numerator := 18352822937426861276685926400 }, { target := 255, numerator := 18352829682017663226740736000 }, { target := 262, numerator := 506413103970551898675609600 }, { target := 466, numerator := 10148653765169531128557600768 }, { target := 468, numerator := 367790571666034299984785965056 }, { target := 471, numerator := 367790706827633971063884349440 }, { target := 478, numerator := 10148518603569860049459216384 }, { target := 562, numerator := 17035963705603943471291301888 }, { target := 564, numerator := 617388963615039613347714564096 }, { target := 567, numerator := 617389190503074190947558359040 }, { target := 574, numerator := 17035736817569365871447506944 }, { target := 597, numerator := 16347232711560502237017931776 }, { target := 599, numerator := 592429124420139082011421704192 }, { target := 602, numerator := 592429342135530168959190958080 }, { target := 609, numerator := 16347014996169415289248677888 }, { target := 613, numerator := 30720366777761007579923742720 }, { target := 616, numerator := 104133746698897596607910379520 }, { target := 618, numerator := 30720366777761007579923742720 }, { target := 733, numerator := 506419848561353848730419200 }, { target := 735, numerator := 18352822937426861276685926400 }, { target := 738, numerator := 18352829682017663226740736000 }, { target := 745, numerator := 506413103970551898675609600 }, { target := 829, numerator := 16347232711560502237017931776 }, { target := 831, numerator := 592429124420139082011421704192 }, { target := 834, numerator := 592429342135530168959190958080 }, { target := 841, numerator := 16347014996169415289248677888 }, { target := 864, numerator := 10918411934982788978627837952 }, { target := 866, numerator := 395686862530923129125348573184 }, { target := 869, numerator := 395687007944300819168530268160 }, { target := 876, numerator := 10918266521605098935446142976 }, { target := 880, numerator := 28078989447336696647818149888 }, { target := 883, numerator := 95180190907964345310781636608 }, { target := 885, numerator := 28078989447336696647818149888 }, { target := 925, numerator := 526676642503808002679635968 }, { target := 927, numerator := 19086935854923935727753363456 }, { target := 930, numerator := 19086942869298369755810365440 }, { target := 937, numerator := 526669628129373974622633984 }, { target := 960, numerator := 10148653765169531128557600768 }, { target := 962, numerator := 367790571666034299984785965056 }, { target := 965, numerator := 367790706827633971063884349440 }, { target := 972, numerator := 10148518603569860049459216384 }, { target := 976, numerator := 30720366777761007579923742720 }, { target := 979, numerator := 104133746698897596607910379520 }, { target := 981, numerator := 30720366777761007579923742720 }, { target := 986, numerator := 486163054618899694781202432 }, { target := 988, numerator := 17618710019929786825618489344 }, { target := 991, numerator := 17618716494736956697671106560 }, { target := 998, numerator := 486156579811729822728585216 }, { target := 1002, numerator := 28078989447336696647818149888 }, { target := 1005, numerator := 95180190907964345310781636608 }, { target := 1007, numerator := 28078989447336696647818149888 }, { target := 1012, numerator := 39614081257132168796771975168 }, { target := 1014, numerator := 39614081257132168796771975168 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk0

namespace RouteChunk1

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot3.Left2.expected,
    Slot3.Left3.expected,
    Slot3.Left4.expected,
    Slot3.Left5.expected,
    Slot3.Left6.expected,
    Slot3.Left7.expected,
    Slot3.Left8.expected,
    Slot3.Left9.expected,
    Slot3.Left10.expected,
    Slot3.Left11.expected,
    Slot3.Left12.expected,
    Slot3.Left13.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 231, numerator := 141533750710180957346856960 }, { target := 232, numerator := 20903794306225679814214287360 }, { target := 234, numerator := 217876752136058136185693798400 }, { target := 242, numerator := 20903794306225679814214287360 }, { target := 249, numerator := 141533750710180957346856960 }, { target := 337, numerator := 125358464914731705078644736 }, { target := 338, numerator := 18514789242657030692589797376 }, { target := 340, numerator := 192976551891937206335900221440 }, { target := 348, numerator := 18514789242657030692589797376 }, { target := 355, numerator := 125358464914731705078644736 }, { target := 412, numerator := 5867584922299216260293984256 }, { target := 413, numerator := 866611586809527468869283741696 }, { target := 415, numerator := 9032547638554867303012620042240 }, { target := 423, numerator := 866611586809527468869283741696 }, { target := 430, numerator := 5867584922299216260293984256 }, { target := 447, numerator := 1597309472300613661485957120 }, { target := 448, numerator := 235914250027404100760418385920 }, { target := 450, numerator := 2458894774106941822667115724800 }, { target := 458, numerator := 235914250027404100760418385920 }, { target := 465, numerator := 1597309472300613661485957120 }, { target := 508, numerator := 145577572159043270413910016 }, { target := 509, numerator := 21501045572117842094620409856 }, { target := 511, numerator := 224101802197088368648142192640 }, { target := 519, numerator := 21501045572117842094620409856 }, { target := 526, numerator := 145577572159043270413910016 }, { target := 543, numerator := 5867584922299216260293984256 }, { target := 544, numerator := 866611586809527468869283741696 }, { target := 546, numerator := 9032547638554867303012620042240 }, { target := 554, numerator := 866611586809527468869283741696 }, { target := 561, numerator := 5867584922299216260293984256 }, { target := 578, numerator := 141533750710180957346856960 }, { target := 579, numerator := 20903794306225679814214287360 }, { target := 581, numerator := 217876752136058136185693798400 }, { target := 589, numerator := 20903794306225679814214287360 }, { target := 596, numerator := 141533750710180957346856960 }, { target := 679, numerator := 141533750710180957346856960 }, { target := 680, numerator := 20903794306225679814214287360 }, { target := 682, numerator := 217876752136058136185693798400 }, { target := 690, numerator := 20903794306225679814214287360 }, { target := 697, numerator := 141533750710180957346856960 }, { target := 714, numerator := 121314643465869392011591680 }, { target := 715, numerator := 17917537976764868412183674880 }, { target := 717, numerator := 186751501830906973873451827200 }, { target := 725, numerator := 17917537976764868412183674880 }, { target := 732, numerator := 121314643465869392011591680 }, { target := 775, numerator := 141533750710180957346856960 }, { target := 776, numerator := 20903794306225679814214287360 }, { target := 778, numerator := 217876752136058136185693798400 }, { target := 786, numerator := 20903794306225679814214287360 }, { target := 793, numerator := 141533750710180957346856960 }, { target := 810, numerator := 1597309472300613661485957120 }, { target := 811, numerator := 235914250027404100760418385920 }, { target := 813, numerator := 2458894774106941822667115724800 }, { target := 821, numerator := 235914250027404100760418385920 }, { target := 828, numerator := 1597309472300613661485957120 }, { target := 845, numerator := 121314643465869392011591680 }, { target := 846, numerator := 17917537976764868412183674880 }, { target := 848, numerator := 186751501830906973873451827200 }, { target := 856, numerator := 17917537976764868412183674880 }, { target := 863, numerator := 121314643465869392011591680 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk1

namespace RouteChunk2

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot3.Left14.expected,
    Slot3.Left15.expected,
    Slot4.Left0.expected,
    Slot4.Left1.expected,
    Slot4.Left2.expected,
    Slot4.Left3.expected,
    Slot4.Left4.expected,
    Slot4.Left5.expected,
    Slot4.Left6.expected,
    Slot4.Left7.expected,
    Slot4.Left8.expected,
    Slot4.Left9.expected,
    Slot4.Left10.expected,
    Slot4.Left11.expected,
    Slot4.Left12.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 80472638972844796110962688 }, { target := 35, numerator := 6766883203324414849424818176 }, { target := 40, numerator := 6766881570787564326129500160 }, { target := 48, numerator := 80474271509695319406280704 }, { target := 79, numerator := 2145937039275861229625671680 }, { target := 80, numerator := 180450218755317729317995151360 }, { target := 85, numerator := 180450175221001715363453337600 }, { target := 93, numerator := 2145980573591875184167485440 }, { target := 105, numerator := 2052052293807542300829548544 }, { target := 106, numerator := 172555521684772578660332863488 }, { target := 111, numerator := 172555480055082890316302254080 }, { target := 119, numerator := 2052093923497230644860157952 }, { target := 154, numerator := 67060532477370663425802240 }, { target := 155, numerator := 5639069336103679041187348480 }, { target := 160, numerator := 5639067975656303605107916800 }, { target := 168, numerator := 67061892924746099505233920 }, { target := 180, numerator := 2105700719789438831570190336 }, { target := 181, numerator := 177066777153655521893282742272 }, { target := 186, numerator := 177066734435607933200388587520 }, { target := 194, numerator := 2105743437837027524464345088 }, { target := 215, numerator := 67060532477370663425802240 }, { target := 216, numerator := 5639069336103679041187348480 }, { target := 221, numerator := 5639067975656303605107916800 }, { target := 229, numerator := 67061892924746099505233920 }, { target := 295, numerator := 2052052293807542300829548544 }, { target := 296, numerator := 172555521684772578660332863488 }, { target := 301, numerator := 172555480055082890316302254080 }, { target := 309, numerator := 2052093923497230644860157952 }, { target := 321, numerator := 1166853265106249543608958976 }, { target := 322, numerator := 98119806448204015316659863552 }, { target := 327, numerator := 98119782776419682728877752320 }, { target := 335, numerator := 1166876936890582131391070208 }, { target := 370, numerator := 2105700719789438831570190336 }, { target := 371, numerator := 177066777153655521893282742272 }, { target := 376, numerator := 177066734435607933200388587520 }, { target := 384, numerator := 2105743437837027524464345088 }, { target := 396, numerator := 32873073020407099211328258048 }, { target := 397, numerator := 2764271788558023465990038224896 }, { target := 402, numerator := 2764271121666720027223900815360 }, { target := 410, numerator := 32873739911710537977465667584 }, { target := 431, numerator := 1287562223565516737775403008 }, { target := 432, numerator := 108270131253190637590797090816 }, { target := 437, numerator := 108270105132601029218072002560 }, { target := 445, numerator := 1287588344155125110500491264 }, { target := 492, numerator := 2145937039275861229625671680 }, { target := 493, numerator := 180450218755317729317995151360 }, { target := 498, numerator := 180450175221001715363453337600 }, { target := 506, numerator := 2145980573591875184167485440 }, { target := 527, numerator := 2052052293807542300829548544 }, { target := 528, numerator := 172555521684772578660332863488 }, { target := 533, numerator := 172555480055082890316302254080 }, { target := 541, numerator := 2052093923497230644860157952 }, { target := 906, numerator := 141533750710180957346856960 }, { target := 907, numerator := 20903794306225679814214287360 }, { target := 909, numerator := 217876752136058136185693798400 }, { target := 917, numerator := 20903794306225679814214287360 }, { target := 924, numerator := 141533750710180957346856960 }, { target := 941, numerator := 125358464914731705078644736 }, { target := 942, numerator := 18514789242657030692589797376 }, { target := 944, numerator := 192976551891937206335900221440 }, { target := 952, numerator := 18514789242657030692589797376 }, { target := 959, numerator := 125358464914731705078644736 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk2

namespace RouteChunk3

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot4.Left13.expected,
    Slot4.Left14.expected,
    Slot4.Left15.expected,
    Slot4.Left16.expected,
    Slot4.Left17.expected,
    Slot4.Left18.expected,
    Slot5.Left0.expected,
    Slot5.Left1.expected,
    Slot5.Left2.expected,
    Slot5.Left3.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 21080643979530096233938944 }, { target := 11, numerator := 504575413961655851792990208 }, { target := 12, numerator := 377411529310942045478584320 }, { target := 13, numerator := 437933378155399418537312256 }, { target := 14, numerator := 21080643979530096233938944 }, { target := 15, numerator := 437253357381866189626540032 }, { target := 16, numerator := 439293419702465876358856704 }, { target := 17, numerator := 21080643979530096233938944 }, { target := 18, numerator := 504575413961655851792990208 }, { target := 19, numerator := 21080643979530096233938944 }, { target := 24, numerator := 20641463896623219229065216 }, { target := 25, numerator := 494063426170788021547302912 }, { target := 26, numerator := 369548789116964086197780480 }, { target := 27, numerator := 428809766110495263984451584 }, { target := 28, numerator := 20641463896623219229065216 }, { target := 29, numerator := 428143912436410644009320448 }, { target := 30, numerator := 430141473458664503934713856 }, { target := 31, numerator := 20641463896623219229065216 }, { target := 32, numerator := 494063426170788021547302912 }, { target := 33, numerator := 20641463896623219229065216 }, { target := 55, numerator := 16249663067554449180327936 }, { target := 56, numerator := 388943548262109719090429952 }, { target := 57, numerator := 290921387177184493389742080 }, { target := 58, numerator := 337573645661453718455844864 }, { target := 59, numerator := 16249663067554449180327936 }, { target := 60, numerator := 337049462981855187837124608 }, { target := 61, numerator := 338622011020650779693285376 }, { target := 62, numerator := 16249663067554449180327936 }, { target := 63, numerator := 388943548262109719090429952 }, { target := 64, numerator := 16249663067554449180327936 }, { target := 69, numerator := 510766436420697956668145664 }, { target := 70, numerator := 12225441800779286575734325248 }, { target := 71, numerator := 9144366845596366643574865920 }, { target := 72, numerator := 10610760808223531744976961536 }, { target := 73, numerator := 510766436420697956668145664 }, { target := 74, numerator := 10594284471564799552826376192 }, { target := 75, numerator := 10643713481540996129278132224 }, { target := 76, numerator := 510766436420697956668145664 }, { target := 77, numerator := 12225441800779286575734325248 }, { target := 78, numerator := 510766436420697956668145664 }, { target := 637, numerator := 67060532477370663425802240 }, { target := 638, numerator := 5639069336103679041187348480 }, { target := 643, numerator := 5639067975656303605107916800 }, { target := 651, numerator := 67061892924746099505233920 }, { target := 663, numerator := 1287562223565516737775403008 }, { target := 664, numerator := 108270131253190637590797090816 }, { target := 669, numerator := 108270105132601029218072002560 }, { target := 677, numerator := 1287588344155125110500491264 }, { target := 698, numerator := 67060532477370663425802240 }, { target := 699, numerator := 5639069336103679041187348480 }, { target := 704, numerator := 5639067975656303605107916800 }, { target := 712, numerator := 67061892924746099505233920 }, { target := 759, numerator := 2065464400303016433514708992 }, { target := 760, numerator := 173683335551993314468570333184 }, { target := 765, numerator := 173683293650214151037323837440 }, { target := 773, numerator := 2065506302082179864761204736 }, { target := 794, numerator := 1166853265106249543608958976 }, { target := 795, numerator := 98119806448204015316659863552 }, { target := 800, numerator := 98119782776419682728877752320 }, { target := 808, numerator := 1166876936890582131391070208 }, { target := 890, numerator := 80472638972844796110962688 }, { target := 891, numerator := 6766883203324414849424818176 }, { target := 896, numerator := 6766881570787564326129500160 }, { target := 904, numerator := 80474271509695319406280704 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk3

namespace RouteChunk4

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot5.Left4.expected,
    Slot5.Left5.expected,
    Slot5.Left6.expected,
    Slot5.Left7.expected,
    Slot5.Left8.expected,
    Slot5.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 95, numerator := 16249663067554449180327936 }, { target := 96, numerator := 388943548262109719090429952 }, { target := 97, numerator := 290921387177184493389742080 }, { target := 98, numerator := 337573645661453718455844864 }, { target := 99, numerator := 16249663067554449180327936 }, { target := 100, numerator := 337049462981855187837124608 }, { target := 101, numerator := 338622011020650779693285376 }, { target := 102, numerator := 16249663067554449180327936 }, { target := 103, numerator := 388943548262109719090429952 }, { target := 104, numerator := 16249663067554449180327936 }, { target := 144, numerator := 16249663067554449180327936 }, { target := 145, numerator := 388943548262109719090429952 }, { target := 146, numerator := 290921387177184493389742080 }, { target := 147, numerator := 337573645661453718455844864 }, { target := 148, numerator := 16249663067554449180327936 }, { target := 149, numerator := 337049462981855187837124608 }, { target := 150, numerator := 338622011020650779693285376 }, { target := 151, numerator := 16249663067554449180327936 }, { target := 152, numerator := 388943548262109719090429952 }, { target := 153, numerator := 16249663067554449180327936 }, { target := 170, numerator := 16688843150461326185201664 }, { target := 171, numerator := 399455536052977549336117248 }, { target := 172, numerator := 298784127371162452670545920 }, { target := 173, numerator := 346697257706357873008705536 }, { target := 174, numerator := 16688843150461326185201664 }, { target := 175, numerator := 346158907927310733454344192 }, { target := 176, numerator := 347773957264452152117428224 }, { target := 177, numerator := 16688843150461326185201664 }, { target := 178, numerator := 399455536052977549336117248 }, { target := 179, numerator := 16688843150461326185201664 }, { target := 271, numerator := 16688843150461326185201664 }, { target := 272, numerator := 399455536052977549336117248 }, { target := 273, numerator := 298784127371162452670545920 }, { target := 274, numerator := 346697257706357873008705536 }, { target := 275, numerator := 16688843150461326185201664 }, { target := 276, numerator := 346158907927310733454344192 }, { target := 277, numerator := 347773957264452152117428224 }, { target := 278, numerator := 16688843150461326185201664 }, { target := 279, numerator := 399455536052977549336117248 }, { target := 280, numerator := 16688843150461326185201664 }, { target := 285, numerator := 282392793309121914133807104 }, { target := 286, numerator := 6759208149528014847976931328 }, { target := 287, numerator := 5055741944727827817556869120 }, { target := 288, numerator := 5866482544873371377489412096 }, { target := 289, numerator := 282392793309121914133807104 }, { target := 290, numerator := 5857373099927915831872192512 }, { target := 291, numerator := 5884701434764282468723851264 }, { target := 292, numerator := 282392793309121914133807104 }, { target := 293, numerator := 6759208149528014847976931328 }, { target := 294, numerator := 282392793309121914133807104 }, { target := 311, numerator := 15371302901740695170580480 }, { target := 312, numerator := 367919572680374058599055360 }, { target := 313, numerator := 275195906789228574828134400 }, { target := 314, numerator := 319326421571645409350123520 }, { target := 315, numerator := 15371302901740695170580480 }, { target := 316, numerator := 318830573090944096602685440 }, { target := 317, numerator := 320318118533048034844999680 }, { target := 318, numerator := 15371302901740695170580480 }, { target := 319, numerator := 367919572680374058599055360 }, { target := 320, numerator := 15371302901740695170580480 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk4

namespace RouteChunk5

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot5.Left10.expected,
    Slot5.Left11.expected,
    Slot5.Left12.expected,
    Slot5.Left13.expected,
    Slot5.Left14.expected,
    Slot5.Left15.expected,
    Slot6.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 360, numerator := 510766436420697956668145664 }, { target := 361, numerator := 12225441800779286575734325248 }, { target := 362, numerator := 9144366845596366643574865920 }, { target := 363, numerator := 10610760808223531744976961536 }, { target := 364, numerator := 510766436420697956668145664 }, { target := 365, numerator := 10594284471564799552826376192 }, { target := 366, numerator := 10643713481540996129278132224 }, { target := 367, numerator := 510766436420697956668145664 }, { target := 368, numerator := 12225441800779286575734325248 }, { target := 369, numerator := 510766436420697956668145664 }, { target := 386, numerator := 282392793309121914133807104 }, { target := 387, numerator := 6759208149528014847976931328 }, { target := 388, numerator := 5055741944727827817556869120 }, { target := 389, numerator := 5866482544873371377489412096 }, { target := 390, numerator := 282392793309121914133807104 }, { target := 391, numerator := 5857373099927915831872192512 }, { target := 392, numerator := 5884701434764282468723851264 }, { target := 393, numerator := 282392793309121914133807104 }, { target := 394, numerator := 6759208149528014847976931328 }, { target := 395, numerator := 282392793309121914133807104 }, { target := 482, numerator := 21080643979530096233938944 }, { target := 483, numerator := 504575413961655851792990208 }, { target := 484, numerator := 377411529310942045478584320 }, { target := 485, numerator := 437933378155399418537312256 }, { target := 486, numerator := 21080643979530096233938944 }, { target := 487, numerator := 437253357381866189626540032 }, { target := 488, numerator := 439293419702465876358856704 }, { target := 489, numerator := 21080643979530096233938944 }, { target := 490, numerator := 504575413961655851792990208 }, { target := 491, numerator := 21080643979530096233938944 }, { target := 613, numerator := 3655064434076276698948567040 }, { target := 616, numerator := 12496912941005151717900156928 }, { target := 618, numerator := 3655063253484655981537263616 }, { target := 627, numerator := 16249663067554449180327936 }, { target := 628, numerator := 388943548262109719090429952 }, { target := 629, numerator := 290921387177184493389742080 }, { target := 630, numerator := 337573645661453718455844864 }, { target := 631, numerator := 16249663067554449180327936 }, { target := 632, numerator := 337049462981855187837124608 }, { target := 633, numerator := 338622011020650779693285376 }, { target := 634, numerator := 16249663067554449180327936 }, { target := 635, numerator := 388943548262109719090429952 }, { target := 636, numerator := 16249663067554449180327936 }, { target := 653, numerator := 15371302901740695170580480 }, { target := 654, numerator := 367919572680374058599055360 }, { target := 655, numerator := 275195906789228574828134400 }, { target := 656, numerator := 319326421571645409350123520 }, { target := 657, numerator := 15371302901740695170580480 }, { target := 658, numerator := 318830573090944096602685440 }, { target := 659, numerator := 320318118533048034844999680 }, { target := 660, numerator := 15371302901740695170580480 }, { target := 661, numerator := 367919572680374058599055360 }, { target := 662, numerator := 15371302901740695170580480 }, { target := 749, numerator := 20641463896623219229065216 }, { target := 750, numerator := 494063426170788021547302912 }, { target := 751, numerator := 369548789116964086197780480 }, { target := 752, numerator := 428809766110495263984451584 }, { target := 753, numerator := 20641463896623219229065216 }, { target := 754, numerator := 428143912436410644009320448 }, { target := 755, numerator := 430141473458664503934713856 }, { target := 756, numerator := 20641463896623219229065216 }, { target := 757, numerator := 494063426170788021547302912 }, { target := 758, numerator := 20641463896623219229065216 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk5

namespace RouteChunk6

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot6.Left1.expected,
    Slot6.Left2.expected,
    Slot6.Left3.expected,
    Slot7.Left0.expected,
    Slot7.Left2.expected,
    Slot7.Left7.expected,
    Slot8.Left0.expected,
    Slot8.Left1.expected,
    Slot8.Left6.expected,
    Slot8.Left14.expected,
    Slot9.Left0.expected,
    Slot9.Left1.expected,
    Slot9.Left3.expected,
    Slot9.Left11.expected,
    Slot9.Left18.expected,
    Slot10.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 3390088350423557866260529152 }, { target := 12, numerator := 32836643528845117458474860544 }, { target := 17, numerator := 3390088350423557866260529152 }, { target := 34, numerator := 188847151160383400868577280 }, { target := 35, numerator := 15812008593511112782085357568 }, { target := 40, numerator := 15812014315863049362563137536 }, { target := 48, numerator := 188841428808446820390797312 }, { target := 79, numerator := 19800283200649150341232721920 }, { target := 80, numerator := 1657860583010462083896104189952 }, { target := 85, numerator := 1657861182988741988420633493504 }, { target := 93, numerator := 19799683222369245816703418368 }, { target := 121, numerator := 189892430594850467663052800 }, { target := 122, numerator := 19909878864121378110649139200 }, { target := 124, numerator := 214608594254715682396569600000 }, { target := 132, numerator := 19909894051870765845630156800 }, { target := 139, numerator := 189892430594850467663052800 }, { target := 154, numerator := 213427262543221834603560960000 }, { target := 155, numerator := 17870080055149531334732414976000 }, { target := 160, numerator := 17870086522315711120253386752000 }, { target := 168, numerator := 213420795377042049082589184000 }, { target := 196, numerator := 15899528936279624476451143680 }, { target := 197, numerator := 1667036933100925896168591851520 }, { target := 199, numerator := 17968991937373606231419125760000 }, { target := 207, numerator := 1667038204758043090411931566080 }, { target := 214, numerator := 15899528936279624476451143680 }, { target := 250, numerator := 3484257471268656695878877184 }, { target := 252, numerator := 121940324511912062084922212352 }, { target := 255, numerator := 121940384319020433322587193344 }, { target := 262, numerator := 3484227567714471077046386688 }, { target := 492, numerator := 19800298304796247868498247680 }, { target := 493, numerator := 1657861847667631844042691575808 }, { target := 498, numerator := 1657862447646369426879352406016 }, { target := 506, numerator := 19799698326058665031837417472 }, { target := 508, numerator := 15899534690305095761248911360 }, { target := 509, numerator := 1667037536400118789094548439040 }, { target := 511, numerator := 17968998440335908783280619520000 }, { target := 519, numerator := 1667038808057696194924810076160 }, { target := 526, numerator := 15899534690305095761248911360 }, { target := 562, numerator := 33748772515757481832321384448 }, { target := 564, numerator := 1181122895304211459909766610944 }, { target := 567, numerator := 1181123474600234182141928275968 }, { target := 574, numerator := 33748482867746120716240551936 }, { target := 880, numerator := 3655064434076276698948567040 }, { target := 883, numerator := 12496912941005151717900156928 }, { target := 885, numerator := 3655063253484655981537263616 }, { target := 890, numerator := 188847151160383400868577280 }, { target := 891, numerator := 15812008593511112782085357568 }, { target := 896, numerator := 15812014315863049362563137536 }, { target := 904, numerator := 188841428808446820390797312 }, { target := 906, numerator := 189886676569379182865285120 }, { target := 907, numerator := 19909275564928485184692551680 }, { target := 909, numerator := 214602091292413130535075840000 }, { target := 917, numerator := 19909290752217661332751646720 }, { target := 924, numerator := 189886676569379182865285120 }, { target := 925, numerator := 3484257471268656695878877184 }, { target := 927, numerator := 121940324511912062084922212352 }, { target := 930, numerator := 121940384319020433322587193344 }, { target := 937, numerator := 3484227567714471077046386688 }, { target := 976, numerator := 3655064434076276698948567040 }, { target := 979, numerator := 12496912941005151717900156928 }, { target := 981, numerator := 3655063253484655981537263616 }, { target := 1002, numerator := 3655064434076276698948567040 }, { target := 1005, numerator := 12496912941005151717900156928 }, { target := 1007, numerator := 3655063253484655981537263616 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk6

namespace RouteChunk7

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot10.Left2.expected,
    Slot10.Left5.expected,
    Slot10.Left12.expected,
    Slot11.Left0.expected,
    Slot11.Left3.expected,
    Slot11.Left5.expected,
    Slot12.Left0.expected,
    Slot12.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 1, numerator := 3655064434076276698948567040 }, { target := 2, numerator := 3655064434076276698948567040 }, { target := 3, numerator := 3655064434076276698948567040 }, { target := 4, numerator := 3655064434076276698948567040 }, { target := 51, numerator := 12496912941005151717900156928 }, { target := 52, numerator := 12496912941005151717900156928 }, { target := 53, numerator := 12496912941005151717900156928 }, { target := 54, numerator := 12496912941005151717900156928 }, { target := 55, numerator := 118644640065644168515059449856 }, { target := 57, numerator := 1149200654890584123155448594432 }, { target := 62, numerator := 118644640065644168515059449856 }, { target := 140, numerator := 3655063253484655981537263616 }, { target := 141, numerator := 3655063253484655981537263616 }, { target := 142, numerator := 3655063253484655981537263616 }, { target := 143, numerator := 3655063253484655981537263616 }, { target := 144, numerator := 118644698256344205394949701632 }, { target := 146, numerator := 1149201218529957582624578863104 }, { target := 151, numerator := 118644698256344205394949701632 }, { target := 250, numerator := 21080643979530096233938944 }, { target := 251, numerator := 20641463896623219229065216 }, { target := 252, numerator := 16249663067554449180327936 }, { target := 253, numerator := 510766436420697956668145664 }, { target := 254, numerator := 16249663067554449180327936 }, { target := 255, numerator := 16249663067554449180327936 }, { target := 256, numerator := 16688843150461326185201664 }, { target := 257, numerator := 16688843150461326185201664 }, { target := 258, numerator := 282392793309121914133807104 }, { target := 259, numerator := 15371302901740695170580480 }, { target := 260, numerator := 510766436420697956668145664 }, { target := 261, numerator := 282392793309121914133807104 }, { target := 262, numerator := 21080643979530096233938944 }, { target := 263, numerator := 16249663067554449180327936 }, { target := 264, numerator := 15371302901740695170580480 }, { target := 265, numerator := 20641463896623219229065216 }, { target := 466, numerator := 504575413961655851792990208 }, { target := 467, numerator := 494063426170788021547302912 }, { target := 468, numerator := 388943548262109719090429952 }, { target := 469, numerator := 12225441800779286575734325248 }, { target := 470, numerator := 388943548262109719090429952 }, { target := 471, numerator := 388943548262109719090429952 }, { target := 472, numerator := 399455536052977549336117248 }, { target := 473, numerator := 399455536052977549336117248 }, { target := 474, numerator := 6759208149528014847976931328 }, { target := 475, numerator := 367919572680374058599055360 }, { target := 476, numerator := 12225441800779286575734325248 }, { target := 477, numerator := 6759208149528014847976931328 }, { target := 478, numerator := 504575413961655851792990208 }, { target := 479, numerator := 388943548262109719090429952 }, { target := 480, numerator := 367919572680374058599055360 }, { target := 481, numerator := 494063426170788021547302912 }, { target := 482, numerator := 3390059255073539426315403264 }, { target := 484, numerator := 32836361709158387723909726208 }, { target := 489, numerator := 3390059255073539426315403264 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk7

namespace RouteChunk8

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot12.Left2.expected,
    Slot12.Left3.expected,
    Slot12.Left4.expected,
    Slot12.Left5.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 562, numerator := 377411529310942045478584320 }, { target := 563, numerator := 369548789116964086197780480 }, { target := 564, numerator := 290921387177184493389742080 }, { target := 565, numerator := 9144366845596366643574865920 }, { target := 566, numerator := 290921387177184493389742080 }, { target := 567, numerator := 290921387177184493389742080 }, { target := 568, numerator := 298784127371162452670545920 }, { target := 569, numerator := 298784127371162452670545920 }, { target := 570, numerator := 5055741944727827817556869120 }, { target := 571, numerator := 275195906789228574828134400 }, { target := 572, numerator := 9144366845596366643574865920 }, { target := 573, numerator := 5055741944727827817556869120 }, { target := 574, numerator := 377411529310942045478584320 }, { target := 575, numerator := 290921387177184493389742080 }, { target := 576, numerator := 275195906789228574828134400 }, { target := 577, numerator := 369548789116964086197780480 }, { target := 597, numerator := 437933378155399418537312256 }, { target := 598, numerator := 428809766110495263984451584 }, { target := 599, numerator := 337573645661453718455844864 }, { target := 600, numerator := 10610760808223531744976961536 }, { target := 601, numerator := 337573645661453718455844864 }, { target := 602, numerator := 337573645661453718455844864 }, { target := 603, numerator := 346697257706357873008705536 }, { target := 604, numerator := 346697257706357873008705536 }, { target := 605, numerator := 5866482544873371377489412096 }, { target := 606, numerator := 319326421571645409350123520 }, { target := 607, numerator := 10610760808223531744976961536 }, { target := 608, numerator := 5866482544873371377489412096 }, { target := 609, numerator := 437933378155399418537312256 }, { target := 610, numerator := 337573645661453718455844864 }, { target := 611, numerator := 319326421571645409350123520 }, { target := 612, numerator := 428809766110495263984451584 }, { target := 733, numerator := 21080643979530096233938944 }, { target := 734, numerator := 20641463896623219229065216 }, { target := 735, numerator := 16249663067554449180327936 }, { target := 736, numerator := 510766436420697956668145664 }, { target := 737, numerator := 16249663067554449180327936 }, { target := 738, numerator := 16249663067554449180327936 }, { target := 739, numerator := 16688843150461326185201664 }, { target := 740, numerator := 16688843150461326185201664 }, { target := 741, numerator := 282392793309121914133807104 }, { target := 742, numerator := 15371302901740695170580480 }, { target := 743, numerator := 510766436420697956668145664 }, { target := 744, numerator := 282392793309121914133807104 }, { target := 745, numerator := 21080643979530096233938944 }, { target := 746, numerator := 16249663067554449180327936 }, { target := 747, numerator := 15371302901740695170580480 }, { target := 748, numerator := 20641463896623219229065216 }, { target := 829, numerator := 437253357381866189626540032 }, { target := 830, numerator := 428143912436410644009320448 }, { target := 831, numerator := 337049462981855187837124608 }, { target := 832, numerator := 10594284471564799552826376192 }, { target := 833, numerator := 337049462981855187837124608 }, { target := 834, numerator := 337049462981855187837124608 }, { target := 835, numerator := 346158907927310733454344192 }, { target := 836, numerator := 346158907927310733454344192 }, { target := 837, numerator := 5857373099927915831872192512 }, { target := 838, numerator := 318830573090944096602685440 }, { target := 839, numerator := 10594284471564799552826376192 }, { target := 840, numerator := 5857373099927915831872192512 }, { target := 841, numerator := 437253357381866189626540032 }, { target := 842, numerator := 337049462981855187837124608 }, { target := 843, numerator := 318830573090944096602685440 }, { target := 844, numerator := 428143912436410644009320448 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk8

namespace RouteChunk9

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot12.Left6.expected,
    Slot12.Left7.expected,
    Slot12.Left8.expected,
    Slot12.Left9.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 864, numerator := 439293419702465876358856704 }, { target := 865, numerator := 430141473458664503934713856 }, { target := 866, numerator := 338622011020650779693285376 }, { target := 867, numerator := 10643713481540996129278132224 }, { target := 868, numerator := 338622011020650779693285376 }, { target := 869, numerator := 338622011020650779693285376 }, { target := 870, numerator := 347773957264452152117428224 }, { target := 871, numerator := 347773957264452152117428224 }, { target := 872, numerator := 5884701434764282468723851264 }, { target := 873, numerator := 320318118533048034844999680 }, { target := 874, numerator := 10643713481540996129278132224 }, { target := 875, numerator := 5884701434764282468723851264 }, { target := 876, numerator := 439293419702465876358856704 }, { target := 877, numerator := 338622011020650779693285376 }, { target := 878, numerator := 320318118533048034844999680 }, { target := 879, numerator := 430141473458664503934713856 }, { target := 925, numerator := 21080643979530096233938944 }, { target := 926, numerator := 20641463896623219229065216 }, { target := 927, numerator := 16249663067554449180327936 }, { target := 928, numerator := 510766436420697956668145664 }, { target := 929, numerator := 16249663067554449180327936 }, { target := 930, numerator := 16249663067554449180327936 }, { target := 931, numerator := 16688843150461326185201664 }, { target := 932, numerator := 16688843150461326185201664 }, { target := 933, numerator := 282392793309121914133807104 }, { target := 934, numerator := 15371302901740695170580480 }, { target := 935, numerator := 510766436420697956668145664 }, { target := 936, numerator := 282392793309121914133807104 }, { target := 937, numerator := 21080643979530096233938944 }, { target := 938, numerator := 16249663067554449180327936 }, { target := 939, numerator := 15371302901740695170580480 }, { target := 940, numerator := 20641463896623219229065216 }, { target := 960, numerator := 504575413961655851792990208 }, { target := 961, numerator := 494063426170788021547302912 }, { target := 962, numerator := 388943548262109719090429952 }, { target := 963, numerator := 12225441800779286575734325248 }, { target := 964, numerator := 388943548262109719090429952 }, { target := 965, numerator := 388943548262109719090429952 }, { target := 966, numerator := 399455536052977549336117248 }, { target := 967, numerator := 399455536052977549336117248 }, { target := 968, numerator := 6759208149528014847976931328 }, { target := 969, numerator := 367919572680374058599055360 }, { target := 970, numerator := 12225441800779286575734325248 }, { target := 971, numerator := 6759208149528014847976931328 }, { target := 972, numerator := 504575413961655851792990208 }, { target := 973, numerator := 388943548262109719090429952 }, { target := 974, numerator := 367919572680374058599055360 }, { target := 975, numerator := 494063426170788021547302912 }, { target := 986, numerator := 21080643979530096233938944 }, { target := 987, numerator := 20641463896623219229065216 }, { target := 988, numerator := 16249663067554449180327936 }, { target := 989, numerator := 510766436420697956668145664 }, { target := 990, numerator := 16249663067554449180327936 }, { target := 991, numerator := 16249663067554449180327936 }, { target := 992, numerator := 16688843150461326185201664 }, { target := 993, numerator := 16688843150461326185201664 }, { target := 994, numerator := 282392793309121914133807104 }, { target := 995, numerator := 15371302901740695170580480 }, { target := 996, numerator := 510766436420697956668145664 }, { target := 997, numerator := 282392793309121914133807104 }, { target := 998, numerator := 21080643979530096233938944 }, { target := 999, numerator := 16249663067554449180327936 }, { target := 1000, numerator := 15371302901740695170580480 }, { target := 1001, numerator := 20641463896623219229065216 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk9

namespace RouteChunk10

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot13.Left0.expected,
    Slot13.Left1.expected,
    Slot13.Left6.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 121, numerator := 83200525039720890894385152 }, { target := 122, numerator := 2218680667725890423850270720 }, { target := 123, numerator := 2121613388512882717806821376 }, { target := 124, numerator := 69333770866434075745320960 }, { target := 125, numerator := 2177080405206029978403078144 }, { target := 126, numerator := 69333770866434075745320960 }, { target := 127, numerator := 2121613388512882717806821376 }, { target := 128, numerator := 1206407613075952917968584704 }, { target := 129, numerator := 2177080405206029978403078144 }, { target := 130, numerator := 33987414478725983930356334592 }, { target := 131, numerator := 1331208400635534254310162432 }, { target := 132, numerator := 2218680667725890423850270720 }, { target := 133, numerator := 2121613388512882717806821376 }, { target := 134, numerator := 69333770866434075745320960 }, { target := 135, numerator := 1331208400635534254310162432 }, { target := 136, numerator := 69333770866434075745320960 }, { target := 137, numerator := 2135480142686169532955885568 }, { target := 138, numerator := 1206407613075952917968584704 }, { target := 139, numerator := 83200525039720890894385152 }, { target := 196, numerator := 6996269074623547556184981504 }, { target := 197, numerator := 186567175323294601498266173440 }, { target := 198, numerator := 178404861402900462682717028352 }, { target := 199, numerator := 5830224228852956296820817920 }, { target := 200, numerator := 183069040785982827720173682688 }, { target := 201, numerator := 5830224228852956296820817920 }, { target := 202, numerator := 178404861402900462682717028352 }, { target := 203, numerator := 101445901582041439564682231808 }, { target := 204, numerator := 183069040785982827720173682688 }, { target := 205, numerator := 2857975916983719176701564944384 }, { target := 206, numerator := 111940305193976760898959704064 }, { target := 207, numerator := 186567175323294601498266173440 }, { target := 208, numerator := 178404861402900462682717028352 }, { target := 209, numerator := 5830224228852956296820817920 }, { target := 210, numerator := 111940305193976760898959704064 }, { target := 211, numerator := 5830224228852956296820817920 }, { target := 212, numerator := 179570906248671053942081191936 }, { target := 213, numerator := 101445901582041439564682231808 }, { target := 214, numerator := 6996269074623547556184981504 }, { target := 508, numerator := 6996267386746464811761008640 }, { target := 509, numerator := 186567130313239061646960230400 }, { target := 510, numerator := 178404818362034852699905720320 }, { target := 511, numerator := 5830222822288720676467507200 }, { target := 512, numerator := 183068996619865829241079726080 }, { target := 513, numerator := 5830222822288720676467507200 }, { target := 514, numerator := 178404818362034852699905720320 }, { target := 515, numerator := 101445877107823739770534625280 }, { target := 516, numerator := 183068996619865829241079726080 }, { target := 517, numerator := 2857975227485930875604372029440 }, { target := 518, numerator := 111940278187943436988176138240 }, { target := 519, numerator := 186567130313239061646960230400 }, { target := 520, numerator := 178404818362034852699905720320 }, { target := 521, numerator := 5830222822288720676467507200 }, { target := 522, numerator := 111940278187943436988176138240 }, { target := 523, numerator := 5830222822288720676467507200 }, { target := 524, numerator := 179570862926492596835199221760 }, { target := 525, numerator := 101445877107823739770534625280 }, { target := 526, numerator := 6996267386746464811761008640 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk10

namespace RouteChunk11

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot13.Left14.expected,
    Slot14.Left0.expected,
    Slot14.Left1.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 34, numerator := 141165173234373194437099520 }, { target := 35, numerator := 145198463898212428563873792 }, { target := 36, numerator := 141165173234373194437099520 }, { target := 37, numerator := 125032010579016257930002432 }, { target := 38, numerator := 5852304753230728717949468672 }, { target := 39, numerator := 1593149812216497480075837440 }, { target := 40, numerator := 145198463898212428563873792 }, { target := 41, numerator := 5852304753230728717949468672 }, { target := 42, numerator := 141165173234373194437099520 }, { target := 43, numerator := 141165173234373194437099520 }, { target := 44, numerator := 120998719915177023803228160 }, { target := 45, numerator := 141165173234373194437099520 }, { target := 46, numerator := 1593149812216497480075837440 }, { target := 47, numerator := 120998719915177023803228160 }, { target := 48, numerator := 141165173234373194437099520 }, { target := 49, numerator := 125032010579016257930002432 }, { target := 79, numerator := 20849357341886550439698104320 }, { target := 80, numerator := 21445053265940451880832335872 }, { target := 81, numerator := 20849357341886550439698104320 }, { target := 82, numerator := 18466573645670944675161178112 }, { target := 83, numerator := 864354785802210991085769981952 }, { target := 84, numerator := 235299890001291069248021463040 }, { target := 85, numerator := 21445053265940451880832335872 }, { target := 86, numerator := 864354785802210991085769981952 }, { target := 87, numerator := 20849357341886550439698104320 }, { target := 88, numerator := 20849357341886550439698104320 }, { target := 89, numerator := 17870877721617043234026946560 }, { target := 90, numerator := 20849357341886550439698104320 }, { target := 91, numerator := 235299890001291069248021463040 }, { target := 92, numerator := 17870877721617043234026946560 }, { target := 93, numerator := 20849357341886550439698104320 }, { target := 94, numerator := 18466573645670944675161178112 }, { target := 906, numerator := 83202212916803635318358016 }, { target := 907, numerator := 2218725677781430275156213760 }, { target := 908, numerator := 2121656429378492700618129408 }, { target := 909, numerator := 69335177430669696098631680 }, { target := 910, numerator := 2177124571323028457497034752 }, { target := 911, numerator := 69335177430669696098631680 }, { target := 912, numerator := 2121656429378492700618129408 }, { target := 913, numerator := 1206432087293652712116191232 }, { target := 914, numerator := 2177124571323028457497034752 }, { target := 915, numerator := 33988103976514285027549249536 }, { target := 916, numerator := 1331235406668858165093728256 }, { target := 917, numerator := 2218725677781430275156213760 }, { target := 918, numerator := 2121656429378492700618129408 }, { target := 919, numerator := 69335177430669696098631680 }, { target := 920, numerator := 1331235406668858165093728256 }, { target := 921, numerator := 69335177430669696098631680 }, { target := 922, numerator := 2135523464864626639837855744 }, { target := 923, numerator := 1206432087293652712116191232 }, { target := 924, numerator := 83202212916803635318358016 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk11

namespace RouteChunk12

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot14.Left3.expected,
    Slot14.Left11.expected,
    Slot14.Left18.expected,
    Slot15.Left0.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 10, numerator := 512912410722396846791065600 }, { target := 11, numerator := 10278764710876832809692954624 }, { target := 12, numerator := 17254373496701429926051446784 }, { target := 13, numerator := 16556812618118970214415597568 }, { target := 14, numerator := 512912410722396846791065600 }, { target := 15, numerator := 16556812618118970214415597568 }, { target := 16, numerator := 11058391575174876016815374336 }, { target := 17, numerator := 533428907151292720662708224 }, { target := 18, numerator := 10278764710876832809692954624 }, { target := 19, numerator := 492395914293500972919422976 }, { target := 154, numerator := 217309364760703818122710220800 }, { target := 155, numerator := 223518203753866784354787655680 }, { target := 156, numerator := 217309364760703818122710220800 }, { target := 157, numerator := 192474008788051953194400481280 }, { target := 158, numerator := 9009025379079464002744358010880 }, { target := 159, numerator := 2452491402299371661670586777600 }, { target := 160, numerator := 223518203753866784354787655680 }, { target := 161, numerator := 9009025379079464002744358010880 }, { target := 162, numerator := 217309364760703818122710220800 }, { target := 163, numerator := 217309364760703818122710220800 }, { target := 164, numerator := 186265169794888986962323046400 }, { target := 165, numerator := 217309364760703818122710220800 }, { target := 166, numerator := 2452491402299371661670586777600 }, { target := 167, numerator := 186265169794888986962323046400 }, { target := 168, numerator := 217309364760703818122710220800 }, { target := 169, numerator := 192474008788051953194400481280 }, { target := 492, numerator := 20849357341886550439698104320 }, { target := 493, numerator := 21445053265940451880832335872 }, { target := 494, numerator := 20849357341886550439698104320 }, { target := 495, numerator := 18466573645670944675161178112 }, { target := 496, numerator := 864354785802210991085769981952 }, { target := 497, numerator := 235299890001291069248021463040 }, { target := 498, numerator := 21445053265940451880832335872 }, { target := 499, numerator := 864354785802210991085769981952 }, { target := 500, numerator := 20849357341886550439698104320 }, { target := 501, numerator := 20849357341886550439698104320 }, { target := 502, numerator := 17870877721617043234026946560 }, { target := 503, numerator := 20849357341886550439698104320 }, { target := 504, numerator := 235299890001291069248021463040 }, { target := 505, numerator := 17870877721617043234026946560 }, { target := 506, numerator := 20849357341886550439698104320 }, { target := 507, numerator := 18466573645670944675161178112 }, { target := 890, numerator := 141165173234373194437099520 }, { target := 891, numerator := 145198463898212428563873792 }, { target := 892, numerator := 141165173234373194437099520 }, { target := 893, numerator := 125032010579016257930002432 }, { target := 894, numerator := 5852304753230728717949468672 }, { target := 895, numerator := 1593149812216497480075837440 }, { target := 896, numerator := 145198463898212428563873792 }, { target := 897, numerator := 5852304753230728717949468672 }, { target := 898, numerator := 141165173234373194437099520 }, { target := 899, numerator := 141165173234373194437099520 }, { target := 900, numerator := 120998719915177023803228160 }, { target := 901, numerator := 141165173234373194437099520 }, { target := 902, numerator := 1593149812216497480075837440 }, { target := 903, numerator := 120998719915177023803228160 }, { target := 904, numerator := 141165173234373194437099520 }, { target := 905, numerator := 125032010579016257930002432 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk12

namespace RouteChunk13

/-- Fixed-left rows containing at most 64 actual routed contributions. -/
def rows : List (List (Option BetaFourRoutedContribution)) :=
  [
    Slot15.Left2.expected,
    Slot15.Left5.expected,
    Slot15.Left12.expected,
    Slot16.Left0.expected,
    Slot16.Left3.expected,
    Slot16.Left5.expected,
    Slot17.Left0.expected,
    Slot17.Left2.expected
  ]

/-- Producer-proposed normalization of this bounded route chunk. -/
def normalized : List BetaFourRoutedContribution :=
  [{ target := 0, numerator := 39614081257132168796771975168 }, { target := 1, numerator := 30720366777761007579923742720 }, { target := 2, numerator := 28078989447336696647818149888 }, { target := 3, numerator := 30720366777761007579923742720 }, { target := 4, numerator := 28078989447336696647818149888 }, { target := 50, numerator := 39614081257132168796771975168 }, { target := 51, numerator := 104133746698897596607910379520 }, { target := 52, numerator := 95180190907964345310781636608 }, { target := 53, numerator := 104133746698897596607910379520 }, { target := 54, numerator := 95180190907964345310781636608 }, { target := 55, numerator := 18588115539188744113566515200 }, { target := 56, numerator := 372505835405342432035872964608 }, { target := 57, numerator := 625304206738309351980377571328 }, { target := 58, numerator := 600024369605012659985927110656 }, { target := 59, numerator := 18588115539188744113566515200 }, { target := 60, numerator := 600024369605012659985927110656 }, { target := 61, numerator := 400759771024909323088494067712 }, { target := 62, numerator := 19331640160756293878109175808 }, { target := 63, numerator := 372505835405342432035872964608 }, { target := 64, numerator := 17844590917621194349023854592 }, { target := 140, numerator := 30720366777761007579923742720 }, { target := 141, numerator := 28078989447336696647818149888 }, { target := 142, numerator := 30720366777761007579923742720 }, { target := 143, numerator := 28078989447336696647818149888 }, { target := 144, numerator := 18588122370248658909134848000 }, { target := 145, numerator := 372505972299783124539062353920 }, { target := 146, numerator := 625304436535164885703296286720 }, { target := 147, numerator := 600024590111626709586872893440 }, { target := 148, numerator := 18588122370248658909134848000 }, { target := 149, numerator := 600024590111626709586872893440 }, { target := 150, numerator := 400759918302561086080947322880 }, { target := 151, numerator := 19331647265058605265500241920 }, { target := 152, numerator := 372505972299783124539062353920 }, { target := 153, numerator := 17844597475438712552769454080 }, { target := 482, numerator := 512905579662482051222732800 }, { target := 483, numerator := 10278627816436140306503565312 }, { target := 484, numerator := 17254143699845896203132731392 }, { target := 485, numerator := 16556592111504920613469814784 }, { target := 486, numerator := 512905579662482051222732800 }, { target := 487, numerator := 16556592111504920613469814784 }, { target := 488, numerator := 11058244297523113024362119168 }, { target := 489, numerator := 533421802848981333271642112 }, { target := 490, numerator := 10278627816436140306503565312 }, { target := 491, numerator := 492389356475982769173823488 }]

/-- Every route in this bounded chunk names a genuine support member. -/
theorem targetsBelowSupport :
    BetaFourRoutedContribution.AllTargetsBelow ParentSupport.codes.length rows.flatten := by
  rw [ParentSupport.codes_length]
  decide +kernel

/-- Kernel normalization checks only this bounded source chunk. -/
theorem normalized_eq :
    BetaFourRoutedContribution.canonicalizeRows rows = normalized := by
  decide +kernel

end RouteChunk13

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4.Parent0
