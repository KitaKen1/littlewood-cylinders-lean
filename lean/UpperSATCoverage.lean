import UpperSATCases.Group00
import UpperSATCases.Group01
import UpperSATCases.Group02
import UpperSATCases.Group03
import UpperSATCases.Group04
import UpperSATCases.Group05
import UpperSATCases.Group06
import UpperSATCases.Group07
import UpperSATCases.Group08
import UpperSATCases.Group09
import UpperSATCases.Group10
import UpperSATCases.Group11
import UpperSATCases.Group12
import UpperSATCases.Group13
import UpperContactCoverage

/-! All contact representatives are excluded by checked local clauses and LRAT. -/
namespace LittlewoodCylinders.Upper
open GraphCover
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem sat_matrix_000 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[0]) a b = SAT.Case000.E a b := by
  decide +kernel

theorem sat_matrix_001 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[1]) a b = SAT.Case001.E a b := by
  decide +kernel

theorem sat_matrix_002 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[2]) a b = SAT.Case002.E a b := by
  decide +kernel

theorem sat_matrix_003 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[3]) a b = SAT.Case003.E a b := by
  decide +kernel

theorem sat_matrix_004 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[4]) a b = SAT.Case004.E a b := by
  decide +kernel

theorem sat_matrix_005 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[5]) a b = SAT.Case005.E a b := by
  decide +kernel

theorem sat_matrix_006 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[6]) a b = SAT.Case006.E a b := by
  decide +kernel

theorem sat_matrix_007 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[7]) a b = SAT.Case007.E a b := by
  decide +kernel

theorem sat_matrix_008 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[8]) a b = SAT.Case008.E a b := by
  decide +kernel

theorem sat_matrix_009 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[9]) a b = SAT.Case009.E a b := by
  decide +kernel

theorem sat_matrix_010 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[10]) a b = SAT.Case010.E a b := by
  decide +kernel

theorem sat_matrix_011 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[11]) a b = SAT.Case011.E a b := by
  decide +kernel

theorem sat_matrix_012 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[12]) a b = SAT.Case012.E a b := by
  decide +kernel

theorem sat_matrix_013 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[13]) a b = SAT.Case013.E a b := by
  decide +kernel

theorem sat_matrix_014 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[14]) a b = SAT.Case014.E a b := by
  decide +kernel

theorem sat_matrix_015 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[15]) a b = SAT.Case015.E a b := by
  decide +kernel

theorem sat_matrix_016 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[16]) a b = SAT.Case016.E a b := by
  decide +kernel

theorem sat_matrix_017 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[17]) a b = SAT.Case017.E a b := by
  decide +kernel

theorem sat_matrix_018 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[18]) a b = SAT.Case018.E a b := by
  decide +kernel

theorem sat_matrix_019 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[19]) a b = SAT.Case019.E a b := by
  decide +kernel

theorem sat_matrix_020 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[20]) a b = SAT.Case020.E a b := by
  decide +kernel

theorem sat_matrix_021 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[21]) a b = SAT.Case021.E a b := by
  decide +kernel

theorem sat_matrix_022 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[22]) a b = SAT.Case022.E a b := by
  decide +kernel

theorem sat_matrix_023 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[23]) a b = SAT.Case023.E a b := by
  decide +kernel

theorem sat_matrix_024 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[24]) a b = SAT.Case024.E a b := by
  decide +kernel

theorem sat_matrix_025 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[25]) a b = SAT.Case025.E a b := by
  decide +kernel

theorem sat_matrix_026 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[26]) a b = SAT.Case026.E a b := by
  decide +kernel

theorem sat_matrix_027 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[27]) a b = SAT.Case027.E a b := by
  decide +kernel

theorem sat_matrix_028 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[28]) a b = SAT.Case028.E a b := by
  decide +kernel

theorem sat_matrix_029 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[29]) a b = SAT.Case029.E a b := by
  decide +kernel

theorem sat_matrix_030 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[30]) a b = SAT.Case030.E a b := by
  decide +kernel

theorem sat_matrix_031 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[31]) a b = SAT.Case031.E a b := by
  decide +kernel

theorem sat_matrix_032 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[32]) a b = SAT.Case032.E a b := by
  decide +kernel

theorem sat_matrix_033 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[33]) a b = SAT.Case033.E a b := by
  decide +kernel

theorem sat_matrix_034 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[34]) a b = SAT.Case034.E a b := by
  decide +kernel

theorem sat_matrix_035 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[35]) a b = SAT.Case035.E a b := by
  decide +kernel

theorem sat_matrix_036 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[36]) a b = SAT.Case036.E a b := by
  decide +kernel

theorem sat_matrix_037 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[37]) a b = SAT.Case037.E a b := by
  decide +kernel

theorem sat_matrix_038 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[38]) a b = SAT.Case038.E a b := by
  decide +kernel

theorem sat_matrix_039 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[39]) a b = SAT.Case039.E a b := by
  decide +kernel

theorem sat_matrix_040 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[40]) a b = SAT.Case040.E a b := by
  decide +kernel

theorem sat_matrix_041 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[41]) a b = SAT.Case041.E a b := by
  decide +kernel

theorem sat_matrix_042 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[42]) a b = SAT.Case042.E a b := by
  decide +kernel

theorem sat_matrix_043 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[43]) a b = SAT.Case043.E a b := by
  decide +kernel

theorem sat_matrix_044 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[44]) a b = SAT.Case044.E a b := by
  decide +kernel

theorem sat_matrix_045 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[45]) a b = SAT.Case045.E a b := by
  decide +kernel

theorem sat_matrix_046 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[46]) a b = SAT.Case046.E a b := by
  decide +kernel

theorem sat_matrix_047 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[47]) a b = SAT.Case047.E a b := by
  decide +kernel

theorem sat_matrix_048 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[48]) a b = SAT.Case048.E a b := by
  decide +kernel

theorem sat_matrix_049 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[49]) a b = SAT.Case049.E a b := by
  decide +kernel

theorem sat_matrix_050 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[50]) a b = SAT.Case050.E a b := by
  decide +kernel

theorem sat_matrix_051 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[51]) a b = SAT.Case051.E a b := by
  decide +kernel

theorem sat_matrix_052 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[52]) a b = SAT.Case052.E a b := by
  decide +kernel

theorem sat_matrix_053 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[53]) a b = SAT.Case053.E a b := by
  decide +kernel

theorem sat_matrix_054 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[54]) a b = SAT.Case054.E a b := by
  decide +kernel

theorem sat_matrix_055 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[55]) a b = SAT.Case055.E a b := by
  decide +kernel

theorem sat_matrix_056 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[56]) a b = SAT.Case056.E a b := by
  decide +kernel

theorem sat_matrix_057 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[57]) a b = SAT.Case057.E a b := by
  decide +kernel

theorem sat_matrix_058 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[58]) a b = SAT.Case058.E a b := by
  decide +kernel

theorem sat_matrix_059 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[59]) a b = SAT.Case059.E a b := by
  decide +kernel

theorem sat_matrix_060 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[60]) a b = SAT.Case060.E a b := by
  decide +kernel

theorem sat_matrix_061 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[61]) a b = SAT.Case061.E a b := by
  decide +kernel

theorem sat_matrix_062 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[62]) a b = SAT.Case062.E a b := by
  decide +kernel

theorem sat_matrix_063 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[63]) a b = SAT.Case063.E a b := by
  decide +kernel

theorem sat_matrix_064 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[64]) a b = SAT.Case064.E a b := by
  decide +kernel

theorem sat_matrix_065 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[65]) a b = SAT.Case065.E a b := by
  decide +kernel

theorem sat_matrix_066 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[66]) a b = SAT.Case066.E a b := by
  decide +kernel

theorem sat_matrix_067 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[67]) a b = SAT.Case067.E a b := by
  decide +kernel

theorem sat_matrix_068 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[68]) a b = SAT.Case068.E a b := by
  decide +kernel

theorem sat_matrix_069 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[69]) a b = SAT.Case069.E a b := by
  decide +kernel

theorem sat_matrix_070 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[70]) a b = SAT.Case070.E a b := by
  decide +kernel

theorem sat_matrix_071 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[71]) a b = SAT.Case071.E a b := by
  decide +kernel

theorem sat_matrix_072 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[72]) a b = SAT.Case072.E a b := by
  decide +kernel

theorem sat_matrix_073 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[73]) a b = SAT.Case073.E a b := by
  decide +kernel

theorem sat_matrix_074 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[74]) a b = SAT.Case074.E a b := by
  decide +kernel

theorem sat_matrix_075 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[75]) a b = SAT.Case075.E a b := by
  decide +kernel

theorem sat_matrix_076 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[76]) a b = SAT.Case076.E a b := by
  decide +kernel

theorem sat_matrix_077 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[77]) a b = SAT.Case077.E a b := by
  decide +kernel

theorem sat_matrix_078 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[78]) a b = SAT.Case078.E a b := by
  decide +kernel

theorem sat_matrix_079 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[79]) a b = SAT.Case079.E a b := by
  decide +kernel

theorem sat_matrix_080 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[80]) a b = SAT.Case080.E a b := by
  decide +kernel

theorem sat_matrix_081 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[81]) a b = SAT.Case081.E a b := by
  decide +kernel

theorem sat_matrix_082 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[82]) a b = SAT.Case082.E a b := by
  decide +kernel

theorem sat_matrix_083 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[83]) a b = SAT.Case083.E a b := by
  decide +kernel

theorem sat_matrix_084 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[84]) a b = SAT.Case084.E a b := by
  decide +kernel

theorem sat_matrix_085 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[85]) a b = SAT.Case085.E a b := by
  decide +kernel

theorem sat_matrix_086 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[86]) a b = SAT.Case086.E a b := by
  decide +kernel

theorem sat_matrix_087 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[87]) a b = SAT.Case087.E a b := by
  decide +kernel

theorem sat_matrix_088 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[88]) a b = SAT.Case088.E a b := by
  decide +kernel

theorem sat_matrix_089 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[89]) a b = SAT.Case089.E a b := by
  decide +kernel

theorem sat_matrix_090 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[90]) a b = SAT.Case090.E a b := by
  decide +kernel

theorem sat_matrix_091 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[91]) a b = SAT.Case091.E a b := by
  decide +kernel

theorem sat_matrix_092 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[92]) a b = SAT.Case092.E a b := by
  decide +kernel

theorem sat_matrix_093 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[93]) a b = SAT.Case093.E a b := by
  decide +kernel

theorem sat_matrix_094 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[94]) a b = SAT.Case094.E a b := by
  decide +kernel

theorem sat_matrix_095 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[95]) a b = SAT.Case095.E a b := by
  decide +kernel

theorem sat_matrix_096 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[96]) a b = SAT.Case096.E a b := by
  decide +kernel

theorem sat_matrix_097 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[97]) a b = SAT.Case097.E a b := by
  decide +kernel

theorem sat_matrix_098 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[98]) a b = SAT.Case098.E a b := by
  decide +kernel

theorem sat_matrix_099 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[99]) a b = SAT.Case099.E a b := by
  decide +kernel

theorem sat_matrix_100 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[100]) a b = SAT.Case100.E a b := by
  decide +kernel

theorem sat_matrix_101 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[101]) a b = SAT.Case101.E a b := by
  decide +kernel

theorem sat_matrix_102 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[102]) a b = SAT.Case102.E a b := by
  decide +kernel

theorem sat_matrix_103 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[103]) a b = SAT.Case103.E a b := by
  decide +kernel

theorem sat_matrix_104 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[104]) a b = SAT.Case104.E a b := by
  decide +kernel

theorem sat_matrix_105 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[105]) a b = SAT.Case105.E a b := by
  decide +kernel

theorem sat_matrix_106 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[106]) a b = SAT.Case106.E a b := by
  decide +kernel

theorem sat_matrix_107 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[107]) a b = SAT.Case107.E a b := by
  decide +kernel

theorem sat_matrix_108 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[108]) a b = SAT.Case108.E a b := by
  decide +kernel

theorem sat_matrix_109 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[109]) a b = SAT.Case109.E a b := by
  decide +kernel

theorem sat_matrix_110 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[110]) a b = SAT.Case110.E a b := by
  decide +kernel

theorem sat_matrix_111 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[111]) a b = SAT.Case111.E a b := by
  decide +kernel

theorem sat_matrix_112 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[112]) a b = SAT.Case112.E a b := by
  decide +kernel

theorem sat_matrix_113 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[113]) a b = SAT.Case113.E a b := by
  decide +kernel

theorem sat_matrix_114 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[114]) a b = SAT.Case114.E a b := by
  decide +kernel

theorem sat_matrix_115 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[115]) a b = SAT.Case115.E a b := by
  decide +kernel

theorem sat_matrix_116 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[116]) a b = SAT.Case116.E a b := by
  decide +kernel

theorem sat_matrix_117 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[117]) a b = SAT.Case117.E a b := by
  decide +kernel

theorem sat_matrix_118 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[118]) a b = SAT.Case118.E a b := by
  decide +kernel

theorem sat_matrix_119 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[119]) a b = SAT.Case119.E a b := by
  decide +kernel

theorem sat_matrix_120 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[120]) a b = SAT.Case120.E a b := by
  decide +kernel

theorem sat_matrix_121 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[121]) a b = SAT.Case121.E a b := by
  decide +kernel

theorem sat_matrix_122 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[122]) a b = SAT.Case122.E a b := by
  decide +kernel

theorem sat_matrix_123 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[123]) a b = SAT.Case123.E a b := by
  decide +kernel

theorem sat_matrix_124 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[124]) a b = SAT.Case124.E a b := by
  decide +kernel

theorem sat_matrix_125 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[125]) a b = SAT.Case125.E a b := by
  decide +kernel

theorem sat_matrix_126 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[126]) a b = SAT.Case126.E a b := by
  decide +kernel

theorem sat_matrix_127 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[127]) a b = SAT.Case127.E a b := by
  decide +kernel

theorem sat_matrix_128 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[128]) a b = SAT.Case128.E a b := by
  decide +kernel

theorem sat_matrix_129 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[129]) a b = SAT.Case129.E a b := by
  decide +kernel

theorem sat_matrix_130 :
    ∀ a b, contactOfGraph (maskGraph 7 contactReps131[130]) a b = SAT.Case130.E a b := by
  decide +kernel

theorem all_contact_representatives_excluded
    (k : Fin contactReps131.size) (χ : Fin 8 → Fin 8 → Fin 8 → ℤ)
    (hu : ∀ a b c, χ a b c = 1 ∨ χ a b c = -1) (hfirst : χ 0 1 2 = 1)
    (hr : SignRealizable (contactOfGraph (maskGraph 7 contactReps131[k])) χ)
    (hn : NecessarySignChecks (contactOfGraph (maskGraph 7 contactReps131[k])) χ) : False := by
  simp only [Fin.getElem_fin] at hr hn
  fin_cases k
  · have he := funext fun a => funext fun b => sat_matrix_000 a b
    rw [he] at hr hn
    exact SAT.Case000.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_001 a b
    rw [he] at hr hn
    exact SAT.Case001.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_002 a b
    rw [he] at hr hn
    exact SAT.Case002.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_003 a b
    rw [he] at hr hn
    exact SAT.Case003.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_004 a b
    rw [he] at hr hn
    exact SAT.Case004.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_005 a b
    rw [he] at hr hn
    exact SAT.Case005.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_006 a b
    rw [he] at hr hn
    exact SAT.Case006.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_007 a b
    rw [he] at hr hn
    exact SAT.Case007.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_008 a b
    rw [he] at hr hn
    exact SAT.Case008.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_009 a b
    rw [he] at hr hn
    exact SAT.Case009.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_010 a b
    rw [he] at hr hn
    exact SAT.Case010.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_011 a b
    rw [he] at hr hn
    exact SAT.Case011.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_012 a b
    rw [he] at hr hn
    exact SAT.Case012.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_013 a b
    rw [he] at hr hn
    exact SAT.Case013.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_014 a b
    rw [he] at hr hn
    exact SAT.Case014.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_015 a b
    rw [he] at hr hn
    exact SAT.Case015.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_016 a b
    rw [he] at hr hn
    exact SAT.Case016.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_017 a b
    rw [he] at hr hn
    exact SAT.Case017.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_018 a b
    rw [he] at hr hn
    exact SAT.Case018.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_019 a b
    rw [he] at hr hn
    exact SAT.Case019.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_020 a b
    rw [he] at hr hn
    exact SAT.Case020.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_021 a b
    rw [he] at hr hn
    exact SAT.Case021.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_022 a b
    rw [he] at hr hn
    exact SAT.Case022.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_023 a b
    rw [he] at hr hn
    exact SAT.Case023.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_024 a b
    rw [he] at hr hn
    exact SAT.Case024.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_025 a b
    rw [he] at hr hn
    exact SAT.Case025.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_026 a b
    rw [he] at hr hn
    exact SAT.Case026.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_027 a b
    rw [he] at hr hn
    exact SAT.Case027.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_028 a b
    rw [he] at hr hn
    exact SAT.Case028.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_029 a b
    rw [he] at hr hn
    exact SAT.Case029.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_030 a b
    rw [he] at hr hn
    exact SAT.Case030.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_031 a b
    rw [he] at hr hn
    exact SAT.Case031.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_032 a b
    rw [he] at hr hn
    exact SAT.Case032.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_033 a b
    rw [he] at hr hn
    exact SAT.Case033.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_034 a b
    rw [he] at hr hn
    exact SAT.Case034.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_035 a b
    rw [he] at hr hn
    exact SAT.Case035.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_036 a b
    rw [he] at hr hn
    exact SAT.Case036.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_037 a b
    rw [he] at hr hn
    exact SAT.Case037.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_038 a b
    rw [he] at hr hn
    exact SAT.Case038.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_039 a b
    rw [he] at hr hn
    exact SAT.Case039.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_040 a b
    rw [he] at hr hn
    exact SAT.Case040.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_041 a b
    rw [he] at hr hn
    exact SAT.Case041.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_042 a b
    rw [he] at hr hn
    exact SAT.Case042.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_043 a b
    rw [he] at hr hn
    exact SAT.Case043.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_044 a b
    rw [he] at hr hn
    exact SAT.Case044.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_045 a b
    rw [he] at hr hn
    exact SAT.Case045.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_046 a b
    rw [he] at hr hn
    exact SAT.Case046.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_047 a b
    rw [he] at hr hn
    exact SAT.Case047.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_048 a b
    rw [he] at hr hn
    exact SAT.Case048.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_049 a b
    rw [he] at hr hn
    exact SAT.Case049.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_050 a b
    rw [he] at hr hn
    exact SAT.Case050.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_051 a b
    rw [he] at hr hn
    exact SAT.Case051.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_052 a b
    rw [he] at hr hn
    exact SAT.Case052.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_053 a b
    rw [he] at hr hn
    exact SAT.Case053.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_054 a b
    rw [he] at hr hn
    exact SAT.Case054.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_055 a b
    rw [he] at hr hn
    exact SAT.Case055.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_056 a b
    rw [he] at hr hn
    exact SAT.Case056.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_057 a b
    rw [he] at hr hn
    exact SAT.Case057.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_058 a b
    rw [he] at hr hn
    exact SAT.Case058.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_059 a b
    rw [he] at hr hn
    exact SAT.Case059.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_060 a b
    rw [he] at hr hn
    exact SAT.Case060.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_061 a b
    rw [he] at hr hn
    exact SAT.Case061.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_062 a b
    rw [he] at hr hn
    exact SAT.Case062.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_063 a b
    rw [he] at hr hn
    exact SAT.Case063.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_064 a b
    rw [he] at hr hn
    exact SAT.Case064.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_065 a b
    rw [he] at hr hn
    exact SAT.Case065.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_066 a b
    rw [he] at hr hn
    exact SAT.Case066.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_067 a b
    rw [he] at hr hn
    exact SAT.Case067.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_068 a b
    rw [he] at hr hn
    exact SAT.Case068.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_069 a b
    rw [he] at hr hn
    exact SAT.Case069.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_070 a b
    rw [he] at hr hn
    exact SAT.Case070.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_071 a b
    rw [he] at hr hn
    exact SAT.Case071.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_072 a b
    rw [he] at hr hn
    exact SAT.Case072.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_073 a b
    rw [he] at hr hn
    exact SAT.Case073.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_074 a b
    rw [he] at hr hn
    exact SAT.Case074.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_075 a b
    rw [he] at hr hn
    exact SAT.Case075.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_076 a b
    rw [he] at hr hn
    exact SAT.Case076.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_077 a b
    rw [he] at hr hn
    exact SAT.Case077.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_078 a b
    rw [he] at hr hn
    exact SAT.Case078.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_079 a b
    rw [he] at hr hn
    exact SAT.Case079.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_080 a b
    rw [he] at hr hn
    exact SAT.Case080.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_081 a b
    rw [he] at hr hn
    exact SAT.Case081.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_082 a b
    rw [he] at hr hn
    exact SAT.Case082.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_083 a b
    rw [he] at hr hn
    exact SAT.Case083.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_084 a b
    rw [he] at hr hn
    exact SAT.Case084.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_085 a b
    rw [he] at hr hn
    exact SAT.Case085.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_086 a b
    rw [he] at hr hn
    exact SAT.Case086.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_087 a b
    rw [he] at hr hn
    exact SAT.Case087.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_088 a b
    rw [he] at hr hn
    exact SAT.Case088.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_089 a b
    rw [he] at hr hn
    exact SAT.Case089.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_090 a b
    rw [he] at hr hn
    exact SAT.Case090.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_091 a b
    rw [he] at hr hn
    exact SAT.Case091.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_092 a b
    rw [he] at hr hn
    exact SAT.Case092.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_093 a b
    rw [he] at hr hn
    exact SAT.Case093.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_094 a b
    rw [he] at hr hn
    exact SAT.Case094.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_095 a b
    rw [he] at hr hn
    exact SAT.Case095.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_096 a b
    rw [he] at hr hn
    exact SAT.Case096.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_097 a b
    rw [he] at hr hn
    exact SAT.Case097.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_098 a b
    rw [he] at hr hn
    exact SAT.Case098.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_099 a b
    rw [he] at hr hn
    exact SAT.Case099.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_100 a b
    rw [he] at hr hn
    exact SAT.Case100.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_101 a b
    rw [he] at hr hn
    exact SAT.Case101.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_102 a b
    rw [he] at hr hn
    exact SAT.Case102.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_103 a b
    rw [he] at hr hn
    exact SAT.Case103.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_104 a b
    rw [he] at hr hn
    exact SAT.Case104.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_105 a b
    rw [he] at hr hn
    exact SAT.Case105.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_106 a b
    rw [he] at hr hn
    exact SAT.Case106.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_107 a b
    rw [he] at hr hn
    exact SAT.Case107.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_108 a b
    rw [he] at hr hn
    exact SAT.Case108.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_109 a b
    rw [he] at hr hn
    exact SAT.Case109.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_110 a b
    rw [he] at hr hn
    exact SAT.Case110.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_111 a b
    rw [he] at hr hn
    exact SAT.Case111.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_112 a b
    rw [he] at hr hn
    exact SAT.Case112.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_113 a b
    rw [he] at hr hn
    exact SAT.Case113.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_114 a b
    rw [he] at hr hn
    exact SAT.Case114.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_115 a b
    rw [he] at hr hn
    exact SAT.Case115.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_116 a b
    rw [he] at hr hn
    exact SAT.Case116.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_117 a b
    rw [he] at hr hn
    exact SAT.Case117.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_118 a b
    rw [he] at hr hn
    exact SAT.Case118.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_119 a b
    rw [he] at hr hn
    exact SAT.Case119.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_120 a b
    rw [he] at hr hn
    exact SAT.Case120.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_121 a b
    rw [he] at hr hn
    exact SAT.Case121.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_122 a b
    rw [he] at hr hn
    exact SAT.Case122.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_123 a b
    rw [he] at hr hn
    exact SAT.Case123.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_124 a b
    rw [he] at hr hn
    exact SAT.Case124.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_125 a b
    rw [he] at hr hn
    exact SAT.Case125.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_126 a b
    rw [he] at hr hn
    exact SAT.Case126.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_127 a b
    rw [he] at hr hn
    exact SAT.Case127.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_128 a b
    rw [he] at hr hn
    exact SAT.Case128.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_129 a b
    rw [he] at hr hn
    exact SAT.Case129.excluded χ hu hfirst hr hn
  · have he := funext fun a => funext fun b => sat_matrix_130 a b
    rw [he] at hr hn
    exact SAT.Case130.excluded χ hu hfirst hr hn

theorem no_eight_affine_axes
    (L : Fin 8 → AffineSubspace ℝ Space)
    (hdim : ∀ i, Module.finrank ℝ (L i).direction = 1)
    (hdist : ∀ i j, i ≠ j →
      sInf {r : ℝ | ∃ x ∈ L i, ∃ y ∈ L j, dist x y = r} = 1) : False := by
  obtain ⟨k, χ, hu, hfirst, hr, hn⟩ := eight_axes_reduce_to_131 L hdim hdist
  exact all_contact_representatives_excluded k χ hu hfirst hr hn

#print axioms all_contact_representatives_excluded
#print axioms no_eight_affine_axes

end LittlewoodCylinders.Upper
