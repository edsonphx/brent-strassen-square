import Brent.Generated.OriginBlocks.Block15
import Mathlib.Tactic.FinCases

namespace Brent.TangentData

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem checkedBatch (q : Fin 126) (r : Fin 2) :
    checkOrigin (Fin.ofNat 251 (q.val * 2 + r.val)) = true := by
  fin_cases q
  · exact originBatch0 r
  · exact originBatch1 r
  · exact originBatch2 r
  · exact originBatch3 r
  · exact originBatch4 r
  · exact originBatch5 r
  · exact originBatch6 r
  · exact originBatch7 r
  · exact originBatch8 r
  · exact originBatch9 r
  · exact originBatch10 r
  · exact originBatch11 r
  · exact originBatch12 r
  · exact originBatch13 r
  · exact originBatch14 r
  · exact originBatch15 r
  · exact originBatch16 r
  · exact originBatch17 r
  · exact originBatch18 r
  · exact originBatch19 r
  · exact originBatch20 r
  · exact originBatch21 r
  · exact originBatch22 r
  · exact originBatch23 r
  · exact originBatch24 r
  · exact originBatch25 r
  · exact originBatch26 r
  · exact originBatch27 r
  · exact originBatch28 r
  · exact originBatch29 r
  · exact originBatch30 r
  · exact originBatch31 r
  · exact originBatch32 r
  · exact originBatch33 r
  · exact originBatch34 r
  · exact originBatch35 r
  · exact originBatch36 r
  · exact originBatch37 r
  · exact originBatch38 r
  · exact originBatch39 r
  · exact originBatch40 r
  · exact originBatch41 r
  · exact originBatch42 r
  · exact originBatch43 r
  · exact originBatch44 r
  · exact originBatch45 r
  · exact originBatch46 r
  · exact originBatch47 r
  · exact originBatch48 r
  · exact originBatch49 r
  · exact originBatch50 r
  · exact originBatch51 r
  · exact originBatch52 r
  · exact originBatch53 r
  · exact originBatch54 r
  · exact originBatch55 r
  · exact originBatch56 r
  · exact originBatch57 r
  · exact originBatch58 r
  · exact originBatch59 r
  · exact originBatch60 r
  · exact originBatch61 r
  · exact originBatch62 r
  · exact originBatch63 r
  · exact originBatch64 r
  · exact originBatch65 r
  · exact originBatch66 r
  · exact originBatch67 r
  · exact originBatch68 r
  · exact originBatch69 r
  · exact originBatch70 r
  · exact originBatch71 r
  · exact originBatch72 r
  · exact originBatch73 r
  · exact originBatch74 r
  · exact originBatch75 r
  · exact originBatch76 r
  · exact originBatch77 r
  · exact originBatch78 r
  · exact originBatch79 r
  · exact originBatch80 r
  · exact originBatch81 r
  · exact originBatch82 r
  · exact originBatch83 r
  · exact originBatch84 r
  · exact originBatch85 r
  · exact originBatch86 r
  · exact originBatch87 r
  · exact originBatch88 r
  · exact originBatch89 r
  · exact originBatch90 r
  · exact originBatch91 r
  · exact originBatch92 r
  · exact originBatch93 r
  · exact originBatch94 r
  · exact originBatch95 r
  · exact originBatch96 r
  · exact originBatch97 r
  · exact originBatch98 r
  · exact originBatch99 r
  · exact originBatch100 r
  · exact originBatch101 r
  · exact originBatch102 r
  · exact originBatch103 r
  · exact originBatch104 r
  · exact originBatch105 r
  · exact originBatch106 r
  · exact originBatch107 r
  · exact originBatch108 r
  · exact originBatch109 r
  · exact originBatch110 r
  · exact originBatch111 r
  · exact originBatch112 r
  · exact originBatch113 r
  · exact originBatch114 r
  · exact originBatch115 r
  · exact originBatch116 r
  · exact originBatch117 r
  · exact originBatch118 r
  · exact originBatch119 r
  · exact originBatch120 r
  · exact originBatch121 r
  · exact originBatch122 r
  · exact originBatch123 r
  · exact originBatch124 r
  · exact originBatch125 r

theorem checkedOrigin (i : Fin 251) : checkOrigin i = true := by
  have bound := i.isLt
  let q : Fin 126 := ⟨i.val / 2, by omega⟩
  let r : Fin 2 := ⟨i.val % 2, by omega⟩
  have he : Fin.ofNat 251 (q.val * 2 + r.val) = i := by
    apply Fin.ext
    change (i.val / 2 * 2 + i.val % 2) % 251 = i.val
    omega
  exact he ▸ checkedBatch q r

end Brent.TangentData
