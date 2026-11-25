import Brent.Generated.AnnihilatorBlocks.Block2
import Mathlib.Tactic.FinCases

/- Generated dispatch for the finite covector certificate. -/
namespace Brent.QuadraticData

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem checkedBatch (q : Fin 132) (r : Fin 16) :
    checkAnnihilatorPivot (Fin.ofNat 2101 (q.val * 16 + r.val)) = true := by
  fin_cases q
  · exact annihilator0 r
  · exact annihilator1 r
  · exact annihilator2 r
  · exact annihilator3 r
  · exact annihilator4 r
  · exact annihilator5 r
  · exact annihilator6 r
  · exact annihilator7 r
  · exact annihilator8 r
  · exact annihilator9 r
  · exact annihilator10 r
  · exact annihilator11 r
  · exact annihilator12 r
  · exact annihilator13 r
  · exact annihilator14 r
  · exact annihilator15 r
  · exact annihilator16 r
  · exact annihilator17 r
  · exact annihilator18 r
  · exact annihilator19 r
  · exact annihilator20 r
  · exact annihilator21 r
  · exact annihilator22 r
  · exact annihilator23 r
  · exact annihilator24 r
  · exact annihilator25 r
  · exact annihilator26 r
  · exact annihilator27 r
  · exact annihilator28 r
  · exact annihilator29 r
  · exact annihilator30 r
  · exact annihilator31 r
  · exact annihilator32 r
  · exact annihilator33 r
  · exact annihilator34 r
  · exact annihilator35 r
  · exact annihilator36 r
  · exact annihilator37 r
  · exact annihilator38 r
  · exact annihilator39 r
  · exact annihilator40 r
  · exact annihilator41 r
  · exact annihilator42 r
  · exact annihilator43 r
  · exact annihilator44 r
  · exact annihilator45 r
  · exact annihilator46 r
  · exact annihilator47 r
  · exact annihilator48 r
  · exact annihilator49 r
  · exact annihilator50 r
  · exact annihilator51 r
  · exact annihilator52 r
  · exact annihilator53 r
  · exact annihilator54 r
  · exact annihilator55 r
  · exact annihilator56 r
  · exact annihilator57 r
  · exact annihilator58 r
  · exact annihilator59 r
  · exact annihilator60 r
  · exact annihilator61 r
  · exact annihilator62 r
  · exact annihilator63 r
  · exact annihilator64 r
  · exact annihilator65 r
  · exact annihilator66 r
  · exact annihilator67 r
  · exact annihilator68 r
  · exact annihilator69 r
  · exact annihilator70 r
  · exact annihilator71 r
  · exact annihilator72 r
  · exact annihilator73 r
  · exact annihilator74 r
  · exact annihilator75 r
  · exact annihilator76 r
  · exact annihilator77 r
  · exact annihilator78 r
  · exact annihilator79 r
  · exact annihilator80 r
  · exact annihilator81 r
  · exact annihilator82 r
  · exact annihilator83 r
  · exact annihilator84 r
  · exact annihilator85 r
  · exact annihilator86 r
  · exact annihilator87 r
  · exact annihilator88 r
  · exact annihilator89 r
  · exact annihilator90 r
  · exact annihilator91 r
  · exact annihilator92 r
  · exact annihilator93 r
  · exact annihilator94 r
  · exact annihilator95 r
  · exact annihilator96 r
  · exact annihilator97 r
  · exact annihilator98 r
  · exact annihilator99 r
  · exact annihilator100 r
  · exact annihilator101 r
  · exact annihilator102 r
  · exact annihilator103 r
  · exact annihilator104 r
  · exact annihilator105 r
  · exact annihilator106 r
  · exact annihilator107 r
  · exact annihilator108 r
  · exact annihilator109 r
  · exact annihilator110 r
  · exact annihilator111 r
  · exact annihilator112 r
  · exact annihilator113 r
  · exact annihilator114 r
  · exact annihilator115 r
  · exact annihilator116 r
  · exact annihilator117 r
  · exact annihilator118 r
  · exact annihilator119 r
  · exact annihilator120 r
  · exact annihilator121 r
  · exact annihilator122 r
  · exact annihilator123 r
  · exact annihilator124 r
  · exact annihilator125 r
  · exact annihilator126 r
  · exact annihilator127 r
  · exact annihilator128 r
  · exact annihilator129 r
  · exact annihilator130 r
  · exact annihilator131 r

theorem checkedAnnihilator (i : Fin 2101) : checkAnnihilatorPivot i = true := by
  have bound := i.isLt
  let q : Fin 132 := ⟨i.val / 16, by omega⟩
  let r : Fin 16 := ⟨i.val % 16, by omega⟩
  have he : Fin.ofNat 2101 (q.val * 16 + r.val) = i := by
    apply Fin.ext
    change (i.val / 16 * 16 + i.val % 16) % 2101 = i.val
    omega
  exact he ▸ checkedBatch q r

end Brent.QuadraticData
