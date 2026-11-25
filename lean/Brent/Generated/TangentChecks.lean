import Brent.Generated.TangentBlocks.Block8
import Mathlib.Tactic.FinCases

/- Generated dispatch for the tangent coefficient certificate. -/
namespace Brent.TangentData

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem checkedBatch (q : Fin 63) (r : Fin 4) :
    checkFrame (Fin.ofNat 251 (q.val * 4 + r.val)) = true := by
  fin_cases q
  · exact tangent0 r
  · exact tangent1 r
  · exact tangent2 r
  · exact tangent3 r
  · exact tangent4 r
  · exact tangent5 r
  · exact tangent6 r
  · exact tangent7 r
  · exact tangent8 r
  · exact tangent9 r
  · exact tangent10 r
  · exact tangent11 r
  · exact tangent12 r
  · exact tangent13 r
  · exact tangent14 r
  · exact tangent15 r
  · exact tangent16 r
  · exact tangent17 r
  · exact tangent18 r
  · exact tangent19 r
  · exact tangent20 r
  · exact tangent21 r
  · exact tangent22 r
  · exact tangent23 r
  · exact tangent24 r
  · exact tangent25 r
  · exact tangent26 r
  · exact tangent27 r
  · exact tangent28 r
  · exact tangent29 r
  · exact tangent30 r
  · exact tangent31 r
  · exact tangent32 r
  · exact tangent33 r
  · exact tangent34 r
  · exact tangent35 r
  · exact tangent36 r
  · exact tangent37 r
  · exact tangent38 r
  · exact tangent39 r
  · exact tangent40 r
  · exact tangent41 r
  · exact tangent42 r
  · exact tangent43 r
  · exact tangent44 r
  · exact tangent45 r
  · exact tangent46 r
  · exact tangent47 r
  · exact tangent48 r
  · exact tangent49 r
  · exact tangent50 r
  · exact tangent51 r
  · exact tangent52 r
  · exact tangent53 r
  · exact tangent54 r
  · exact tangent55 r
  · exact tangent56 r
  · exact tangent57 r
  · exact tangent58 r
  · exact tangent59 r
  · exact tangent60 r
  · exact tangent61 r
  · exact tangent62 r

theorem checkedFrame (i : Fin 251) : checkFrame i = true := by
  have bound := i.isLt
  let q : Fin 63 := ⟨i.val / 4, by omega⟩
  let r : Fin 4 := ⟨i.val % 4, by omega⟩
  have he : Fin.ofNat 251 (q.val * 4 + r.val) = i := by
    apply Fin.ext
    change (i.val / 4 * 4 + i.val % 4) % 251 = i.val
    omega
  exact he ▸ checkedBatch q r

end Brent.TangentData
