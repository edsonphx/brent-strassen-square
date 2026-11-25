import Brent.Generated.FrameBlockChecks.Block2
import Mathlib.Tactic.FinCases

/- Generated dispatch for the tangent coefficient certificate. -/
namespace Brent.TangentData

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem checkedBatch (q : Fin 18) (r : Fin 3) :
    checkBlock (Fin.ofNat 54 (q.val * 3 + r.val)) = true := by
  fin_cases q
  · exact blockMatch0 r
  · exact blockMatch1 r
  · exact blockMatch2 r
  · exact blockMatch3 r
  · exact blockMatch4 r
  · exact blockMatch5 r
  · exact blockMatch6 r
  · exact blockMatch7 r
  · exact blockMatch8 r
  · exact blockMatch9 r
  · exact blockMatch10 r
  · exact blockMatch11 r
  · exact blockMatch12 r
  · exact blockMatch13 r
  · exact blockMatch14 r
  · exact blockMatch15 r
  · exact blockMatch16 r
  · exact blockMatch17 r

theorem checkedBlock (i : Fin 54) : checkBlock i = true := by
  have bound := i.isLt
  let q : Fin 18 := ⟨i.val / 3, by omega⟩
  let r : Fin 3 := ⟨i.val % 3, by omega⟩
  have he : Fin.ofNat 54 (q.val * 3 + r.val) = i := by
    apply Fin.ext
    change (i.val / 3 * 3 + i.val % 3) % 54 = i.val
    omega
  exact he ▸ checkedBatch q r

end Brent.TangentData
