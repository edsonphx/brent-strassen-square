import Brent.Generated.AugmentedBlocks.Block23
import Mathlib.Tactic.FinCases

/- Generated dispatch for the augmented rank trace. -/
namespace Brent.AugmentedTrace

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem augStepsBatch (q : Fin 92) (r : Fin 32) :
    checkMixedStep (Fin.ofNat 2916 (q.val * 32 + r.val)) = true := by
  fin_cases q
  · exact augSteps0 r
  · exact augSteps1 r
  · exact augSteps2 r
  · exact augSteps3 r
  · exact augSteps4 r
  · exact augSteps5 r
  · exact augSteps6 r
  · exact augSteps7 r
  · exact augSteps8 r
  · exact augSteps9 r
  · exact augSteps10 r
  · exact augSteps11 r
  · exact augSteps12 r
  · exact augSteps13 r
  · exact augSteps14 r
  · exact augSteps15 r
  · exact augSteps16 r
  · exact augSteps17 r
  · exact augSteps18 r
  · exact augSteps19 r
  · exact augSteps20 r
  · exact augSteps21 r
  · exact augSteps22 r
  · exact augSteps23 r
  · exact augSteps24 r
  · exact augSteps25 r
  · exact augSteps26 r
  · exact augSteps27 r
  · exact augSteps28 r
  · exact augSteps29 r
  · exact augSteps30 r
  · exact augSteps31 r
  · exact augSteps32 r
  · exact augSteps33 r
  · exact augSteps34 r
  · exact augSteps35 r
  · exact augSteps36 r
  · exact augSteps37 r
  · exact augSteps38 r
  · exact augSteps39 r
  · exact augSteps40 r
  · exact augSteps41 r
  · exact augSteps42 r
  · exact augSteps43 r
  · exact augSteps44 r
  · exact augSteps45 r
  · exact augSteps46 r
  · exact augSteps47 r
  · exact augSteps48 r
  · exact augSteps49 r
  · exact augSteps50 r
  · exact augSteps51 r
  · exact augSteps52 r
  · exact augSteps53 r
  · exact augSteps54 r
  · exact augSteps55 r
  · exact augSteps56 r
  · exact augSteps57 r
  · exact augSteps58 r
  · exact augSteps59 r
  · exact augSteps60 r
  · exact augSteps61 r
  · exact augSteps62 r
  · exact augSteps63 r
  · exact augSteps64 r
  · exact augSteps65 r
  · exact augSteps66 r
  · exact augSteps67 r
  · exact augSteps68 r
  · exact augSteps69 r
  · exact augSteps70 r
  · exact augSteps71 r
  · exact augSteps72 r
  · exact augSteps73 r
  · exact augSteps74 r
  · exact augSteps75 r
  · exact augSteps76 r
  · exact augSteps77 r
  · exact augSteps78 r
  · exact augSteps79 r
  · exact augSteps80 r
  · exact augSteps81 r
  · exact augSteps82 r
  · exact augSteps83 r
  · exact augSteps84 r
  · exact augSteps85 r
  · exact augSteps86 r
  · exact augSteps87 r
  · exact augSteps88 r
  · exact augSteps89 r
  · exact augSteps90 r
  · exact augSteps91 r

theorem checkedSteps (i : Fin 2916) : checkMixedStep i = true := by
  have bound := i.isLt
  let q : Fin 92 := ⟨i.val / 32, by omega⟩
  let r : Fin 32 := ⟨i.val % 32, by omega⟩
  have he : Fin.ofNat 2916 (q.val * 32 + r.val) = i := by
    apply Fin.ext
    change (i.val / 32 * 32 + i.val % 32) % 2916 = i.val
    omega
  exact he ▸ augStepsBatch q r

private theorem augPivotsBatch (q : Fin 86) (r : Fin 32) :
    checkPivotAt (Fin.ofNat 2749 (q.val * 32 + r.val)) = true := by
  fin_cases q
  · exact augPivots0 r
  · exact augPivots1 r
  · exact augPivots2 r
  · exact augPivots3 r
  · exact augPivots4 r
  · exact augPivots5 r
  · exact augPivots6 r
  · exact augPivots7 r
  · exact augPivots8 r
  · exact augPivots9 r
  · exact augPivots10 r
  · exact augPivots11 r
  · exact augPivots12 r
  · exact augPivots13 r
  · exact augPivots14 r
  · exact augPivots15 r
  · exact augPivots16 r
  · exact augPivots17 r
  · exact augPivots18 r
  · exact augPivots19 r
  · exact augPivots20 r
  · exact augPivots21 r
  · exact augPivots22 r
  · exact augPivots23 r
  · exact augPivots24 r
  · exact augPivots25 r
  · exact augPivots26 r
  · exact augPivots27 r
  · exact augPivots28 r
  · exact augPivots29 r
  · exact augPivots30 r
  · exact augPivots31 r
  · exact augPivots32 r
  · exact augPivots33 r
  · exact augPivots34 r
  · exact augPivots35 r
  · exact augPivots36 r
  · exact augPivots37 r
  · exact augPivots38 r
  · exact augPivots39 r
  · exact augPivots40 r
  · exact augPivots41 r
  · exact augPivots42 r
  · exact augPivots43 r
  · exact augPivots44 r
  · exact augPivots45 r
  · exact augPivots46 r
  · exact augPivots47 r
  · exact augPivots48 r
  · exact augPivots49 r
  · exact augPivots50 r
  · exact augPivots51 r
  · exact augPivots52 r
  · exact augPivots53 r
  · exact augPivots54 r
  · exact augPivots55 r
  · exact augPivots56 r
  · exact augPivots57 r
  · exact augPivots58 r
  · exact augPivots59 r
  · exact augPivots60 r
  · exact augPivots61 r
  · exact augPivots62 r
  · exact augPivots63 r
  · exact augPivots64 r
  · exact augPivots65 r
  · exact augPivots66 r
  · exact augPivots67 r
  · exact augPivots68 r
  · exact augPivots69 r
  · exact augPivots70 r
  · exact augPivots71 r
  · exact augPivots72 r
  · exact augPivots73 r
  · exact augPivots74 r
  · exact augPivots75 r
  · exact augPivots76 r
  · exact augPivots77 r
  · exact augPivots78 r
  · exact augPivots79 r
  · exact augPivots80 r
  · exact augPivots81 r
  · exact augPivots82 r
  · exact augPivots83 r
  · exact augPivots84 r
  · exact augPivots85 r

theorem checkedPivots (i : Fin 2749) : checkPivotAt i = true := by
  have bound := i.isLt
  let q : Fin 86 := ⟨i.val / 32, by omega⟩
  let r : Fin 32 := ⟨i.val % 32, by omega⟩
  have he : Fin.ofNat 2749 (q.val * 32 + r.val) = i := by
    apply Fin.ext
    change (i.val / 32 * 32 + i.val % 32) % 2749 = i.val
    omega
  exact he ▸ augPivotsBatch q r

private theorem augCoverBatch (q : Fin 165) (r : Fin 32) :
    checkCoverAt (Fin.ofNat 5268 (q.val * 32 + r.val)) = true := by
  fin_cases q
  · exact augCover0 r
  · exact augCover1 r
  · exact augCover2 r
  · exact augCover3 r
  · exact augCover4 r
  · exact augCover5 r
  · exact augCover6 r
  · exact augCover7 r
  · exact augCover8 r
  · exact augCover9 r
  · exact augCover10 r
  · exact augCover11 r
  · exact augCover12 r
  · exact augCover13 r
  · exact augCover14 r
  · exact augCover15 r
  · exact augCover16 r
  · exact augCover17 r
  · exact augCover18 r
  · exact augCover19 r
  · exact augCover20 r
  · exact augCover21 r
  · exact augCover22 r
  · exact augCover23 r
  · exact augCover24 r
  · exact augCover25 r
  · exact augCover26 r
  · exact augCover27 r
  · exact augCover28 r
  · exact augCover29 r
  · exact augCover30 r
  · exact augCover31 r
  · exact augCover32 r
  · exact augCover33 r
  · exact augCover34 r
  · exact augCover35 r
  · exact augCover36 r
  · exact augCover37 r
  · exact augCover38 r
  · exact augCover39 r
  · exact augCover40 r
  · exact augCover41 r
  · exact augCover42 r
  · exact augCover43 r
  · exact augCover44 r
  · exact augCover45 r
  · exact augCover46 r
  · exact augCover47 r
  · exact augCover48 r
  · exact augCover49 r
  · exact augCover50 r
  · exact augCover51 r
  · exact augCover52 r
  · exact augCover53 r
  · exact augCover54 r
  · exact augCover55 r
  · exact augCover56 r
  · exact augCover57 r
  · exact augCover58 r
  · exact augCover59 r
  · exact augCover60 r
  · exact augCover61 r
  · exact augCover62 r
  · exact augCover63 r
  · exact augCover64 r
  · exact augCover65 r
  · exact augCover66 r
  · exact augCover67 r
  · exact augCover68 r
  · exact augCover69 r
  · exact augCover70 r
  · exact augCover71 r
  · exact augCover72 r
  · exact augCover73 r
  · exact augCover74 r
  · exact augCover75 r
  · exact augCover76 r
  · exact augCover77 r
  · exact augCover78 r
  · exact augCover79 r
  · exact augCover80 r
  · exact augCover81 r
  · exact augCover82 r
  · exact augCover83 r
  · exact augCover84 r
  · exact augCover85 r
  · exact augCover86 r
  · exact augCover87 r
  · exact augCover88 r
  · exact augCover89 r
  · exact augCover90 r
  · exact augCover91 r
  · exact augCover92 r
  · exact augCover93 r
  · exact augCover94 r
  · exact augCover95 r
  · exact augCover96 r
  · exact augCover97 r
  · exact augCover98 r
  · exact augCover99 r
  · exact augCover100 r
  · exact augCover101 r
  · exact augCover102 r
  · exact augCover103 r
  · exact augCover104 r
  · exact augCover105 r
  · exact augCover106 r
  · exact augCover107 r
  · exact augCover108 r
  · exact augCover109 r
  · exact augCover110 r
  · exact augCover111 r
  · exact augCover112 r
  · exact augCover113 r
  · exact augCover114 r
  · exact augCover115 r
  · exact augCover116 r
  · exact augCover117 r
  · exact augCover118 r
  · exact augCover119 r
  · exact augCover120 r
  · exact augCover121 r
  · exact augCover122 r
  · exact augCover123 r
  · exact augCover124 r
  · exact augCover125 r
  · exact augCover126 r
  · exact augCover127 r
  · exact augCover128 r
  · exact augCover129 r
  · exact augCover130 r
  · exact augCover131 r
  · exact augCover132 r
  · exact augCover133 r
  · exact augCover134 r
  · exact augCover135 r
  · exact augCover136 r
  · exact augCover137 r
  · exact augCover138 r
  · exact augCover139 r
  · exact augCover140 r
  · exact augCover141 r
  · exact augCover142 r
  · exact augCover143 r
  · exact augCover144 r
  · exact augCover145 r
  · exact augCover146 r
  · exact augCover147 r
  · exact augCover148 r
  · exact augCover149 r
  · exact augCover150 r
  · exact augCover151 r
  · exact augCover152 r
  · exact augCover153 r
  · exact augCover154 r
  · exact augCover155 r
  · exact augCover156 r
  · exact augCover157 r
  · exact augCover158 r
  · exact augCover159 r
  · exact augCover160 r
  · exact augCover161 r
  · exact augCover162 r
  · exact augCover163 r
  · exact augCover164 r

theorem checkedCover (i : Fin 5268) : checkCoverAt i = true := by
  have bound := i.isLt
  let q : Fin 165 := ⟨i.val / 32, by omega⟩
  let r : Fin 32 := ⟨i.val % 32, by omega⟩
  have he : Fin.ofNat 5268 (q.val * 32 + r.val) = i := by
    apply Fin.ext
    change (i.val / 32 * 32 + i.val % 32) % 5268 = i.val
    omega
  exact he ▸ augCoverBatch q r

private theorem augOrderBatch (q : Fin 86) (r : Fin 32) :
    checkOrderAt (Fin.ofNat 2748 (q.val * 32 + r.val)) = true := by
  fin_cases q
  · exact augOrder0 r
  · exact augOrder1 r
  · exact augOrder2 r
  · exact augOrder3 r
  · exact augOrder4 r
  · exact augOrder5 r
  · exact augOrder6 r
  · exact augOrder7 r
  · exact augOrder8 r
  · exact augOrder9 r
  · exact augOrder10 r
  · exact augOrder11 r
  · exact augOrder12 r
  · exact augOrder13 r
  · exact augOrder14 r
  · exact augOrder15 r
  · exact augOrder16 r
  · exact augOrder17 r
  · exact augOrder18 r
  · exact augOrder19 r
  · exact augOrder20 r
  · exact augOrder21 r
  · exact augOrder22 r
  · exact augOrder23 r
  · exact augOrder24 r
  · exact augOrder25 r
  · exact augOrder26 r
  · exact augOrder27 r
  · exact augOrder28 r
  · exact augOrder29 r
  · exact augOrder30 r
  · exact augOrder31 r
  · exact augOrder32 r
  · exact augOrder33 r
  · exact augOrder34 r
  · exact augOrder35 r
  · exact augOrder36 r
  · exact augOrder37 r
  · exact augOrder38 r
  · exact augOrder39 r
  · exact augOrder40 r
  · exact augOrder41 r
  · exact augOrder42 r
  · exact augOrder43 r
  · exact augOrder44 r
  · exact augOrder45 r
  · exact augOrder46 r
  · exact augOrder47 r
  · exact augOrder48 r
  · exact augOrder49 r
  · exact augOrder50 r
  · exact augOrder51 r
  · exact augOrder52 r
  · exact augOrder53 r
  · exact augOrder54 r
  · exact augOrder55 r
  · exact augOrder56 r
  · exact augOrder57 r
  · exact augOrder58 r
  · exact augOrder59 r
  · exact augOrder60 r
  · exact augOrder61 r
  · exact augOrder62 r
  · exact augOrder63 r
  · exact augOrder64 r
  · exact augOrder65 r
  · exact augOrder66 r
  · exact augOrder67 r
  · exact augOrder68 r
  · exact augOrder69 r
  · exact augOrder70 r
  · exact augOrder71 r
  · exact augOrder72 r
  · exact augOrder73 r
  · exact augOrder74 r
  · exact augOrder75 r
  · exact augOrder76 r
  · exact augOrder77 r
  · exact augOrder78 r
  · exact augOrder79 r
  · exact augOrder80 r
  · exact augOrder81 r
  · exact augOrder82 r
  · exact augOrder83 r
  · exact augOrder84 r
  · exact augOrder85 r

theorem checkedOrder (i : Fin 2748) : checkOrderAt i = true := by
  have bound := i.isLt
  let q : Fin 86 := ⟨i.val / 32, by omega⟩
  let r : Fin 32 := ⟨i.val % 32, by omega⟩
  have he : Fin.ofNat 2748 (q.val * 32 + r.val) = i := by
    apply Fin.ext
    change (i.val / 32 * 32 + i.val % 32) % 2748 = i.val
    omega
  exact he ▸ augOrderBatch q r

/-- **Augmented rank.** The Jacobian columns together with the 2916 mixed quadratic
columns span a space of dimension 2749 over every field. -/
theorem augmented_rank (k : Type) [Field k] :
    Module.finrank k (Submodule.span k (Set.range (fun i =>
      SparseRow.decode (K := k) (Fin.val : Fin 4096 → Nat) (original i)))) = 2749 :=
  rank_of_checks k checkedSteps checkedPivots checkedCover checkedOrder

end Brent.AugmentedTrace
