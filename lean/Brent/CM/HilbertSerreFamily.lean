import Brent.CM.HilbertSerre
import Mathlib.RingTheory.Length
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Exact

/-!
# Hilbert–Serre for graded families (roadmap step A, module part)

DRAFT, NOT YET COMPILED.

A *graded family* over `A` is a sequence of `A`-modules `G n` with `s` commuting maps
`X i n : G n → G (n + 1)` (multiplication by the variables of `k[X₁, …, X_s]`). It is
*Noetherian* (`GNoeth`) when every stable subfamily is generated in bounded degree. This is
what the Hilbert basis theorem gives for a finitely generated graded `k[X]`-module, and it is
discharged for `gr_m (A ⧸ J)` in `Brent.CM.HilbertSamuelPoly`.

* `orderLE_length_fam`: **Hilbert–Serre.** For a Noetherian graded family with `s` variables
  and pieces of finite length, `n ↦ length (G n)` has order `≤ s` (is eventually a polynomial
  of degree `< s`).

The proof is the classical induction on `s`: the last variable `Y` gives the exact sequence
`0 → K n → G n →Y→ G (n + 1) → C (n + 1) → 0`, the kernel `K` and cokernel `C` are Noetherian
graded families in `s − 1` variables (on them `Y` acts by `0`), and
`ΔH_G(n) = H_C(n + 1) − H_K(n)`.
-/

namespace Brent.CM

universe u

/-! ### Differences -/

theorem diffPow_sub (e : ℕ) (f g : ℕ → ℤ) (n : ℕ) :
    diffPow e (fun m => f m - g m) n = diffPow e f n - diffPow e g n := by
  induction e generalizing n with
  | zero => rfl
  | succ e ih =>
    rw [diffPow_succ, diffPow_succ, diffPow_succ]
    simp only [diff]
    rw [ih, ih]
    ring

theorem OrderLE.sub_shift {f g : ℕ → ℤ} {e : ℕ} (hf : OrderLE f e) (hg : OrderLE g e) :
    OrderLE (fun n => f (n + 1) - g n) e := by
  obtain ⟨n₁, h₁⟩ := hf
  obtain ⟨n₂, h₂⟩ := hg
  refine ⟨max n₁ n₂, fun n hn => ?_⟩
  rw [diffPow_sub, diffPow_shift e 1 f n, h₁ _ (by omega), h₂ _ (by omega), sub_zero]

theorem orderLE_succ_of_diff {f : ℕ → ℤ} {e : ℕ} (h : OrderLE (diff f) e) : OrderLE f (e + 1) := by
  obtain ⟨n₀, hn₀⟩ := h
  exact ⟨n₀, fun n hn => by rw [diffPow_succ']; exact hn₀ n hn⟩

/-! ### Graded families -/

variable {A : Type u} [CommRing A]

section Fam

variable {s : ℕ} {G : ℕ → Type u} [∀ n, AddCommGroup (G n)] [∀ n, Module A (G n)]

/-- `S` is stable under the variables. -/
def IsStableFam (X : Fin s → ∀ n, G n →ₗ[A] G (n + 1)) (S : ∀ n, Submodule A (G n)) : Prop :=
  ∀ i n, ∀ g ∈ S n, X i n g ∈ S (n + 1)

/-- Every stable subfamily is generated in bounded degree. -/
def GNoeth (X : Fin s → ∀ n, G n →ₗ[A] G (n + 1)) : Prop :=
  ∀ S : ∀ n, Submodule A (G n), IsStableFam X S →
    ∃ d, ∀ n ≥ d, S (n + 1) ≤ ⨆ i, (S n).map (X i n)

/-- The variables commute. -/
def Commutes (X : Fin s → ∀ n, G n →ₗ[A] G (n + 1)) : Prop :=
  ∀ i j n, (X i (n + 1)).comp (X j n) = (X j (n + 1)).comp (X i n)

end Fam

/-- The length of a module, as an integer (`0` if infinite). -/
noncomputable def lenZ (M : Type u) [AddCommGroup M] [Module A M] : ℤ :=
  ((Module.length A M).toNat : ℤ)

theorem iSup_fin_succ_eq {α : Type*} [CompleteLattice α] {s : ℕ} (f : Fin (s + 1) → α) :
    (⨆ i, f i) = (⨆ i : Fin s, f i.castSucc) ⊔ f (Fin.last s) := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    induction i using Fin.lastCases with
    | last => exact le_sup_right
    | cast i => exact le_sup_of_le_left (le_iSup (fun i : Fin s => f i.castSucc) i)
  · exact sup_le (iSup_le fun i => le_iSup f _) (le_iSup f _)

section Step

variable {s : ℕ} {G : ℕ → Type u} [∀ n, AddCommGroup (G n)] [∀ n, Module A (G n)]
  (X : Fin (s + 1) → ∀ n, G n →ₗ[A] G (n + 1))

/-- The last variable. -/
abbrev lastVar : ∀ n, G n →ₗ[A] G (n + 1) := X (Fin.last s)

/-- The kernel family `K n = ker (Y : G n → G (n + 1))`. -/
abbrev KerFam (n : ℕ) : Type u := LinearMap.ker (lastVar X n)

/-- The images `R 0 = 0`, `R (n + 1) = Y (G n)`. -/
def imFam : ∀ n, Submodule A (G n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (lastVar X n)

/-- The cokernel family `C n = G n ⧸ R n`. -/
abbrev CokFam (n : ℕ) : Type u := G n ⧸ imFam X n

variable {X}

theorem ker_stable (hc : Commutes X) (i : Fin s) (n : ℕ) :
    ∀ g ∈ LinearMap.ker (lastVar X n), X i.castSucc n g ∈ LinearMap.ker (lastVar X (n + 1)) := by
  intro g hg
  rw [LinearMap.mem_ker] at hg ⊢
  have h := congrArg (fun φ => φ g) (hc (Fin.last s) i.castSucc n)
  simp only [LinearMap.comp_apply] at h
  rw [h, hg, map_zero]

theorem im_stable (hc : Commutes X) (i : Fin s) (n : ℕ) :
    imFam X n ≤ (imFam X (n + 1)).comap (X i.castSucc n) := by
  cases n with
  | zero => exact bot_le
  | succ n =>
    rintro _ ⟨g, rfl⟩
    show X i.castSucc (n + 1) (lastVar X n g) ∈ LinearMap.range (lastVar X (n + 1))
    have h := congrArg (fun φ => φ g) (hc i.castSucc (Fin.last s) n)
    simp only [LinearMap.comp_apply] at h
    rw [h]
    exact LinearMap.mem_range_self _ _

variable (X)

/-- The variables on the kernel family. -/
noncomputable def kerVars (hc : Commutes X) (i : Fin s) (n : ℕ) :
    KerFam X n →ₗ[A] KerFam X (n + 1) :=
  (X i.castSucc n).restrict (ker_stable hc i n)

/-- The variables on the cokernel family. -/
noncomputable def cokVars (hc : Commutes X) (i : Fin s) (n : ℕ) :
    CokFam X n →ₗ[A] CokFam X (n + 1) :=
  Submodule.mapQ _ _ (X i.castSucc n) (im_stable hc i n)

variable {X}

theorem kerVars_commutes (hc : Commutes X) : Commutes (kerVars X hc) := by
  intro i j n
  ext g
  simp only [kerVars, LinearMap.comp_apply, LinearMap.restrict_apply]
  have h := congrArg (fun φ => φ (g : G n)) (hc i.castSucc j.castSucc n)
  simp only [LinearMap.comp_apply] at h
  exact h

theorem cokVars_commutes (hc : Commutes X) : Commutes (cokVars X hc) := by
  intro i j n
  apply Submodule.linearMap_qext
  ext g
  simp only [cokVars, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
  have h := congrArg (fun φ => φ g) (hc i.castSucc j.castSucc n)
  simp only [LinearMap.comp_apply] at h
  rw [h]

/-- Pushing a stable subfamily of the kernel family into `G` keeps it stable (the last variable
kills the kernel). -/
theorem kerVars_gnoeth (hc : Commutes X) (hN : GNoeth X) : GNoeth (kerVars X hc) := by
  intro S hS
  let T : ∀ n, Submodule A (G n) := fun n => (S n).map (LinearMap.ker (lastVar X n)).subtype
  have hT : IsStableFam X T := by
    intro i n g hg
    obtain ⟨k, hk, rfl⟩ := hg
    induction i using Fin.lastCases with
    | last =>
      have : X (Fin.last s) n (k : G n) = 0 := LinearMap.mem_ker.mp k.2
      rw [Submodule.subtype_apply, this]
      exact Submodule.zero_mem _
    | cast i =>
      exact ⟨kerVars X hc i n k, hS i n k hk, rfl⟩
  obtain ⟨d, hd⟩ := hN T hT
  refine ⟨d, fun n hn => ?_⟩
  have h := hd n hn
  rw [iSup_fin_succ_eq] at h
  have hlast : (T n).map (X (Fin.last s) n) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨g, ⟨k, -, rfl⟩, rfl⟩
    exact (Submodule.mem_bot A).mpr (LinearMap.mem_ker.mp k.2)
  rw [hlast, sup_bot_eq] at h
  intro k hk
  have hk' : (k : G (n + 1)) ∈ T (n + 1) := ⟨k, hk, rfl⟩
  have hk'' := h hk'
  have hmap : (⨆ i : Fin s, (T n).map (X i.castSucc n)) =
      (⨆ i : Fin s, (S n).map (kerVars X hc i n)).map
        (LinearMap.ker (lastVar X (n + 1))).subtype := by
    rw [Submodule.map_iSup]
    refine iSup_congr fun i => ?_
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    rfl
  rw [hmap] at hk''
  obtain ⟨k', hk', hkk⟩ := hk''
  rw [Submodule.subtype_apply] at hkk
  rw [← Subtype.ext hkk]
  exact hk'

/-- Pulling a stable subfamily of the cokernel family back to `G` keeps it stable. -/
theorem cokVars_gnoeth (hc : Commutes X) (hN : GNoeth X) : GNoeth (cokVars X hc) := by
  intro S hS
  let T : ∀ n, Submodule A (G n) := fun n => (S n).comap (imFam X n).mkQ
  have hT : IsStableFam X T := by
    intro i n g hg
    induction i using Fin.lastCases with
    | last =>
      show (imFam X (n + 1)).mkQ (X (Fin.last s) n g) ∈ S (n + 1)
      have hz : (imFam X (n + 1)).mkQ (X (Fin.last s) n g) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact LinearMap.mem_range_self (lastVar X n) g
      rw [hz]
      exact Submodule.zero_mem _
    | cast i =>
      show (imFam X (n + 1)).mkQ (X i.castSucc n g) ∈ S (n + 1)
      exact hS i n _ hg
  obtain ⟨d, hd⟩ := hN T hT
  refine ⟨d, fun n hn => ?_⟩
  have h := hd n hn
  rw [iSup_fin_succ_eq] at h
  have hS' : S (n + 1) = (T (n + 1)).map (imFam X (n + 1)).mkQ :=
    (Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective _) _).symm
  rw [hS']
  refine (Submodule.map_mono h).trans ?_
  rw [Submodule.map_sup, Submodule.map_iSup]
  refine sup_le (iSup_mono fun i => ?_) ?_
  · rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨(imFam X n).mkQ g, hg, rfl⟩
  · rintro _ ⟨_, ⟨g, -, rfl⟩, rfl⟩
    have hz : (imFam X (n + 1)).mkQ (X (Fin.last s) n g) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact LinearMap.mem_range_self (lastVar X n) g
    rw [hz]
    exact Submodule.zero_mem _

/-! ### Lengths along the exact sequence -/

theorem length_fam_eq (n : ℕ) :
    Module.length A (G n) = Module.length A (KerFam X n) +
      Module.length A (LinearMap.range (lastVar X n)) := by
  refine Module.length_eq_add_of_exact (LinearMap.ker (lastVar X n)).subtype
    (lastVar X n).rangeRestrict (Submodule.injective_subtype _)
    (LinearMap.surjective_rangeRestrict _) fun g => ?_
  constructor
  · intro hg
    refine ⟨⟨g, ?_⟩, rfl⟩
    rw [LinearMap.mem_ker]
    exact congrArg Subtype.val hg
  · rintro ⟨k, rfl⟩
    exact Subtype.ext (LinearMap.mem_ker.mp k.2)

theorem length_fam_succ_eq (n : ℕ) :
    Module.length A (G (n + 1)) = Module.length A (LinearMap.range (lastVar X n)) +
      Module.length A (CokFam X (n + 1)) :=
  Module.length_eq_add_of_exact (LinearMap.range (lastVar X n)).subtype
    (LinearMap.range (lastVar X n)).mkQ (Submodule.injective_subtype _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)

theorem diff_lenZ (hfin : ∀ n, Module.length A (G n) ≠ ⊤) (n : ℕ) :
    lenZ (A := A) (G (n + 1)) - lenZ (A := A) (G n) =
      lenZ (A := A) (CokFam X (n + 1)) - lenZ (A := A) (KerFam X n) := by
  have e1 := length_fam_eq (X := X) n
  have e2 := length_fam_succ_eq (X := X) n
  have h1 := hfin n
  have h2 := hfin (n + 1)
  rw [e1] at h1
  rw [e2] at h2
  have ha : Module.length A (KerFam X n) ≠ ⊤ := fun h => h1 (by rw [h, top_add])
  have hb : Module.length A (LinearMap.range (lastVar X n)) ≠ ⊤ :=
    fun h => h1 (by rw [h, add_top])
  have hc : Module.length A (CokFam X (n + 1)) ≠ ⊤ := fun h => h2 (by rw [h, add_top])
  unfold lenZ
  rw [e1, e2]
  lift Module.length A (KerFam X n) to ℕ using ha with a
  lift Module.length A (LinearMap.range (lastVar X n)) to ℕ using hb with b
  lift Module.length A (CokFam X (n + 1)) to ℕ using hc with c
  simp only [← Nat.cast_add, ENat.toNat_coe]
  push_cast
  ring

theorem ker_length_ne_top (hfin : ∀ n, Module.length A (G n) ≠ ⊤) (n : ℕ) :
    Module.length A (KerFam X n) ≠ ⊤ :=
  ne_top_of_le_ne_top (hfin n)
    (Module.length_le_of_injective _ (Submodule.injective_subtype (LinearMap.ker (lastVar X n))))

theorem cok_length_ne_top (hfin : ∀ n, Module.length A (G n) ≠ ⊤) (n : ℕ) :
    Module.length A (CokFam X n) ≠ ⊤ :=
  ne_top_of_le_ne_top (hfin n)
    (Module.length_le_of_surjective _ (Submodule.mkQ_surjective (imFam X n)))

end Step

/-! ### Hilbert–Serre -/

/-- **Hilbert–Serre.** For a Noetherian graded family in `s` commuting variables whose pieces
have finite length, `n ↦ length (G n)` has order `≤ s`. -/
theorem orderLE_length_fam : ∀ (s : ℕ) (G : ℕ → Type u) [∀ n, AddCommGroup (G n)]
    [∀ n, Module A (G n)] (X : Fin s → ∀ n, G n →ₗ[A] G (n + 1)), Commutes X → GNoeth X →
    (∀ n, Module.length A (G n) ≠ ⊤) → OrderLE (fun n => lenZ (A := A) (G n)) s := by
  intro s
  induction s with
  | zero =>
    intro G _ _ X _ hN _
    obtain ⟨d, hd⟩ := hN (fun _ => ⊤) (fun _ _ _ _ => Submodule.mem_top)
    refine ⟨d + 1, fun n hn => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h := hd m (by omega)
    rw [iSup_of_empty] at h
    haveI : Subsingleton (G (m + 1)) :=
      ⟨fun a b => by
        have ha := (Submodule.mem_bot A).mp (h (Submodule.mem_top (x := a)))
        have hb := (Submodule.mem_bot A).mp (h (Submodule.mem_top (x := b)))
        rw [ha, hb]⟩
    show lenZ (A := A) (G (m + 1)) = 0
    unfold lenZ
    rw [Module.length_eq_zero_iff.mpr inferInstance]
    rfl
  | succ s ih =>
    intro G _ _ X hc hN hfin
    have hK := ih (KerFam X) (kerVars X hc) (kerVars_commutes hc) (kerVars_gnoeth hc hN)
      (ker_length_ne_top hfin)
    have hC := ih (CokFam X) (cokVars X hc) (cokVars_commutes hc) (cokVars_gnoeth hc hN)
      (cok_length_ne_top hfin)
    refine orderLE_succ_of_diff ?_
    have hdiff : diff (fun n => lenZ (A := A) (G n)) =
        fun n => lenZ (A := A) (CokFam X (n + 1)) - lenZ (A := A) (KerFam X n) := by
      funext n
      exact diff_lenZ hfin n
    rw [hdiff]
    exact OrderLE.sub_shift hC hK

end Brent.CM
