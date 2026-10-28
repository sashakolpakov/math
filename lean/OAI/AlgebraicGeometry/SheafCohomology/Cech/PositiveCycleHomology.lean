/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/TotalComplexUpNatHorizontalEdgeHOne.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.QuasiIso

/-! # Positive Cycle Homology -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u
variable (n : ℕ)

theorem up_prev_succ : (ComplexShape.up ℕ).prev (n + 1) = n :=
  (ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel n (n + 1) by rfl)

theorem up_next_succ : (ComplexShape.up ℕ).next (n + 1) = n + 2 :=
  (ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel (n + 1) (n + 2) by rfl)

noncomputable def abCyclesMk
    (L : CochainComplex AddCommGrpCat.{u} ℕ) (x : L.X (n + 1))
    (hx : L.d (n + 1) (n + 2) x = 0) : L.cycles (n + 1) :=
  (L.cyclesIsoSc' n (n + 1) (n + 2) (up_prev_succ n) (up_next_succ n)).inv
    ((L.sc' n (n + 1) (n + 2)).abCyclesIso.inv ⟨x, hx⟩)

@[simp]
theorem i_abCyclesMk
    (L : CochainComplex AddCommGrpCat.{u} ℕ) (x : L.X (n + 1))
    (hx : L.d (n + 1) (n + 2) x = 0) :
    L.iCycles (n + 1) (abCyclesMk n L x hx) = x := by
  have h₁ := congrArg
    (fun g ↦ g ((L.sc' n (n + 1) (n + 2)).abCyclesIso.inv ⟨x, hx⟩))
    (L.cyclesIsoSc'_inv_iCycles n (n + 1) (n + 2) (up_prev_succ n) (up_next_succ n))
  simp only [ConcreteCategory.comp_apply] at h₁
  have h₂ := (L.sc' n (n + 1) (n + 2)).abCyclesIso_inv_apply_iCycles ⟨x, hx⟩
  exact h₁.trans h₂

theorem cyclesMap_cyclesMk
    {L M : CochainComplex AddCommGrpCat.{u} ℕ} (f : L ⟶ M)
    (x : L.X (n + 1)) (hx : L.d (n + 1) (n + 2) x = 0)
    (hfx : M.d (n + 1) (n + 2) (f.f (n + 1) x) = 0) :
    HomologicalComplex.cyclesMap f (n + 1) (abCyclesMk n L x hx) =
      abCyclesMk n M (f.f (n + 1) x) hfx := by
  apply (AddCommGrpCat.mono_iff_injective (M.iCycles (n + 1))).mp inferInstance
  have h := congrArg (fun g ↦ g (abCyclesMk n L x hx))
    (HomologicalComplex.cyclesMap_i f (n + 1))
  simpa only [ConcreteCategory.comp_apply, i_abCyclesMk n] using h

theorem homologyπ_cyclesMk_eq_of_sub_eq_boundary
    (L : CochainComplex AddCommGrpCat.{u} ℕ)
    (x y : L.X (n + 1)) (hx : L.d (n + 1) (n + 2) x = 0) (hy : L.d (n + 1) (n + 2) y = 0)
    (b : L.X n) (hxy : x - y = L.d n (n + 1) b) :
    L.homologyπ (n + 1) (abCyclesMk n L x hx) =
      L.homologyπ (n + 1) (abCyclesMk n L y hy) := by
  let S := L.sc' n (n + 1) (n + 2)
  let cIso := L.cyclesIsoSc' n (n + 1) (n + 2) (up_prev_succ n) (up_next_succ n)
  let hIso := L.homologyIsoSc' n (n + 1) (n + 2) (up_prev_succ n) (up_next_succ n)
  let qIso := hIso ≪≫ S.abHomologyIso
  apply (AddCommGrpCat.mono_iff_injective qIso.hom).mp inferInstance
  have class_eq (z : L.X (n + 1)) (hz : L.d (n + 1) (n + 2) z = 0) :
      qIso.hom (L.homologyπ (n + 1) (abCyclesMk n L z hz)) =
        QuotientAddGroup.mk' (AddMonoidHom.range S.abToCycles)
          (⟨z, hz⟩ : AddMonoidHom.ker S.g.hom) := by
    have h₁ := congrArg (fun g ↦ g (abCyclesMk n L z hz))
      (L.π_homologyIsoSc'_hom n (n + 1) (n + 2) (up_prev_succ n) (up_next_succ n))
    have h₂ := congrArg
      (fun g ↦ g (cIso.hom (abCyclesMk n L z hz)))
      S.abLeftHomologyData.homologyπ_comp_homologyIso_hom
    simp only [ConcreteCategory.comp_apply] at h₁ h₂
    calc
      _ = S.abHomologyIso.hom
          (hIso.hom (L.homologyπ (n + 1) (abCyclesMk n L z hz))) := rfl
      _ = S.abHomologyIso.hom
          (S.homologyπ (cIso.hom (abCyclesMk n L z hz))) := by
        rw [h₁]
      _ = QuotientAddGroup.mk' (AddMonoidHom.range S.abToCycles)
          (S.abCyclesIso.hom (cIso.hom (abCyclesMk n L z hz))) := by
        change S.abLeftHomologyData.homologyIso.hom
            (S.homologyπ (cIso.hom (abCyclesMk n L z hz))) =
          S.abLeftHomologyData.π
            (S.abLeftHomologyData.cyclesIso.hom
              (cIso.hom (abCyclesMk n L z hz)))
        exact h₂
      _ = QuotientAddGroup.mk' (AddMonoidHom.range S.abToCycles)
          (⟨z, hz⟩ : AddMonoidHom.ker S.g.hom) := by
        change QuotientAddGroup.mk' (AddMonoidHom.range S.abToCycles)
            (S.abCyclesIso.hom
              (cIso.hom (cIso.inv (S.abCyclesIso.inv ⟨z, hz⟩)))) = _
        rw [cIso.inv_hom_id_apply, S.abCyclesIso.inv_hom_id_apply]
  rw [class_eq x hx, class_eq y hy]
  dsimp only [S]
  refine (QuotientAddGroup.eq_iff_sub_mem).2 ?_
  rw [AddMonoidHom.mem_range]
  refine ⟨b, ?_⟩
  apply Subtype.ext
  change L.d n (n + 1) b = x - y
  exact hxy.symm

theorem exists_boundary_of_homologyπ_abCyclesMk_eq_zero
    (L : CochainComplex AddCommGrpCat.{u} ℕ)
    (x : L.X (n + 1)) (hx : L.d (n + 1) (n + 2) x = 0)
    (hzero : L.homologyπ (n + 1) (abCyclesMk n L x hx) = 0) :
    ∃ b : L.X n, L.d n (n + 1) b = x := by
  let S := L.sc' n (n + 1) (n + 2)
  let cIso := L.cyclesIsoSc' n (n + 1) (n + 2) (up_prev_succ n) (up_next_succ n)
  let hIso := L.homologyIsoSc' n (n + 1) (n + 2) (up_prev_succ n) (up_next_succ n)
  let qIso := hIso ≪≫ S.abHomologyIso
  have class_eq :
      qIso.hom (L.homologyπ (n + 1) (abCyclesMk n L x hx)) =
        QuotientAddGroup.mk' (AddMonoidHom.range S.abToCycles)
          (⟨x, hx⟩ : AddMonoidHom.ker S.g.hom) := by
    have h₁ := congrArg (fun g ↦ g (abCyclesMk n L x hx))
      (L.π_homologyIsoSc'_hom n (n + 1) (n + 2) (up_prev_succ n) (up_next_succ n))
    have h₂ := congrArg
      (fun g ↦ g (cIso.hom (abCyclesMk n L x hx)))
      S.abLeftHomologyData.homologyπ_comp_homologyIso_hom
    simp only [ConcreteCategory.comp_apply] at h₁ h₂
    calc
      _ = S.abHomologyIso.hom
          (hIso.hom (L.homologyπ (n + 1) (abCyclesMk n L x hx))) := rfl
      _ = S.abHomologyIso.hom
          (S.homologyπ (cIso.hom (abCyclesMk n L x hx))) := by rw [h₁]
      _ = QuotientAddGroup.mk' (AddMonoidHom.range S.abToCycles)
          (S.abCyclesIso.hom (cIso.hom (abCyclesMk n L x hx))) := by
        change S.abLeftHomologyData.homologyIso.hom
            (S.homologyπ (cIso.hom (abCyclesMk n L x hx))) =
          S.abLeftHomologyData.π
            (S.abLeftHomologyData.cyclesIso.hom
              (cIso.hom (abCyclesMk n L x hx)))
        exact h₂
      _ = QuotientAddGroup.mk' (AddMonoidHom.range S.abToCycles)
          (⟨x, hx⟩ : AddMonoidHom.ker S.g.hom) := by
        change QuotientAddGroup.mk' (AddMonoidHom.range S.abToCycles)
            (S.abCyclesIso.hom
              (cIso.hom (cIso.inv (S.abCyclesIso.inv ⟨x, hx⟩)))) = _
        rw [cIso.inv_hom_id_apply, S.abCyclesIso.inv_hom_id_apply]
  have hclass :
      QuotientAddGroup.mk' (AddMonoidHom.range S.abToCycles)
        (⟨x, hx⟩ : AddMonoidHom.ker S.g.hom) = 0 := by
    rw [← class_eq, hzero, map_zero]
  have hmem := (QuotientAddGroup.eq_zero_iff
    (⟨x, hx⟩ : AddMonoidHom.ker S.g.hom)).mp hclass
  rw [AddMonoidHom.mem_range] at hmem
  obtain ⟨b, hb⟩ := hmem
  refine ⟨b, ?_⟩
  have hb' := congrArg Subtype.val hb
  exact hb'

theorem homologyMap_abCyclesMk
    {L M : CochainComplex AddCommGrpCat.{u} ℕ} (f : L ⟶ M)
    (x : L.X (n + 1)) (hx : L.d (n + 1) (n + 2) x = 0)
    (hfx : M.d (n + 1) (n + 2) (f.f (n + 1) x) = 0) :
    HomologicalComplex.homologyMap f (n + 1)
        (L.homologyπ (n + 1) (abCyclesMk n L x hx)) =
      M.homologyπ (n + 1) (abCyclesMk n M (f.f (n + 1) x) hfx) := by
  have h := congrArg (fun g ↦ g (abCyclesMk n L x hx))
    (HomologicalComplex.homologyπ_naturality (φ := f) (i := n + 1))
  simp only [ConcreteCategory.comp_apply, cyclesMap_cyclesMk n f x hx hfx] at h
  exact h

end

end OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology
