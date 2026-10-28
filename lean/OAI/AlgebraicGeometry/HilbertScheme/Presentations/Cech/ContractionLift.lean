import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.Pushforward

/-! # Contraction Lift -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.ContractionLift.ProjectiveCech

noncomputable section

/-! A lifted pivot contraction solves a Čech cocycle after restricting to pivot charts. -/

open _root_.MvPolynomial

universe u v w

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]

theorem moduleCechPushforward_contraction_lift (j : σ)
    (f g : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M)
    (hz : ∀ s : Finset σ, j ∈ s → g s = 0)
    (hg : ∀ s : Finset σ, j ∉ s →
      Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.subset_insert j s) (g s) =
        Signs.ProjectiveCech.alternatingSign R s j • f (insert j s))
    (a : Finset σ) (ha : j ∈ a) :
    Pushforward.ProjectiveCech.moduleCechPushforward R M g a =
      ConstantModuleContraction.ProjectiveCech.constantModuleContraction R (Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M a) j (Pushforward.ProjectiveCech.moduleCechPushforward R M f a) := by
  funext s
  by_cases hs : s ⊆ a
  · rw [Pushforward.ProjectiveCech.moduleCechPushforward_of_subset R M g a s hs]
    by_cases hj : j ∈ s
    · rw [hz s hj, map_zero, ConstantModuleContraction.ProjectiveCech.constantModuleContraction, ite_eq_left hj]
    · have hsa : insert j s ⊆ a := Finset.insert_subset ha hs
      rw [ConstantModuleContraction.ProjectiveCech.constantModuleContraction, ite_eq_right hj, Pushforward.ProjectiveCech.moduleCechPushforward_of_subset R M f a (insert j s) hsa]
      calc
        _ = Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M hsa
            (Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.subset_insert j s) (g s)) :=
          (LinearMap.congr_fun (Presentations.Module.ChartCompatibility.ProjectiveCech.moduleChartRestriction_comp R M (Finset.subset_insert j s) hsa) (g s)).symm
        _ = _ := by rw [hg s hj, map_smul]
  · have hsa : ¬insert j s ⊆ a := fun h => hs ((Finset.subset_insert j s).trans h)
    simp only [Pushforward.ProjectiveCech.moduleCechPushforward, dite_eq_right hs, ConstantModuleContraction.ProjectiveCech.constantModuleContraction, dite_eq_right hsa, smul_zero, ite_self]

theorem moduleCech_contraction_lift_restrict (j : σ)
    (f g : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M)
    (hz : ∀ s : Finset σ, j ∈ s → g s = 0)
    (hg : ∀ s : Finset σ, j ∉ s →
      Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.subset_insert j s) (g s) =
        Signs.ProjectiveCech.alternatingSign R s j • f (insert j s))
    (hf : ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f = 0) (s : Finset σ) :
    Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.subset_insert j s) (ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M g s) =
      Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.subset_insert j s) (f s) := by
  let a := insert j s
  have hsa : s ⊆ a := Finset.subset_insert j s
  have hcycle : ConstantModuleContraction.ProjectiveCech.constantModuleDifferential R (Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M a) (Pushforward.ProjectiveCech.moduleCechPushforward R M f a) a = 0 := by
    rw [← Pushforward.ProjectiveCech.moduleCechPushforward_differential R M f a a (Finset.Subset.refl a)]
    rw [show ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f a = 0 from congrFun hf a, map_zero]
  have h := ConstantModuleContraction.ProjectiveCech.constantModule_contraction_identity R (Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M a) j (Pushforward.ProjectiveCech.moduleCechPushforward R M f a) s
  have hsecond : ConstantModuleContraction.ProjectiveCech.constantModuleContraction R (Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M a) j
      (ConstantModuleContraction.ProjectiveCech.constantModuleDifferential R (Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M a) (Pushforward.ProjectiveCech.moduleCechPushforward R M f a)) s = 0 := by
    change (if j ∈ s then 0 else Signs.ProjectiveCech.alternatingSign R s j •
      ConstantModuleContraction.ProjectiveCech.constantModuleDifferential R (Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M a) (Pushforward.ProjectiveCech.moduleCechPushforward R M f a) a) = 0
    rw [hcycle, smul_zero, ite_self]
  rw [hsecond, add_zero, ← moduleCechPushforward_contraction_lift R M j f g hz hg a
    (Finset.mem_insert_self j s), ← Pushforward.ProjectiveCech.moduleCechPushforward_differential R M g a s hsa,
    Pushforward.ProjectiveCech.moduleCechPushforward_of_subset R M f a s hsa] at h
  exact h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.ContractionLift.ProjectiveCech
