import OAI.AlgebraicGeometry.HilbertScheme.Presentations.AddedCechKernel

/-! # Added Kernel Degrees -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.AddedKernelDegrees.ProjectiveCech

noncomputable section

/-! The added-chart kernel equivalence preserves homogeneous degrees and shifts face cardinality by one. -/

open _root_.MvPolynomial DirectSum

universe u v w

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable [Algebra (MvPolynomial (WithBot σ) R) (MvPolynomial σ R)]
  [IsScalarTower R (MvPolynomial (WithBot σ) R) (MvPolynomial σ R)]
variable (he : ∀ i : σ, algebraMap (MvPolynomial (WithBot σ) R) (MvPolynomial σ R) (X (i : WithBot σ)) = X i)
variable (M : Type w) [AddCommGroup M] [Module R M]
  [Module (MvPolynomial (WithBot σ) R) M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial (WithBot σ) R) M] [IsScalarTower R (MvPolynomial σ R) M]
  [IsScalarTower (MvPolynomial (WithBot σ) R) (MvPolynomial σ R) M]
variable (l : MvPolynomial σ R)
variable (hl : algebraMap (MvPolynomial (WithBot σ) R) (MvPolynomial σ R) (X ⊥) = l)

theorem addedModuleCechComponent_card (q : ℕ) (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := WithBot σ) R M)
    (hf : ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M (q + 1) f) :
    ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R (Presentations.Module.Fractions.GradedModules.AwayModule l M) q (AddedCechKernel.ProjectiveCech.addedModuleCechComponent R he M l hl f) := by
  intro s hs
  change AddedCoordinateCharts.ProjectiveCech.addedModuleChartEquiv R he l hl M s (f (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s)) = 0
  rw [hf _ (by rw [AddedCoordinateFinsets.ProjectiveCech.card_addedCoordinateFace]; omega), map_zero]

theorem addedModuleCechComponent_card_iff (q : ℕ) (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := WithBot σ) R M)
    (hker : ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap R Function.Embedding.coeWithBot he M f = 0) :
    ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R (Presentations.Module.Fractions.GradedModules.AwayModule l M) q (AddedCechKernel.ProjectiveCech.addedModuleCechComponent R he M l hl f) ↔
      ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M (q + 1) f := by
  constructor
  · intro h s hs
    by_cases hbot : ⊥ ∈ s
    · obtain ⟨t, rfl⟩ : ∃ t : Finset σ, AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace t = s :=
        ⟨AddedCoordinateFinsets.ProjectiveCech.removeAddedCoordinate s, AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace_representation s hbot⟩
      apply (AddedCoordinateCharts.ProjectiveCech.addedModuleChartEquiv R he l hl M t).injective
      rw [map_zero]
      exact h t (by rw [AddedCoordinateFinsets.ProjectiveCech.card_addedCoordinateFace] at hs; omega)
    · exact (AddedCechKernel.ProjectiveCech.retainedModuleCechMap_eq_zero_iff R he M f).mp hker s hbot
  · exact addedModuleCechComponent_card R he M l hl q f

theorem retainedModuleCechMap_kernel_card_zero (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := WithBot σ) R M)
    (hker : ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap R Function.Embedding.coeWithBot he M f = 0)
    (hf : ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M 0 f) : f = 0 := by
  funext s
  by_cases hbot : ⊥ ∈ s
  · exact hf s (Finset.card_ne_zero.mpr ⟨⊥, hbot⟩)
  · exact (AddedCechKernel.ProjectiveCech.retainedModuleCechMap_eq_zero_iff R he M f).mp hker s hbot

variable (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]
variable (hlhom : l ∈ WeightedFreeModules.GradedModules.polynomialIntegerGrading R 1)

include hlhom in
theorem addedModuleCechComponent_homogeneous (d : ℤ) (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := WithBot σ) R M)
    (hf : ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d f) :
    ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R (Presentations.Module.Fractions.GradedModules.AwayModule l M) (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ l 1) d
      (AddedCechKernel.ProjectiveCech.addedModuleCechComponent R he M l hl f) := by
  intro s
  rw [← AddedCoordinateCharts.ProjectiveCech.addedModuleChartEquiv_degree R he l hl M ℳ hlhom s d]
  exact Submodule.mem_map.mpr ⟨f (AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace s), hf _, rfl⟩

include hlhom in
theorem addedModuleCechComponent_homogeneous_iff (d : ℤ) (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := WithBot σ) R M)
    (hker : ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap R Function.Embedding.coeWithBot he M f = 0) :
    ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R (Presentations.Module.Fractions.GradedModules.AwayModule l M) (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ l 1) d
      (AddedCechKernel.ProjectiveCech.addedModuleCechComponent R he M l hl f) ↔ ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d f := by
  constructor
  · intro h s
    by_cases hbot : ⊥ ∈ s
    · obtain ⟨t, rfl⟩ : ∃ t : Finset σ, AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace t = s :=
        ⟨AddedCoordinateFinsets.ProjectiveCech.removeAddedCoordinate s, AddedCoordinateFinsets.ProjectiveCech.addedCoordinateFace_representation s hbot⟩
      have hm := h t
      rw [← AddedCoordinateCharts.ProjectiveCech.addedModuleChartEquiv_degree R he l hl M ℳ hlhom t d] at hm
      obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.mp hm
      exact ((AddedCoordinateCharts.ProjectiveCech.addedModuleChartEquiv R he l hl M t).injective hxe) ▸ hx
    · rw [(AddedCechKernel.ProjectiveCech.retainedModuleCechMap_eq_zero_iff R he M f).mp hker s hbot]
      exact Submodule.zero_mem _
  · exact addedModuleCechComponent_homogeneous R he M l hl ℳ hlhom d f

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.AddedKernelDegrees.ProjectiveCech
