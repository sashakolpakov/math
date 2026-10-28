import OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorBoundedComplex
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EventualDegreeFlatness

/-! # Tensor Augmentation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.TensorAugmentation.ProjectiveCech

noncomputable section

/-! High-degree projective Čech augmentations remain injective after arbitrary tensor base change. -/

open _root_.MvPolynomial DirectSum

universe u v w

variable {σ : Type v} [Fintype σ] [LinearOrder σ] [Nonempty σ]
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable (M : Type (max u v)) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]
  [Module.Finite (MvPolynomial σ R) M]

theorem moduleCech_eventual_lTensor_injective
    (hflat : ∀ s : Finset σ, s.Nonempty → Module.Flat R (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s 0)) :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d →
      ∀ (S : Type w) [AddCommGroup S] [Module R S],
        Function.Injective ((ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d 0).lTensor S) := by
  obtain ⟨B, hB⟩ := Graded.CechVanishing.ProjectiveCech.moduleCech_eventual_exactness_explicit (σ := σ) R M ℳ
  refine ⟨B, fun d hd S _ _ => ?_⟩
  have hflatd (s : Finset σ) (hs : s.Nonempty) : Module.Flat R (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s d) := by
    let : Module.Flat R (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s 0) := hflat s hs
    exact EventualDegreeFlatness.ProjectiveCech.moduleChartDegree_flat_of_zero R M ℳ s hs d ((Int.natCast_nonneg B).trans hd)
  apply TensorBoundedComplex.lTensor_augmentation_injective_of_bounded_exact R (Fintype.card σ)
    (fun q => ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d q) (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential R M ℳ d)
  · exact fun q => FlatAugmentation.ProjectiveCech.moduleCechTermDifferential_exact R M ℳ d q ((hB d hd).2 q)
  · exact ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential_zero R M ℳ d (Fintype.card σ + 2) (by omega)
  · exact FlatAugmentation.ProjectiveCech.moduleCechTermDifferential_injective R M ℳ d (hB d hd).1
  · intro q hq _
    exact ModuleCech.Terms.ProjectiveCech.moduleCechTerm_flat R M ℳ d q (by omega) hflatd

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.TensorAugmentation.ProjectiveCech
