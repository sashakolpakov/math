import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.HomogeneousProjection
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.Boundaries

/-! # Cech Boundaries -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.CechBoundaries.ProjectiveCech

noncomputable section

/-! Every homogeneous Čech boundary has a primitive in the same homogeneous degree. -/

open _root_.MvPolynomial DirectSum

universe u v w

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]

theorem homogeneous_moduleCech_boundary (d : ℤ) (q : ℕ) (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M)
    (hf : ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d f) (hb : f ∈ Cech.Boundaries.ProjectiveCech.moduleCechBoundarySubmodule R M q) :
    ∃ g : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M,
      ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d g ∧ ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M (q - 1) g ∧
      ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M g = f := by
  obtain ⟨g, hgc, hgd⟩ := (Cech.Boundaries.ProjectiveCech.mem_moduleCechBoundarySubmodule R M q f).mp hb
  refine ⟨Cech.HomogeneousProjection.ProjectiveCech.moduleCechHomogeneousProjection R M ℳ d g, Cech.HomogeneousProjection.ProjectiveCech.moduleCechHomogeneousProjection_mem R M ℳ d g,
    Cech.HomogeneousProjection.ProjectiveCech.moduleCechHomogeneousProjection_card R M ℳ d (q - 1) g hgc, ?_⟩
  rw [Cech.HomogeneousProjection.ProjectiveCech.moduleCechHomogeneousProjection_differential, hgd,
    Cech.HomogeneousProjection.ProjectiveCech.moduleCechHomogeneousProjection_of_homogeneous R M ℳ d f hf]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.CechBoundaries.ProjectiveCech
