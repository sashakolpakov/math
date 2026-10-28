import OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexMinimalResolution
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPolynomialMono

/-! # Complex Minimal Resolution Finite -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexMinimalResolutionFinite

noncomputable section

/-! Coherent finite free terms and the injective final map of the actual sheaf resolution. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
namespace ComplexResolution
variable {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra ComplexMinimalResolution.ComplexResolution.complexResolutionField

omit [LinearOrder σ] in
theorem term_quasicoherent (j : σ) (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤)) (n : ℕ) :
    (ComplexMinimalResolution.ComplexResolution.term j D n).IsQuasicoherent := by
  induction n generalizing D with
  | zero => exact TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_quasicoherent (R := ℂ) j (GradedMinimalFiniteCover.augmentationFinWeight D)
  | succ n ih => exact ih (GradedMinimalSyzygy.minimalGradedSyzygy D)

omit [LinearOrder σ] in
theorem term_finiteType (j : σ) (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤)) (n : ℕ) :
    (ComplexMinimalResolution.ComplexResolution.term j D n).IsFiniteType := by
  induction n generalizing D with
  | zero => exact TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_finiteType (R := ℂ) j (GradedMinimalFiniteCover.augmentationFinWeight D)
  | succ n ih => exact ih (GradedMinimalSyzygy.minimalGradedSyzygy D)

omit [LinearOrder σ] in
theorem term_eq_iterated (j : σ) (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤)) (n : ℕ) :
    ComplexMinimalResolution.ComplexResolution.term j D n = ComplexMinimalResolution.ComplexResolution.freeSheaf j (GradedMinimalSyzygy.iteratedMinimalGradedSyzygy D n) := by
  induction n generalizing D with
  | zero => rfl
  | succ n ih => exact ih (GradedMinimalSyzygy.minimalGradedSyzygy D)

theorem differential_mono_of_projective_syzygy
    (j : σ) (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤))
    (hD : GradedNonnegativeSyzygy.HasNonnegativeGrading D) (n : ℕ)
    (hp : Projective (GradedSyzygyDimension.gradedModuleObject (GradedMinimalSyzygy.iteratedMinimalGradedSyzygy D (n + 1)))) :
    Mono (ComplexMinimalResolution.ComplexResolution.differential j D hD n) := by
  induction n generalizing D with
  | zero =>
      have : Projective (GradedSyzygyDimension.gradedModuleObject (GradedMinimalSyzygy.minimalGradedSyzygy D)) := hp
      exact GradedPolynomialMono.MvPolynomial.coordinateGradedPolynomialSheafMap_mono (R := ℂ) j
        (GradedMinimalFiniteCover.augmentationFinWeight D) (GradedMinimalFiniteCover.augmentationFinWeight (GradedMinimalSyzygy.minimalGradedSyzygy D))
        (GradedMinimalResolutionStep.minimalGradedResolutionStep D) (GradedMinimalResolutionStep.minimalGradedResolutionStep_homogeneous D hD)
        (GradedMinimalResolutionStep.minimalGradedResolutionStep_injective_of_projective_syzygy D)
  | succ n ih => exact ih (GradedMinimalSyzygy.minimalGradedSyzygy D) (GradedNonnegativeSyzygy.minimalGradedSyzygy_nonnegative D hD) hp

theorem last_differential_mono {r : ℕ} (j : Fin (r + 1))
    (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule (Fin (r + 1)) Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤))
    (hD : GradedNonnegativeSyzygy.HasNonnegativeGrading D) : Mono (ComplexMinimalResolution.ComplexResolution.differential j D hD r) :=
  differential_mono_of_projective_syzygy j D hD r (GradedMinimalSyzygy.iteratedMinimalGradedSyzygy_projective (r + 1) D)

end ComplexResolution

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexMinimalResolutionFinite
