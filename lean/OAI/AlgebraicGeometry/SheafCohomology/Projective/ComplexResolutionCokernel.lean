import OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexMinimalResolution
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CokernelSyzygySequence
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoherentQuotientFiniteType

/-! # Complex Resolution Cokernel -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexResolutionCokernel

noncomputable section

/-! Actual coherent cokernels and the short exact sequences of the twist-sheaf resolution. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
namespace ComplexResolution
variable {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra ComplexMinimalResolution.ComplexResolution.complexResolutionField

def cokernelSheaf (j : σ) (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤))
    (hD : GradedNonnegativeSyzygy.HasNonnegativeGrading D) : (Proj (MvPolynomial.homogeneousSubmodule σ ℂ)).Modules :=
  cokernel (ComplexMinimalResolution.ComplexResolution.differential j D hD 0)

theorem cokernelSheaf_quasicoherent (j : σ) (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤))
    (hD : GradedNonnegativeSyzygy.HasNonnegativeGrading D) : (cokernelSheaf j D hD).IsQuasicoherent := by
  have : (ComplexMinimalResolution.ComplexResolution.term j D 0).IsQuasicoherent :=
    TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_quasicoherent (R := ℂ) j (GradedMinimalFiniteCover.augmentationFinWeight D)
  have : (ComplexMinimalResolution.ComplexResolution.term j D 1).IsQuasicoherent :=
    TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_quasicoherent (R := ℂ) j
      (GradedMinimalFiniteCover.augmentationFinWeight (GradedMinimalSyzygy.minimalGradedSyzygy D))
  exact Quasicoherent.Scheme.Modules.isQuasicoherent_cokernel (ComplexMinimalResolution.ComplexResolution.differential j D hD 0)

theorem cokernelSheaf_finiteType (j : σ) (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤))
    (hD : GradedNonnegativeSyzygy.HasNonnegativeGrading D) : (cokernelSheaf j D hD).IsFiniteType := by
  have : (ComplexMinimalResolution.ComplexResolution.term j D 0).IsQuasicoherent :=
    TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_quasicoherent (R := ℂ) j (GradedMinimalFiniteCover.augmentationFinWeight D)
  have : (ComplexMinimalResolution.ComplexResolution.term j D 0).IsFiniteType :=
    TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_finiteType (R := ℂ) j (GradedMinimalFiniteCover.augmentationFinWeight D)
  have : (ComplexMinimalResolution.ComplexResolution.term j D 1).IsQuasicoherent :=
    TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_quasicoherent (R := ℂ) j
      (GradedMinimalFiniteCover.augmentationFinWeight (GradedMinimalSyzygy.minimalGradedSyzygy D))
  exact CoherentQuotientFiniteType.Scheme.Modules.isFiniteType_cokernel (ComplexMinimalResolution.ComplexResolution.differential j D hD 0)

def syzygyShortComplex (j : σ) (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤))
    (hD : GradedNonnegativeSyzygy.HasNonnegativeGrading D) : ShortComplex (Proj (MvPolynomial.homogeneousSubmodule σ ℂ)).Modules :=
  CokernelSyzygySequence.cokernelSyzygyShortComplex (ComplexMinimalResolution.ComplexResolution.differential j D hD 1) (ComplexMinimalResolution.ComplexResolution.differential j D hD 0)
    (ComplexMinimalResolution.ComplexResolution.differential_comp j D hD 0)

theorem syzygyShortComplex_shortExact (j : σ) (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤))
    (hD : GradedNonnegativeSyzygy.HasNonnegativeGrading D) : (syzygyShortComplex j D hD).ShortExact :=
  CokernelSyzygySequence.cokernelSyzygyShortComplex_shortExact _ _ _ (ComplexMinimalResolution.ComplexResolution.differential_exact j D hD 0)

end ComplexResolution

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexResolutionCokernel
