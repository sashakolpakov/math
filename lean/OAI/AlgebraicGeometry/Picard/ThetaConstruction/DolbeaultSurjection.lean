import OAI.AlgebraicGeometry.Picard.ThetaConstruction.DolbeaultInjection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomogeneousCovector

/-! # Dolbeault Surjection -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! The constructed complex-linear translation map fills the actual
native Dolbeault space. Both directions embed in the original finite
dimensional tangent space, so injectivity forces surjectivity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomogeneousCovector

variable {dim : ℕ} {E : DefinitionsIntegral.IntegralMatrix dim} {T : DefinitionsIntegral.MarkedPolarizedTorus dim E}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel T)

local instance PeriodModel.Geometric.AlgebraicPeriodModel.dolbeaultSurjection_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.dolbeaultSurjection_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

def PeriodModel.Geometric.AlgebraicPeriodModel.nativePeriodHermitian : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian →ₗ⋆[ℂ] HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian →ₗ[ℂ] ℂ :=
  (T.riemannForm.comp M.periodDifferential.symm.toLinearMap).compl₂ M.periodDifferential.symm.toLinearMap

theorem PeriodModel.Geometric.AlgebraicPeriodModel.nativePeriodHermitian_symm (a b : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) :
    M.nativePeriodHermitian b a = star (M.nativePeriodHermitian a b) :=
  T.hermitian (M.periodDifferential.symm a) (M.periodDifferential.symm b)

theorem PeriodModel.Geometric.AlgebraicPeriodModel.nativePeriodHermitian_pos (a : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ha : a ≠ 0) :
    0 < (M.nativePeriodHermitian a a).re :=
  T.positive (M.periodDifferential.symm a)
    (fun h => ha (M.periodDifferential.symm.injective (h.trans M.periodDifferential.symm.map_zero.symm)))

def PeriodModel.Geometric.AlgebraicPeriodModel.periodDolbeaultCoordinate :
    RepresentationTheory.Theta.Geometric.DolbeaultQuotient.DolbeaultOneSpace (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) →ₗ[ℂ] DefinitionsIntegral.Tangent dim :=
  M.periodDifferential.symm.toLinearMap.comp
    (AbelianModuli.ReferenceFamily.Intrinsic.HomogeneousCovector.nativeDolbeaultHermitianCoordinate M.abelian M.nativePeriodHermitian
      M.nativePeriodHermitian_symm M.nativePeriodHermitian_pos)

theorem PeriodModel.Geometric.AlgebraicPeriodModel.periodDolbeaultCoordinate_injective : Function.Injective M.periodDolbeaultCoordinate :=
  M.periodDifferential.symm.injective.comp
    (AbelianModuli.ReferenceFamily.Intrinsic.HomogeneousCovector.nativeDolbeaultHermitianCoordinate_injective M.abelian M.nativePeriodHermitian
      M.nativePeriodHermitian_symm M.nativePeriodHermitian_pos)

theorem PeriodModel.Geometric.AlgebraicPeriodModel.translationDolbeaultLinear_surjective : Function.Surjective M.translationDolbeaultLinear := by
  have hinj : Function.Injective (M.periodDolbeaultCoordinate.comp M.translationDolbeaultLinear) :=
    M.periodDolbeaultCoordinate_injective.comp M.translationDolbeaultLinear_injective
  have hsurj := LinearMap.surjective_of_injective hinj
  intro w
  obtain ⟨a, ha⟩ := hsurj (M.periodDolbeaultCoordinate w)
  exact ⟨a, M.periodDolbeaultCoordinate_injective ha⟩

def PeriodModel.Geometric.AlgebraicPeriodModel.translationDolbeaultEquiv : DefinitionsIntegral.Tangent dim ≃ₗ[ℂ]
    RepresentationTheory.Theta.Geometric.DolbeaultQuotient.DolbeaultOneSpace (HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :=
  LinearEquiv.ofBijective M.translationDolbeaultLinear
    ⟨M.translationDolbeaultLinear_injective, M.translationDolbeaultLinear_surjective⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
