import OAI.AlgebraicGeometry.Picard.ThetaConstruction.ProjectivePeriodData
import OAI.RepresentationTheory.Theta.Geometric.Torus.AbelianModel

/-! # Realization -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.Realization.Geometric

noncomputable section

/-!
Algebraize the actual quotient constructed by ThetaConstruction, with a biholomorphic,
group-preserving comparison to the original quotient. This is a geometric
construction from the positive period, not an algebraization premise.
The comparison of the specified polarization morphism is a separate step.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

local instance algebraicRealizationIntegral (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left :=
  A.variety.property
local instance algebraicRealizationSmooth (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom :=
  A.variety.presentation.smooth

variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g}

/-- The checked analytic torus is biholomorphic to an actual algebraic
abelian variety, and the comparison preserves its group operation. -/
theorem algebraic_uniformization_of_positive_period
    (E : DefinitionsIntegral.IntegralMatrix g) (hE : E.transpose = -E)
    (P : Submodule ℂ (DefinitionsIntegral.CVec g)) (hP : DefinitionsIntegral.CompatiblePositivePeriod E P) :
    ∃ (T : DefinitionsIntegral.MarkedPolarizedTorus g E), T.periodMap.ker = P ∧
      ∃ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
        (e : (ProjectivePeriodData.Geometric.projectivePeriodData T).periodTorus ≃ₘ⟮𝓘(ℂ, (ProjectivePeriodData.Geometric.projectivePeriodData T).space),
          𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension A.toOver.hom) → ℂ)⟯
          ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver),
        ∀ u v, e (u + v) = e u * e v := by
  obtain ⟨T, hT⟩ := DefinitionsIntegral.realize_positive_period E hE P hP
  obtain ⟨A, e, he⟩ :=
    RepresentationTheory.Theta.Geometric.Torus.AbelianModel.CM.Algebraization.AbelianTorusModel.exists_abelian_model_with_group
      (ProjectivePeriodData.Geometric.projectivePeriodData T)
  exact ⟨T, hT, A, e, he⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.Realization.Geometric
