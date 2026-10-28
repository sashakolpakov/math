import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Algebraization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.FunctorAction
import OAI.RepresentationTheory.Theta.Geometric.AbelianScheme
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.ComplexLevel

/-! # Algebraic Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel

noncomputable section

/-! Chosen algebraic reference models, constructed from admissibility.
Their dimension, integral scheme action, and finite ordered levels are
derived while retaining the exact biholomorphic period comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} (F : Fiber.ReferenceAnalyticFiber P z) (hP : P.IsAdmissible)

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

structure ReferenceAlgebraicModel where
  abelian : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety
  period : F.periodData.periodTorus ≃ₘ⟮𝓘(ℂ, F.periodData.space),
    𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel abelian)⟯ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints abelian.toOver
  functorAction : NumberField.RingOfIntegers E →+* AbelianScheme.TateComparison.End.IntegralEnd abelian.toOver
  period_add : ∀ u v, period (u + v) = period u * period v
  period_action : ∀ a t,
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianScheme.TateComparison.End.endSchemeMap abelian.toOver (functorAction a)) (period t) =
      period (F.quotientAction hP a t)

theorem referenceAlgebraicModel_nonempty : Nonempty (ReferenceAlgebraicModel F hP) := by
  obtain ⟨A, e, r, he, hr⟩ := F.exists_abelian_model_with_action hP
  exact ⟨⟨A, e, r, he, hr⟩⟩

def referenceAlgebraicModel : ReferenceAlgebraicModel F hP :=
  Classical.choice (referenceAlgebraicModel_nonempty F hP)

namespace ReferenceAlgebraicModel

variable {F hP} (M : ReferenceAlgebraicModel F hP)

theorem dimension : Betti.AffineDimension.Realization.functionFieldDifferentialDimension M.abelian.toOver.hom = 3 * s := by
  have h := RepresentationTheory.Theta.Geometric.AbelianScheme.abelian_model_dimension F.periodData M.abelian M.period
  change Betti.AffineDimension.Realization.functionFieldDifferentialDimension M.abelian.toOver.hom =
    Module.finrank ℂ (Fin (3 * Fintype.card (Fin s)) → ℂ) at h
  simpa only [Module.finrank_fin_fun, Fintype.card_fin] using h

def abelianScheme : HilbertConstruction.Abelian.Schemes.AbelianScheme (3 * s) Foundations.Scheme.ProjectiveSpace.complexBase where
  scheme := M.abelian.toOver
  group := M.abelian.group
  commutative := M.abelian.commutative
  proper := M.abelian.variety.presentation.projective.isProper
  smoothDimension := by
    rw [← M.dimension]
    exact Betti.SmoothDimension.Realization.smoothOfFunctionFieldDimension M.abelian.toOver.hom
  connected := (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety M.abelian).connected

def integralAction : ActionData.IntegralAction (NumberField.RingOfIntegers E) M.abelianScheme :=
  Integral.FunctorAction.integralActionOfFunctorAction M.abelianScheme M.functorAction

def fullLevel (N : ℕ) [NeZero N] : M.abelianScheme.FullLevel N :=
  Complex.ComplexLevel.fullLevel M.abelianScheme M.abelian.variety.presentation.projective N

end ReferenceAlgebraicModel

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel
