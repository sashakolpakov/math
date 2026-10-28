import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntegralDualLe
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.PeriodModel
import OAI.RepresentationTheory.Theta.Geometric.AbelianScheme
import OAI.RepresentationTheory.Theta.Geometric.Torus.Isogeny

/-! # Integral Dual Model -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! Algebraize the actual integral dual torus and its lattice inclusion.
This constructs an actual finite etale isogeny. Identification with the
homogeneous Picard sheaf is a separate universal-property obligation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} {T : DefinitionsIntegral.MarkedPolarizedTorus g E}

section
variable (M : PeriodModel.Geometric.AlgebraicPeriodModel T)

local instance PeriodModel.Geometric.AlgebraicPeriodModel.originalModelIntegral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.originalModelSmooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

theorem PeriodModel.Geometric.AlgebraicPeriodModel.abelian_dimension : Betti.AffineDimension.Realization.functionFieldDifferentialDimension M.abelian.toOver.hom = g := by
  have h := RepresentationTheory.Theta.Geometric.AbelianScheme.abelian_model_dimension (ProjectivePeriodData.Geometric.projectivePeriodData T) M.abelian M.period
  exact h.trans (by
    change Module.finrank ℂ (Fin g → ℂ) = g
    exact Module.finrank_fin_fun ℂ)

def PeriodModel.Geometric.AlgebraicPeriodModel.abelianScheme : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase where
  scheme := M.abelian.toOver
  group := M.abelian.group
  commutative := M.abelian.commutative
  proper := M.abelian.variety.presentation.projective.isProper
  smoothDimension := by
    exact (congrArg (fun d : ℕ => SmoothOfRelativeDimension d M.abelian.toOver.hom)
      M.abelian_dimension).mp (Betti.SmoothDimension.Realization.smoothOfFunctionFieldDimension M.abelian.toOver.hom)
  connected := (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety M.abelian).connected

end

local instance IntegralDualModel.Geometric.integralDualVarietyIntegral (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral B.toOver.left := B.variety.property
local instance IntegralDualModel.Geometric.integralDualVarietySmooth (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth B.toOver.hom := B.variety.presentation.smooth

structure IntegralDualModel.Geometric.IntegralDualAlgebraicModel (T : DefinitionsIntegral.MarkedPolarizedTorus g E) where
  abelian : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety
  period : T.integralDualPeriodData.periodTorus ≃ₘ⟮𝓘(ℂ, T.integralDualPeriodData.space),
    𝓘(ℂ, HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel abelian)⟯ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints abelian.toOver
  period_add : ∀ u v, period (u + v) = period u * period v

theorem IntegralDualModel.Geometric.exists_integral_dual_algebraic_model (T : DefinitionsIntegral.MarkedPolarizedTorus g E) :
    Nonempty (IntegralDualModel.Geometric.IntegralDualAlgebraicModel T) := by
  obtain ⟨A, e, he⟩ :=
    RepresentationTheory.Theta.Geometric.Torus.AbelianModel.CM.Algebraization.AbelianTorusModel.exists_abelian_model_with_group T.integralDualPeriodData
  exact ⟨⟨A, e, he⟩⟩

namespace IntegralDualModel.Geometric.IntegralDualAlgebraicModel
variable (M : IntegralDualAlgebraicModel T)

local instance dualModelIntegral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance dualModelSmooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

theorem abelian_dimension : Betti.AffineDimension.Realization.functionFieldDifferentialDimension M.abelian.toOver.hom = g := by
  have h := RepresentationTheory.Theta.Geometric.AbelianScheme.abelian_model_dimension T.integralDualPeriodData M.abelian M.period
  exact h.trans (by
    change Module.finrank ℂ (Fin g → ℂ) = g
    exact Module.finrank_fin_fun ℂ)

def abelianScheme : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase where
  scheme := M.abelian.toOver
  group := M.abelian.group
  commutative := M.abelian.commutative
  proper := M.abelian.variety.presentation.projective.isProper
  smoothDimension := by
    exact (congrArg (fun d : ℕ => SmoothOfRelativeDimension d M.abelian.toOver.hom)
      M.abelian_dimension).mp (Betti.SmoothDimension.Realization.smoothOfFunctionFieldDimension M.abelian.toOver.hom)
  connected := (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety M.abelian).connected

end IntegralDualModel.Geometric.IntegralDualAlgebraicModel

def IntegralDualModel.Geometric.integralDualTorusMap (T : DefinitionsIntegral.MarkedPolarizedTorus g E) :
    (ProjectivePeriodData.Geometric.projectivePeriodData T).periodTorus →+ T.integralDualPeriodData.periodTorus :=
  RepresentationTheory.Theta.Geometric.Torus.Hom.torusLinearMap (ProjectivePeriodData.Geometric.projectivePeriodData T) T.integralDualPeriodData
    (LinearMap.id : DefinitionsIntegral.Tangent g →ₗ[ℂ] DefinitionsIntegral.Tangent g) (fun _ hv => T.lattice_le_integralDual hv)

theorem IntegralDualModel.Geometric.exists_integral_dual_algebraic_isogeny (M : PeriodModel.Geometric.AlgebraicPeriodModel T) :
    ∃ (N : IntegralDualModel.Geometric.IntegralDualAlgebraicModel T) (p : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny M.abelianScheme N.abelianScheme),
      Etale p.hom.left ∧ ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.hom (M.period t) =
        N.period (IntegralDualModel.Geometric.integralDualTorusMap T t) := by
  obtain ⟨N⟩ := IntegralDualModel.Geometric.exists_integral_dual_algebraic_model T
  obtain ⟨n, hn, hL⟩ := T.integralDual_bounded_denominator
  obtain ⟨f, hfg, hfinite, het, hsurj, hf⟩ := RepresentationTheory.Theta.Geometric.Torus.Isogeny.exists_algebraic_torus_isogeny
    (ProjectivePeriodData.Geometric.projectivePeriodData T) T.integralDualPeriodData LinearMap.id (n • LinearMap.id)
    (fun _ hv => T.lattice_le_integralDual hv) (fun v hv => hL ⟨v, hv⟩)
    n hn (fun _ => rfl) (fun _ => rfl) M.abelian N.abelian M.period N.period M.period_add N.period_add
  exact ⟨N, ⟨f, hfg, hfinite, (Etale.iff_flat_and_formallyUnramified.mp het).1, hsurj⟩, het, hf⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
