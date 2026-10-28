import OAI.AlgebraicGeometry.PELModuli.CMPoints.Action
import OAI.RepresentationTheory.Theta.Geometric.AbelianScheme
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PELAdapters
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Realization

/-! # Integral Model -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.IntegralModel

noncomputable section

/-! A constructed integral CM model, with its actual abelian scheme,
correct dimension, rational H1 realization, and full coefficient action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open _root_.NumberField

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [IsCMField E]

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

structure CMIntegralModel (Φ : ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) where
  realization : ComplexMultiplication.CMKnownResults.CM.HodgeRealization Φ.hodgeStructure
  comparison : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E),
    𝓘(ℂ, realization.abelianVariety.variety.analyticModel)⟯
      realization.abelianVariety.variety.analyticSpace
  additive : ∀ u v, comparison (u + v) = comparison u * comparison v
  action : RingOfIntegers E →+* AbelianScheme.TateComparison.End.IntegralEnd realization.abelianVariety.toOver
  action_comparison : ∀ a t,
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianScheme.TateComparison.End.endSchemeMap realization.abelianVariety.toOver (action a))
      (comparison t) = comparison (PeriodAction.cmQuotientAction Φ a t)

theorem exists_CM_integral_model (Φ : ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) : Nonempty (CMIntegralModel Φ) := by
  obtain ⟨R, e, r, he, hr⟩ := Action.exists_CM_integral_realization Action.cmRiemannProjectivityInput_proved Φ
  exact ⟨⟨R, e, he, r, hr⟩⟩

namespace CMIntegralModel

variable {Φ : ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E} (M : CMIntegralModel Φ)

theorem dimension :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension M.realization.abelianVariety.toOver.hom =
      Fintype.card (InfinitePlace E) := by
  let d := (M.comparison.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv
    (x := (0 : Φ.periodTorus)) (by trivial)
  have h := d.toLinearEquiv.finrank_eq
  change Module.finrank ℂ (InfinitePlace E → ℂ) =
    Module.finrank ℂ (Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension
      M.realization.abelianVariety.toOver.hom) → ℂ) at h
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one, Fintype.card_fin] using h.symm

def abelianScheme : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (Fintype.card (InfinitePlace E)) Foundations.Scheme.ProjectiveSpace.complexBase where
  scheme := M.realization.abelianVariety.toOver
  group := M.realization.abelianVariety.group
  commutative := M.realization.abelianVariety.commutative
  proper := M.realization.abelianVariety.variety.presentation.projective.isProper
  smoothDimension := by
    rw [← M.dimension]
    exact Betti.SmoothDimension.Realization.smoothOfFunctionFieldDimension M.realization.abelianVariety.toOver.hom
  connected := (RepresentationTheory.Theta.Geometric.AbelianScheme.abelianSchemeOfVariety M.realization.abelianVariety).connected

def integralAction : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (RingOfIntegers E) M.abelianScheme :=
  AbelianScheme.TateComparison.PELAdapters.actionFromEnd M.action

theorem coefficient_degree : Module.finrank ℚ E = 2 * Fintype.card (InfinitePlace E) := by
  have hfin : Module.finrank ℚ E =
      (letI : Algebra ℚ E := DivisionRing.toRatAlgebra; Module.finrank ℚ E) :=
    congrArg (fun a : Algebra ℚ E => letI := a; Module.finrank ℚ E)
      (Subsingleton.elim (inferInstance : Algebra ℚ E) DivisionRing.toRatAlgebra)
  rw [hfin]
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  simpa only [IsTotallyComplex.nrRealPlaces_eq_zero, zero_add] using
    (NumberField.InfinitePlace.card_add_two_mul_card_eq_rank (K := E)).symm

theorem hasCMH1 : M.realization.abelianVariety.HasCMH1 :=
  Realization.realization_hasCMH1 E M.realization Φ.rankOneCMAction

end CMIntegralModel

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.IntegralModel
