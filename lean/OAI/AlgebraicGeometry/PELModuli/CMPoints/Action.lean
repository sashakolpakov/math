import OAI.AlgebraicGeometry.PELModuli.CMPoints.GroupRealization
import OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodAction
import OAI.RepresentationTheory.Theta.Geometric.AlgebraicAction
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion

/-! # Action -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.Action

noncomputable section

/-! Algebraize the full integral coefficient action on the canonical
CM realization, retaining its literal action on all period-torus points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

theorem cmRiemannProjectivityInput_proved : Geometry.ComplexTorus.RiemannProjectivity.Fin.Constructions.RiemannProjectivityInput := by
  intro V _ _ _ Λ _ _
  exact Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.riemann_projectivity_criterion V Λ

theorem exists_CM_integral_realization
    (hRiemannProjectivity : Geometry.ComplexTorus.RiemannProjectivity.Fin.Constructions.RiemannProjectivityInput)
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    (Φ : ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) :
    ∃ (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization Φ.hodgeStructure)
      (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E),
        𝓘(ℂ, R.abelianVariety.variety.analyticModel)⟯ R.abelianVariety.variety.analyticSpace)
      (r : NumberField.RingOfIntegers E →+* AbelianScheme.TateComparison.End.IntegralEnd R.abelianVariety.toOver),
      (∀ u v, e (u + v) = e u * e v) ∧
      ∀ a t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianScheme.TateComparison.End.endSchemeMap R.abelianVariety.toOver (r a)) (e t) =
        e (PeriodAction.cmQuotientAction Φ a t) := by
  obtain ⟨R, e, he⟩ := GroupRealization.exists_CM_group_realization hRiemannProjectivity Φ
  let eadd : Φ.periodTorus ≃+ RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianPoints R.abelianVariety :=
    { toFun := fun t => Additive.ofMul (e t)
      invFun := fun p => e.symm p.toMul
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply
      map_add' := he }
  let r := RepresentationTheory.Theta.Geometric.AlgebraicAction.transportAdditiveAction eadd (PeriodAction.cmQuotientAction Φ)
  have hr : ∀ a, MDifferentiable 𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel R.abelianVariety)
      𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel R.abelianVariety)
      (fun p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints R.abelianVariety.toOver => (r a (Additive.ofMul p)).toMul) := by
    intro a
    change MDifferentiable _ _ (fun p => e (PeriodAction.cmQuotientAction Φ a (e.symm p)))
    exact (e.contMDiff.comp ((PeriodAction.cmQuotientAction_contMDiff Φ a).comp e.symm.contMDiff)).mdifferentiable
      (by norm_num)
  obtain ⟨ralg, hralg⟩ := RepresentationTheory.Theta.Geometric.AlgebraicAction.exists_algebraic_ring_action R.abelianVariety r hr
  refine ⟨R, e, ralg, he, fun a t => ?_⟩
  have h := DFunLike.congr_fun (hralg a) (Additive.ofMul (e t))
  change (RepresentationTheory.Theta.Geometric.AlgebraicAction.algebraicEndPoints R.abelianVariety (ralg a) (Additive.ofMul (e t))).toMul =
    e (PeriodAction.cmQuotientAction Φ a (e.symm (e t))) at h
  rw [e.symm_apply_apply] at h
  exact (AbelianScheme.TateComparison.End.endSchemeMap_points R.abelianVariety.toOver (ralg a) _ (e t)).symm.trans h

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.Action
