import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Action
import OAI.RepresentationTheory.Theta.Geometric.Torus.AbelianModel
import OAI.RepresentationTheory.Theta.Geometric.AlgebraicAction

/-! # Algebraization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Algebraization.ReferenceAnalyticFiber

noncomputable section

/-! Construct an actual abelian variety for each ReferenceFamily reference period
fiber, retaining its original torus and algebraizing the integral action.
The construction invokes the proved projective-torus and graph theorems. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} (F : Fiber.ReferenceAnalyticFiber P z)

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber.exists_abelian_model_with_action (hP : P.IsAdmissible) :
    ∃ (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
      (e : F.periodData.periodTorus ≃ₘ⟮𝓘(ℂ, F.periodData.space),
        𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel A)⟯ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
      (r : NumberField.RingOfIntegers E →+* AbelianScheme.TateComparison.End.IntegralEnd A.toOver),
      (∀ u v, e (u + v) = e u * e v) ∧
      ∀ a t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AbelianScheme.TateComparison.End.endSchemeMap A.toOver (r a)) (e t) =
        e (F.quotientAction hP a t) := by
  obtain ⟨A, e, he⟩ :=
    RepresentationTheory.Theta.Geometric.Torus.AbelianModel.CM.Algebraization.AbelianTorusModel.exists_abelian_model_with_group F.periodData
  let eadd : F.periodData.periodTorus ≃+ RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianPoints A := {
    toFun := fun t => Additive.ofMul (e t)
    invFun := fun p => e.symm p.toMul
    left_inv := e.symm_apply_apply
    right_inv := e.apply_symm_apply
    map_add' := he }
  let r := RepresentationTheory.Theta.Geometric.AlgebraicAction.transportAdditiveAction eadd (F.quotientRingAction hP)
  have hr : ∀ a, MDifferentiable 𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel A) 𝓘(ℂ, RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel A)
      (fun p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver => (r a (Additive.ofMul p)).toMul) := by
    intro a
    change MDifferentiable _ _ (fun p => e (F.quotientAction hP a (e.symm p)))
    exact (e.contMDiff.comp ((F.quotientAction_contMDiff hP a).comp e.symm.contMDiff)).mdifferentiable
      (by norm_num)
  obtain ⟨ralg, hralg⟩ := RepresentationTheory.Theta.Geometric.AlgebraicAction.exists_algebraic_ring_action A r hr
  refine ⟨A, e, ralg, he, ?_⟩
  intro a t
  have h := DFunLike.congr_fun (hralg a) (Additive.ofMul (e t))
  change (RepresentationTheory.Theta.Geometric.AlgebraicAction.algebraicEndPoints A (ralg a) (Additive.ofMul (e t))).toMul =
    e (F.quotientAction hP a (e.symm (e t))) at h
  rw [e.symm_apply_apply] at h
  exact (AbelianScheme.TateComparison.End.endSchemeMap_points A.toOver (ralg a) _ (e t)).symm.trans h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Algebraization.ReferenceAnalyticFiber
