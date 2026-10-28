import OAI.RepresentationTheory.Theta.Geometric.Torus.AlgebraicAction

/-! # Chosen Torus Ring Action -/

namespace OAI.RepresentationTheory.Theta.Geometric.ChosenTorusRingAction

noncomputable section

/-! Algebraize a lattice-preserving ring action on an already chosen
abelian model of the period torus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

theorem exists_ring_action_on_period_model (Φ : Torus.Data.CM.ProjectivePeriodData)
    {R : Type} [Ring R] (action : R →+* Module.End ℂ Φ.space)
    (haction : ∀ a v, v ∈ Φ.periodIntegerLattice → action a v ∈ Φ.periodIntegerLattice)
    (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (he : ∀ u v, e (u + v) = e u * e v) :
    ∃ r : R →+* AlgebraicGeometry.AbelianScheme.TateComparison.End.IntegralEnd A.toOver,
      ∀ a t, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap A.toOver (r a)) (e t) =
        e (Φ.quotientRingAction action haction a t) := by
  let eadd : Φ.periodTorus ≃+ AlgebraicAction.AbelianPoints A :=
    { toFun := fun t => Additive.ofMul (e t)
      invFun := fun p => e.symm p.toMul
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply
      map_add' := he }
  let r := AlgebraicAction.transportAdditiveAction eadd (Φ.quotientRingAction action haction)
  have hr : ∀ a, MDifferentiable 𝓘(ℂ, AlgebraicAction.AbelianModel A) 𝓘(ℂ, AlgebraicAction.AbelianModel A)
      (fun p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver => (r a (Additive.ofMul p)).toMul) := by
    intro a
    change MDifferentiable _ _ (fun p => e (Φ.quotientRingAction action haction a (e.symm p)))
    exact (e.contMDiff.comp ((Φ.quotientRingAction_contMDiff action haction a).comp e.symm.contMDiff)).mdifferentiable
      (by norm_num)
  obtain ⟨ralg, hralg⟩ := AlgebraicAction.exists_algebraic_ring_action A r hr
  refine ⟨ralg, fun a t => ?_⟩
  have h := DFunLike.congr_fun (hralg a) (Additive.ofMul (e t))
  change (AlgebraicAction.algebraicEndPoints A (ralg a) (Additive.ofMul (e t))).toMul =
    e (Φ.quotientRingAction action haction a (e.symm (e t))) at h
  rw [e.symm_apply_apply] at h
  exact (AlgebraicGeometry.AbelianScheme.TateComparison.End.endSchemeMap_points A.toOver (ralg a) _ (e t)).symm.trans h

end

end OAI.RepresentationTheory.Theta.Geometric.ChosenTorusRingAction
