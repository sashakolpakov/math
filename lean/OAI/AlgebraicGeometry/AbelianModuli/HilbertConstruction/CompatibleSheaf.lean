import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.Transitions

/-! # Compatible Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleSheaf

noncomputable section

/-! Local linear frames of an actual module sheaf, with their restriction and prescribed transition equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens}

structure CompatibleSheafFrames (D : OpenFrame.Transitions.OpenFrameTransitions U) (M : X.Modules) where
  frame : ∀ (V : X.Opens) (i : ι), V ≤ U i → Γ(X, V) ≃ₗ[Γ(X, V)] Γ(M, V)
  restrict : ∀ (V W : X.Opens) (h : W ≤ V) (i : ι) (hi : V ≤ U i) (x : Γ(X, V)),
    M.presheaf.map (homOfLE h).op (frame V i hi x) =
      frame W i (h.trans hi) (X.presheaf.map (homOfLE h).op x)
  change : ∀ (V : X.Opens) (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j) (x : Γ(X, V)),
    frame V i hi ((D.value V i j hi hj).val * x) = frame V j hj x

namespace CompatibleSheafFrames

variable {D : OpenFrame.Transitions.OpenFrameTransitions U} {M : X.Modules} (E : CompatibleSheafFrames D M)

theorem coordinate_change (V : X.Opens) (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j) (x : Γ(M, V)) :
    (E.frame V i hi).symm x = (D.value V i j hi hj).val * (E.frame V j hj).symm x := by
  apply (E.frame V i hi).injective
  exact ((E.frame V i hi).apply_symm_apply x).trans
    ((E.change V i j hi hj ((E.frame V j hj).symm x)).trans ((E.frame V j hj).apply_symm_apply x)).symm

theorem coordinate_restrict (V W : X.Opens) (h : W ≤ V) (i : ι) (hi : V ≤ U i) (x : Γ(M, V)) :
    (E.frame W i (h.trans hi)).symm (M.presheaf.map (homOfLE h).op x) =
      X.presheaf.map (homOfLE h).op ((E.frame V i hi).symm x) := by
  apply (E.frame W i (h.trans hi)).injective
  exact ((E.frame W i (h.trans hi)).apply_symm_apply _).trans
    ((congrArg (M.presheaf.map (homOfLE h).op) ((E.frame V i hi).apply_symm_apply x)).symm.trans
      (E.restrict V W h i hi ((E.frame V i hi).symm x)))

end CompatibleSheafFrames

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleSheaf
