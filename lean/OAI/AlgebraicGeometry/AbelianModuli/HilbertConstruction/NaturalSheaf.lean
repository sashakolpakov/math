import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleSheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.FrameRatios

/-! # Natural Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalSheaf

noncomputable section

/-! Local frames commuting with restriction determine their actual regular-function transition cocycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v}

structure NaturalSheafFrames (U : ι → X.Opens) (M : X.Modules) where
  frame : ∀ (V : X.Opens) (i : ι), V ≤ U i → Γ(X, V) ≃ₗ[Γ(X, V)] Γ(M, V)
  restrict : ∀ (V W : X.Opens) (h : W ≤ V) (i : ι) (hi : V ≤ U i) (r : Γ(X, V)),
    M.presheaf.map (homOfLE h).op (frame V i hi r) =
      frame W i (h.trans hi) (X.presheaf.map (homOfLE h).op r)

namespace NaturalSheafFrames

variable {U : ι → X.Opens} {M : X.Modules} (E : NaturalSheafFrames U M)

theorem ratio_restrict (V W : X.Opens) (h : W ≤ V) (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j) :
    X.presheaf.map (homOfLE h).op (Linear.FrameRatios.linearFrameRatio (E.frame V i hi) (E.frame V j hj)) =
      Linear.FrameRatios.linearFrameRatio (E.frame W i (h.trans hi)) (E.frame W j (h.trans hj)) := by
  apply (E.frame W i (h.trans hi)).injective
  have hi' := E.restrict V W h i hi (Linear.FrameRatios.linearFrameRatio (E.frame V i hi) (E.frame V j hj))
  have hj' := E.restrict V W h j hj 1
  exact hi'.symm.trans ((congrArg (M.presheaf.map (homOfLE h).op)
    ((E.frame V i hi).apply_symm_apply (E.frame V j hj 1))).trans
      (hj'.trans ((congrArg (E.frame W j (h.trans hj)) ((X.presheaf.map (homOfLE h).op).hom.map_one)).trans
        ((E.frame W i (h.trans hi)).apply_symm_apply (E.frame W j (h.trans hj) 1)).symm)))

def transitions : OpenFrame.Transitions.OpenFrameTransitions U where
  value V i j hi hj := Linear.FrameRatios.linearFrameRatioUnit (E.frame V i hi) (E.frame V j hj)
  restrict := E.ratio_restrict
  self V i hi := Units.ext (Linear.FrameRatios.linearFrameRatio_self (E.frame V i hi))
  comp V i j k hi hj hk := Units.ext (Linear.FrameRatios.linearFrameRatio_comp (E.frame V i hi) (E.frame V j hj) (E.frame V k hk))

def compatible : CompatibleSheaf.CompatibleSheafFrames E.transitions M where
  frame := E.frame
  restrict := E.restrict
  change V i j hi hj r := Linear.FrameRatios.linearFrameRatio_frame (E.frame V i hi) (E.frame V j hj) r

end NaturalSheafFrames

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalSheaf
