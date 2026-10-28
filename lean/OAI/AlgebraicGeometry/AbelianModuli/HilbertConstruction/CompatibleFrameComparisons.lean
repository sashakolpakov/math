import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleSheaf

/-! # Compatible Frame Comparisons -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Two sheaves with the same actual frame cocycle have compatible local linear isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens} {D : OpenFrame.Transitions.OpenFrameTransitions U}
variable {M N : X.Modules} (E : CompatibleSheaf.CompatibleSheafFrames D M) (F : CompatibleSheaf.CompatibleSheafFrames D N)

def CompatibleSheaf.CompatibleSheafFrames.comparison (V : X.Opens) (i : ι) (hi : V ≤ U i) : Γ(M, V) ≃ₗ[Γ(X, V)] Γ(N, V) :=
  (E.frame V i hi).symm.trans (F.frame V i hi)

theorem CompatibleSheaf.CompatibleSheafFrames.comparison_independent (V : X.Opens) (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j) :
    E.comparison F V i hi = E.comparison F V j hj := by
  ext x
  exact (congrArg (F.frame V i hi) (E.coordinate_change V i j hi hj x)).trans
    (F.change V i j hi hj ((E.frame V j hj).symm x))

theorem CompatibleSheaf.CompatibleSheafFrames.comparison_restrict (V W : X.Opens) (h : W ≤ V) (i j : ι)
    (hi : W ≤ U i) (hj : V ≤ U j) (x : Γ(M, V)) :
    E.comparison F W i hi (M.presheaf.map (homOfLE h).op x) =
      N.presheaf.map (homOfLE h).op (E.comparison F V j hj x) := by
  have hc := congrArg (fun e : Γ(M, W) ≃ₗ[Γ(X, W)] Γ(N, W) =>
      e (M.presheaf.map (homOfLE h).op x)) (E.comparison_independent F W i j hi (h.trans hj))
  exact hc.trans ((congrArg (F.frame W j (h.trans hj)) (E.coordinate_restrict V W h j hj x)).trans
    (F.restrict V W h j hj ((E.frame V j hj).symm x)).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
