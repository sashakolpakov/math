import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleSheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.OpenMapGluing

/-! # Frame Coefficient Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.FrameCoefficientMaps

noncomputable section

/-! Compatible coefficients in a target module determine local linear maps from a sheaf with rank-one frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens} {D : OpenFrame.Transitions.OpenFrameTransitions U}
variable {M N : X.Modules} (E : CompatibleSheaf.CompatibleSheafFrames D M)

def FrameMorphismCompatible (t : ∀ i, Γ(N, U i)) : Prop :=
  ∀ (V : X.Opens) (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j),
    N.presheaf.map (homOfLE hj).op (t j) =
      (D.value V i j hi hj).val • N.presheaf.map (homOfLE hi).op (t i)

def frameCoefficientMap (t : ∀ i, Γ(N, U i)) (V : X.Opens) (i : ι) (hi : V ≤ U i) :
    Γ(M, V) →ₗ[Γ(X, V)] Γ(N, V) :=
  (LinearMap.toSpanSingleton Γ(X, V) Γ(N, V) (N.presheaf.map (homOfLE hi).op (t i))).comp
    (E.frame V i hi).symm.toLinearMap

theorem frameCoefficientMap_independent (t : ∀ i, Γ(N, U i)) (ht : FrameMorphismCompatible (D := D) t)
    (V : X.Opens) (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j) :
    frameCoefficientMap E t V i hi = frameCoefficientMap E t V j hj := by
  ext x
  change (E.frame V i hi).symm x • N.presheaf.map (homOfLE hi).op (t i) =
    (E.frame V j hj).symm x • N.presheaf.map (homOfLE hj).op (t j)
  rw [E.coordinate_change V i j hi hj x, ht V i j hi hj, mul_smul]
  exact smul_comm _ _ _

theorem frameCoefficientMap_restrict (t : ∀ i, Γ(N, U i))
    (V W : X.Opens) (h : W ≤ V) (i : ι) (hi : V ≤ U i) (x : Γ(M, V)) :
    frameCoefficientMap E t W i (h.trans hi) (M.presheaf.map (homOfLE h).op x) =
      N.presheaf.map (homOfLE h).op (frameCoefficientMap E t V i hi x) := by
  change (E.frame W i (h.trans hi)).symm (M.presheaf.map (homOfLE h).op x) •
    N.presheaf.map (homOfLE (h.trans hi)).op (t i) =
      N.presheaf.map (homOfLE h).op ((E.frame V i hi).symm x •
        N.presheaf.map (homOfLE hi).op (t i))
  rw [E.coordinate_restrict, N.map_smul, ← N.presheaf.map_comp_apply]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.FrameCoefficientMaps
