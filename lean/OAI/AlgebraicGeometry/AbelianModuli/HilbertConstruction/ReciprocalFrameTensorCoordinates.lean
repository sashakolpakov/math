import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompatibleSheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.InverseFrameTransitions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf

/-! # Reciprocal Frame Tensor Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Multiplying local frame coordinates pairs reciprocal frame cocycles with the structure sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u v

variable {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens} {D : OpenFrame.Transitions.OpenFrameTransitions U}
variable {M N : X.Modules} (E : CompatibleSheaf.CompatibleSheafFrames D M) (F : CompatibleSheaf.CompatibleSheafFrames D.reciprocal N)

def CompatibleSheaf.CompatibleSheafFrames.reciprocalTensorCoordinate (V : X.Opens) (i : ι) (hi : V ≤ U i) :
    Γ(M, V) ⊗[Γ(X, V)] Γ(N, V) ≃ₗ[Γ(X, V)] Γ(X, V) :=
  (TensorProduct.congr (E.frame V i hi).symm (F.frame V i hi).symm).trans
    (TensorProduct.lid Γ(X, V) Γ(X, V))

theorem CompatibleSheaf.CompatibleSheafFrames.reciprocalTensorCoordinate_tmul (V : X.Opens) (i : ι) (hi : V ≤ U i)
    (x : Γ(M, V)) (y : Γ(N, V)) :
    E.reciprocalTensorCoordinate F V i hi (x ⊗ₜ[Γ(X, V)] y) =
      (E.frame V i hi).symm x * (F.frame V i hi).symm y := by
  simp [CompatibleSheaf.CompatibleSheafFrames.reciprocalTensorCoordinate]

theorem CompatibleSheaf.CompatibleSheafFrames.reciprocalTensorCoordinate_independent (V : X.Opens) (i j : ι)
    (hi : V ≤ U i) (hj : V ≤ U j) :
    E.reciprocalTensorCoordinate F V i hi = E.reciprocalTensorCoordinate F V j hj := by
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change E.reciprocalTensorCoordinate F V i hi (x ⊗ₜ[Γ(X, V)] y) =
    E.reciprocalTensorCoordinate F V j hj (x ⊗ₜ[Γ(X, V)] y)
  rw [E.reciprocalTensorCoordinate_tmul, E.reciprocalTensorCoordinate_tmul,
    E.coordinate_change V i j hi hj x, F.coordinate_change V i j hi hj y, D.reciprocal_value]
  calc
    _ = ((D.value V i j hi hj).val * ((D.value V i j hi hj)⁻¹).val) *
        ((E.frame V j hj).symm x * (F.frame V j hj).symm y) := by ring
    _ = _ := by simp only [← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

theorem CompatibleSheaf.CompatibleSheafFrames.reciprocalTensorCoordinate_restrict (V W : X.Opens) (h : W ≤ V)
    (i : ι) (hi : V ≤ U i) (x : Γ(M, V) ⊗[Γ(X, V)] Γ(N, V)) :
    E.reciprocalTensorCoordinate F W i (h.trans hi)
      ((PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val).map (homOfLE h).op x) =
        X.presheaf.map (homOfLE h).op (E.reciprocalTensorCoordinate F V i hi x) := by
  let ρ : Γ(M, V) ⊗[Γ(X, V)] Γ(N, V) →+ Γ(M, W) ⊗[Γ(X, W)] Γ(N, W) :=
    ((PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val).map (homOfLE h).op).hom.toAddMonoidHom
  have hρ (a : Γ(M, V)) (b : Γ(N, V)) : ρ (a ⊗ₜ[Γ(X, V)] b) =
      M.presheaf.map (homOfLE h).op a ⊗ₜ[Γ(X, W)] N.presheaf.map (homOfLE h).op b := rfl
  change E.reciprocalTensorCoordinate F W i (h.trans hi) (ρ x) =
    X.presheaf.map (homOfLE h).op (E.reciprocalTensorCoordinate F V i hi x)
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    rw [hρ,
      E.reciprocalTensorCoordinate_tmul, E.reciprocalTensorCoordinate_tmul,
      E.coordinate_restrict, F.coordinate_restrict, map_mul]
  | add a b ha hb => simp only [map_add, ha, hb]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
