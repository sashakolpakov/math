import OAI.RepresentationTheory.Theta.Geometric.Dual.TensorEvaluation
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Tensor Point Diagram -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.TensorPointDiagram

noncomputable section

/-! The tensor evaluation is the actual constant dual-number point of
the affine base change, with both native scheme projections verified. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped TensorProduct

variable {A : Type} [CommRing A] [Algebra ℂ A]

def dualTensorPoint (p : A →ₐ[ℂ] ℂ) :
    Spec (.of (DualNumber ℂ)) ⟶ Spec (.of (DualNumber ℂ ⊗[ℂ] A)) :=
  Spec.map (CommRingCat.ofHom (TensorEvaluation.dualTensorEvaluation p).toRingHom)

theorem dualTensorPoint_first (p : A →ₐ[ℂ] ℂ) :
    dualTensorPoint p ≫ (pullbackSpecIso ℂ (DualNumber ℂ) A).inv ≫
      pullback.fst _ _ = 𝟙 (Spec (.of (DualNumber ℂ))) := by
  rw [pullbackSpecIso_inv_fst]
  unfold dualTensorPoint
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((TensorEvaluation.dualTensorEvaluation p).comp Algebra.TensorProduct.includeLeft).toRingHom) = _
  rw [TensorEvaluation.dualTensorEvaluation_comp_left]
  exact Spec.map_id _

theorem dualTensorPoint_second (p : A →ₐ[ℂ] ℂ) :
    dualTensorPoint p ≫ (pullbackSpecIso ℂ (DualNumber ℂ) A).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom ((Algebra.ofId ℂ (DualNumber ℂ)).comp p).toRingHom) := by
  rw [pullbackSpecIso_inv_snd]
  unfold dualTensorPoint
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((TensorEvaluation.dualTensorEvaluation p).comp Algebra.TensorProduct.includeRight).toRingHom) = _
  rw [TensorEvaluation.dualTensorEvaluation_comp_right]

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.TensorPointDiagram
