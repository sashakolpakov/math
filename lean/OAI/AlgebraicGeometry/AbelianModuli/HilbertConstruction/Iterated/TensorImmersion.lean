import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ImmersionTransport
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Tensor Immersion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.TensorImmersion

noncomputable section

/-! Removing an intermediate coefficient algebra preserves the actual affine open immersion. -/

open TensorProduct _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {C D F A B : Type u}
variable [CommRing C] [CommRing D] [CommRing F] [CommRing A] [CommRing B]
variable [Algebra C D] [Algebra C F] [Algebra D F] [IsScalarTower C D F]
variable [Algebra C A] [Algebra C B]

theorem tensor_cancelBaseChange_natural (φ : A →ₐ[C] B) :
    (Algebra.TensorProduct.cancelBaseChange C D F F B).toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id F F)
        (Algebra.TensorProduct.map (AlgHom.id D D) φ)) =
    (Algebra.TensorProduct.map (AlgHom.id F F) φ).comp
      (Algebra.TensorProduct.cancelBaseChange C D F F A).toAlgHom := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul r x =>
    induction x using TensorProduct.inductionOn with
    | tmul d a =>
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.cancelBaseChange_tmul]
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem isOpenImmersion_of_iterated_tensorMap (φ : A →ₐ[C] B)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id F F)
        (Algebra.TensorProduct.map (AlgHom.id D D) φ)).toRingHom))] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id F F) φ).toRingHom)) := by
  exact Affine.ImmersionTransport.isOpenImmersion_SpecMap_of_conjugate
    (Algebra.TensorProduct.map (AlgHom.id F F)
      (Algebra.TensorProduct.map (AlgHom.id D D) φ)).toRingHom
    (Algebra.TensorProduct.map (AlgHom.id F F) φ).toRingHom
    (Algebra.TensorProduct.cancelBaseChange C D F F A).toRingEquiv
    (Algebra.TensorProduct.cancelBaseChange C D F F B).toRingEquiv
    (DFunLike.congr_fun (tensor_cancelBaseChange_natural (D := D) (F := F) φ))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.TensorImmersion
