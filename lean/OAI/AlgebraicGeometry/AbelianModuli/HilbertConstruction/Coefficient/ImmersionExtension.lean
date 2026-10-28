import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalTensorMapCartesian
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.TensorImmersion

/-! # Immersion Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ImmersionExtension

noncomputable section

/-! The descended affine open immersion persists under further coefficient extension. -/

open TensorProduct _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem natural_tensorMap_isOpenImmersion_mono
    {C R A B : Type u} [CommRing C] [CommRing R] [CommRing A] [CommRing B]
    [Algebra C R] [Algebra C A] [Algebra C B]
    {D E : Subalgebra C R} (h : D ≤ E) (φ : A →ₐ[C] B)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id D D) φ).toRingHom))] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id E E) φ).toRingHom)) := by
  let : Algebra D E := (Subalgebra.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower C D E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (R := E ⊗[D] (D ⊗[C] A)) (S := E ⊗[D] (D ⊗[C] B))
      (Algebra.TensorProduct.map (AlgHom.id E E)
        (Algebra.TensorProduct.map (AlgHom.id D D) φ)).toRingHom)) :=
    NaturalTensorMapCartesian.natural_tensorMap_isOpenImmersion (C := D) (R := E) (A := D ⊗[C] A) (B := D ⊗[C] B)
      (Algebra.TensorProduct.map (AlgHom.id D D) φ)
  exact Iterated.TensorImmersion.isOpenImmersion_of_iterated_tensorMap (C := C) (D := D) (F := E) (A := A) (B := B) φ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ImmersionExtension
