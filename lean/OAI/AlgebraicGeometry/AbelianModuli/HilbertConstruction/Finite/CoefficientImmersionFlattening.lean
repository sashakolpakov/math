import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.TensorImmersion
import Mathlib.RingTheory.Finiteness.Subalgebra

/-! # Coefficient Immersion Flattening -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoefficientImmersionFlattening

noncomputable section

/-! Two finite coefficient extensions give one finite extension carrying the same open immersion. -/

open TensorProduct _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem finite_coefficient_immersion_flatten
    {C R A B : Type u} [CommRing C] [CommRing R] [CommRing A] [CommRing B]
    [Algebra C R] [Algebra C A] [Algebra C B]
    (D : Subalgebra C R) (F : Subalgebra D R) (hD : D.FG) (hF : F.FG)
    (φ : A →ₐ[C] B)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (R := F ⊗[D] (D ⊗[C] A)) (S := F ⊗[D] (D ⊗[C] B))
      (Algebra.TensorProduct.map (AlgHom.id F F)
        (Algebra.TensorProduct.map (AlgHom.id D D) φ)).toRingHom))] :
    D ≤ F.restrictScalars C ∧ (F.restrictScalars C).FG ∧
      IsOpenImmersion (Spec.map (CommRingCat.ofHom
        (R := (F.restrictScalars C) ⊗[C] A) (S := (F.restrictScalars C) ⊗[C] B)
        (Algebra.TensorProduct.map (AlgHom.id (F.restrictScalars C) (F.restrictScalars C))
          φ).toRingHom)) := by
  have : Algebra.FiniteType C D := (Subalgebra.fg_iff_finiteType D).mp hD
  have : Algebra.FiniteType D F := (Subalgebra.fg_iff_finiteType F).mp hF
  have : Algebra.FiniteType C F :=
    Algebra.FiniteType.trans (S := D) (inferInstanceAs (Algebra.FiniteType C D))
      (inferInstanceAs (Algebra.FiniteType D F))
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    exact F.algebraMap_mem (⟨r, hr⟩ : D)
  · exact (Subalgebra.fg_iff_finiteType (F.restrictScalars C)).mpr
      (inferInstanceAs (Algebra.FiniteType C F))
  · exact Iterated.TensorImmersion.isOpenImmersion_of_iterated_tensorMap (C := C) (D := D) (F := F) φ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoefficientImmersionFlattening
