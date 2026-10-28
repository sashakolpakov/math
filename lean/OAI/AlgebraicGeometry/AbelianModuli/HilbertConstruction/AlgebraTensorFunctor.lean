import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Algebra Tensor Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraTensorFunctor

noncomputable section

/-! Scalar extension by tensor product is functorial for commutative algebras. -/

open _root_.CategoryTheory TensorProduct

universe u

def algebraTensorFunctor (C D : Type u) [CommRing C] [CommRing D] [Algebra C D] :
    CommAlgCat C ⥤ CommAlgCat D where
  obj A := CommAlgCat.of D (D ⊗[C] A)
  map f := CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id D D) f.hom)
  map_id A := by
    apply CommAlgCat.hom_ext
    exact Algebra.TensorProduct.map_id
  map_comp f g := by
    apply CommAlgCat.hom_ext
    exact Algebra.TensorProduct.map_id_comp g.hom f.hom

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraTensorFunctor
