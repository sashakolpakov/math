import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraSpecPullbackIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraTensorFunctor

/-! # Algebra Spec Tensor Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraSpecTensorIso

noncomputable section

/-! The spectrum of a scalar-extended algebra is canonically the base change of its spectrum over the base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry TensorProduct

universe u

variable (C D : Type u) [CommRing C] [CommRing D] [Algebra C D]

def algebraSpecTensorIso (A : CommAlgCat.{u} C) :
    (algSpec (.of D)).obj (Opposite.op ((AlgebraTensorFunctor.algebraTensorFunctor C D).obj A)) ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C D)))).obj
      ((algSpec (.of C)).obj (Opposite.op A)) :=
  Over.isoMk (Tensor.ComparisonIso.naturalTensorProjection_isPullback (C := C) (R := D) (A := A)).isoPullback
    (Tensor.ComparisonIso.naturalTensorProjection_isPullback (C := C) (R := D) (A := A)).isoPullback_hom_snd

theorem algebraSpecTensorIso_hom_fst (A : CommAlgCat.{u} C) :
    (algebraSpecTensorIso C D A).hom.left ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap C A)))
        (Spec.map (CommRingCat.ofHom (algebraMap C D))) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := C) (A := D) (B := A)).toRingHom) :=
  (Tensor.ComparisonIso.naturalTensorProjection_isPullback (C := C) (R := D) (A := A)).isoPullback_hom_fst

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraSpecTensorIso
