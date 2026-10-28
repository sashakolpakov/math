import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ComparisonIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.MapRealizationIso
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.AlgebraicGeometry.Group.Affine

/-! # Algebra Spec Pullback Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraSpecPullbackIso

noncomputable section

/-! A bijective scalar extension of an algebra map gives an isomorphism of the actual affine pullbacks. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry TensorProduct

universe u

theorem isIso_algebraSpec_pullback_of_tensor_bijective
    {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
    {A B : CommAlgCat.{u} C} (φ : A ⟶ B)
    (hφ : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R R) φ.hom)) :
    IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C R)))).map
      ((algSpec (.of C)).map φ.op)) := by
  let c := Spec.map (CommRingCat.ofHom (algebraMap C R))
  let f := (algSpec (.of C)).map φ.op
  let f' := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.map (AlgHom.id R R) φ.hom).toRingHom)
  have : IsIso f' := isIso_SpecMap_iff.mpr hφ
  have hk := HilbertConstruction.Pullback.MapRealizationIso.isIso_pullback_map_of_isIso_realization
    (Spec.map (CommRingCat.ofHom (algebraMap C B)))
    (Spec.map (CommRingCat.ofHom (algebraMap C A))) c f.left f.w
    _ _ _ _ (Tensor.ComparisonIso.naturalTensorProjection_isPullback (C := C) (R := R) (A := B))
    (Tensor.ComparisonIso.naturalTensorProjection_isPullback (C := C) (R := R) (A := A)) f'
    (NaturalTensorMapCartesian.naturalTensorMap_isPullback (R := R) φ.hom).w
    (Tensor.ComparisonIso.algebraSpecMap_over (Algebra.TensorProduct.map (AlgHom.id R R) φ.hom))
  have he : ((Over.pullback c).map f).left =
      pullback.map (Spec.map (CommRingCat.ofHom (algebraMap C B))) c (Spec.map (CommRingCat.ofHom (algebraMap C A))) c f.left (𝟙 _) (𝟙 _)
        ((Category.comp_id _).trans f.w.symm) (by simp) := by
    apply pullback.hom_ext <;> simp [Over.pullback_map_left, pullback.map] <;> rfl
  have hleft : IsIso ((Over.pullback c).map f).left := (congrArg IsIso he).mpr hk
  have : IsIso ((Over.forget (Spec (.of R))).map ((Over.pullback c).map f)) := hleft
  exact isIso_of_reflects_iso ((Over.pullback c).map f) (Over.forget _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AlgebraSpecPullbackIso
