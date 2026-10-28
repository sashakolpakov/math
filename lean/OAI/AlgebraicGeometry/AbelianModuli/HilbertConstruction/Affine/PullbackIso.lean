import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TensorProjectionNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.MapRealizationIso
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Pullback Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PullbackIso

noncomputable section

/-! Bijectivity of the coordinate tensor map implies an isomorphism of actual base-changed affine schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry TensorProduct

universe u

theorem isIso_affine_pullback_of_tensor_bijective
    {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
    {X Y : Over (Spec (.of C))} [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y)
    (hf : Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R R) (OverMorphisms.affineOverMap C f))) :
    IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C R)))).map f) := by
  let c := Spec.map (CommRingCat.ofHom (algebraMap C R))
  let f' := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.map (AlgHom.id R R) (OverMorphisms.affineOverMap C f)).toRingHom)
  have : IsIso f' := isIso_SpecMap_iff.mpr hf
  have hk := HilbertConstruction.Pullback.MapRealizationIso.isIso_pullback_map_of_isIso_realization X.hom Y.hom c f.left f.w
    (TensorProjection.affineTensorProjection C R X) (TensorProjection.affineTensorProjection C R Y) _ _
    (TensorProjection.affineTensorProjection_isPullback C R X) (TensorProjection.affineTensorProjection_isPullback C R Y)
    f' (TensorProjectionNaturality.affineTensorProjection_natural R f)
    (Tensor.ComparisonIso.algebraSpecMap_over (Algebra.TensorProduct.map (AlgHom.id R R) (OverMorphisms.affineOverMap C f)))
  have he : ((Over.pullback c).map f).left =
      pullback.map X.hom c Y.hom c f.left (𝟙 _) (𝟙 _)
        ((Category.comp_id X.hom).trans f.w.symm) (by simp) := by
    apply pullback.hom_ext <;> simp [Over.pullback_map_left, pullback.map]
  have hleft : IsIso ((Over.pullback c).map f).left := (congrArg IsIso he).mpr hk
  have : IsIso ((Over.forget (Spec (.of R))).map ((Over.pullback c).map f)) := hleft
  exact isIso_of_reflects_iso ((Over.pullback c).map f) (Over.forget _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PullbackIso
