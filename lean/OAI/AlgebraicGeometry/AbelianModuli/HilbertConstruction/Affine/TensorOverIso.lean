import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TensorProjectionNaturality
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Tensor Over Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TensorOverIso

noncomputable section

/-! Tensor coordinate schemes are canonically isomorphic, over the new base, to actual affine base changes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry TensorProduct

universe u

variable (C R : Type u) [CommRing C] [CommRing R] [Algebra C R]

abbrev affineTensorOver (X : Over (Spec (.of C))) [IsAffine X.left] : Over (Spec (.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[C] OverChartPoints.affineOverAlgebra C X))))

def affineTensorOverMap {X Y : Over (Spec (.of C))} [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y) :
    affineTensorOver C R X ⟶ affineTensorOver C R Y :=
  Over.homMk (Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.map (AlgHom.id R R) (OverMorphisms.affineOverMap C f)).toRingHom))
    (Tensor.ComparisonIso.algebraSpecMap_over (Algebra.TensorProduct.map (AlgHom.id R R) (OverMorphisms.affineOverMap C f)))

def affineTensorOverIso (X : Over (Spec (.of C))) [IsAffine X.left] :
    affineTensorOver C R X ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C R)))).obj X :=
  Over.isoMk (TensorProjection.affineTensorProjection_isPullback C R X).isoPullback
    (TensorProjection.affineTensorProjection_isPullback C R X).isoPullback_hom_snd

theorem affineTensorOverIso_hom_fst (X : Over (Spec (.of C))) [IsAffine X.left] :
    (affineTensorOverIso C R X).hom.left ≫ pullback.fst X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap C R))) = TensorProjection.affineTensorProjection C R X :=
  (TensorProjection.affineTensorProjection_isPullback C R X).isoPullback_hom_fst

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TensorOverIso
