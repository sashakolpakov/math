import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverMorphisms

/-! # Coordinate Section Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.CoordinateSectionMap

noncomputable section

/-! The coordinate algebra homomorphism of an affine scheme map is
literally pullback on its original global sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k : Type) [CommRing k] {X Y : Over (Spec (.of k))}
    [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y)

theorem affineCoordinateMap_toRingHom : (HilbertConstruction.Affine.OverMorphisms.affineOverMap k f).toRingHom = f.left.appTop.hom := by
  have hs : Spec.map (CommRingCat.ofHom (HilbertConstruction.Affine.OverMorphisms.affineOverMap k f).toRingHom) = Spec.map f.left.appTop := by
    calc
      _ = X.left.isoSpec.inv ≫ f.left ≫ Y.left.isoSpec.hom := HilbertConstruction.Affine.OverMorphisms.affineOverMap_spec k f
      _ = _ := by
        rw [← Scheme.isoSpec_hom_naturality f.left]
        simp only [Iso.inv_hom_id_assoc]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective hs)

theorem affineCoordinateMap_apply (a : HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra k Y) :
    HilbertConstruction.Affine.OverMorphisms.affineOverMap k f a = f.left.appTop a :=
  RingHom.congr_fun (affineCoordinateMap_toRingHom k f) a

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.CoordinateSectionMap
