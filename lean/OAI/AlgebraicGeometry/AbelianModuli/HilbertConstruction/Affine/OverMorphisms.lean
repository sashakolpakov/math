import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverChartPoints
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Over Morphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverMorphisms

noncomputable section

/-! Actual morphisms of affine schemes over the base give coordinate-algebra maps with exact recovery. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R]
variable {X Y : Over (Spec (.of R))} [IsAffine X.left] [IsAffine Y.left]

def affineOverMap (f : X ⟶ Y) : OverChartPoints.affineOverAlgebra R Y →ₐ[R] OverChartPoints.affineOverAlgebra R X :=
  ((algSpec.fullyFaithful (R := CommRingCat.of R)).preimage
    ((OverChartPoints.affineOverIso R X).inv ≫ f ≫ (OverChartPoints.affineOverIso R Y).hom)).unop.hom

theorem affineOverMap_spec (f : X ⟶ Y) :
    Spec.map (CommRingCat.ofHom (affineOverMap R f).toRingHom) =
      (OverChartPoints.affineOverIso R X).inv.left ≫ f.left ≫ (OverChartPoints.affineOverIso R Y).hom.left := by
  have h := (algSpec.fullyFaithful (R := CommRingCat.of R)).map_preimage
    ((OverChartPoints.affineOverIso R X).inv ≫ f ≫ (OverChartPoints.affineOverIso R Y).hom)
  exact congrArg (fun k => k.left) h

theorem affineOverMap_isOpenImmersion (f : X ⟶ Y) [IsOpenImmersion f.left] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (affineOverMap R f).toRingHom)) := by
  have : IsIso (OverChartPoints.affineOverIso R X).inv.left := (Over.forget _).map_isIso (OverChartPoints.affineOverIso R X).inv
  have : IsIso (OverChartPoints.affineOverIso R Y).hom.left := (Over.forget _).map_isIso (OverChartPoints.affineOverIso R Y).hom
  have : IsOpenImmersion (OverChartPoints.affineOverIso R X).inv.left := IsOpenImmersion.of_isIso _
  have : IsOpenImmersion (OverChartPoints.affineOverIso R Y).hom.left := IsOpenImmersion.of_isIso _
  have : IsOpenImmersion (f.left ≫ (OverChartPoints.affineOverIso R Y).hom.left) := IsOpenImmersion.comp _ _
  have hc : IsOpenImmersion ((OverChartPoints.affineOverIso R X).inv.left ≫ f.left ≫
      (OverChartPoints.affineOverIso R Y).hom.left) := IsOpenImmersion.comp _ _
  exact (congrArg (fun q : Spec (.of (OverChartPoints.affineOverAlgebra R X)) ⟶ Spec (.of (OverChartPoints.affineOverAlgebra R Y)) =>
    IsOpenImmersion q) (affineOverMap_spec R f)).mpr hc

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverMorphisms
