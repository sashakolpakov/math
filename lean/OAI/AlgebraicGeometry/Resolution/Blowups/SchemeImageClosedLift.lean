import OAI.AlgebraicGeometry.Resolution.Blowups.Integral.SchemeImage

/-! # Scheme Image Closed Lift -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.SchemeImageClosedLift.Construction

noncomputable section

/-! A commuting map into a closed subscheme descends to the actual scheme image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem schemeImage_closed_kernel_le {V Z Y X : Scheme.{u}}
    (j : V ⟶ Y) (k : V ⟶ Z) (π : Y ⟶ X) (i : Z ⟶ X)
    (h : j ≫ π = k ≫ i) : i.ker.comap π ≤ j.ker := by
  apply Scheme.IdealSheafData.le_map_iff_comap_le.mp
  rw [Scheme.IdealSheafData.map_ker, h]
  exact Scheme.Hom.le_ker_comp k i

def schemeImageClosedLift {V Z Y X : Scheme.{u}}
    (j : V ⟶ Y) (k : V ⟶ Z) (π : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (h : j ≫ π = k ≫ i) : j.image ⟶ Z :=
  ClosedTransformMap.Construction.closedTransformMap π i.ker j.ker (schemeImage_closed_kernel_le j k π i h) ≫ inv i.toImage

theorem schemeImageClosedLift_over {V Z Y X : Scheme.{u}}
    (j : V ⟶ Y) (k : V ⟶ Z) (π : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (h : j ≫ π = k ≫ i) :
    schemeImageClosedLift j k π i h ≫ i = j.imageι ≫ π := by
  have hi : inv i.toImage ≫ i = i.imageι :=
    (IsIso.inv_comp_eq i.toImage).mpr i.toImage_imageι.symm
  rw [schemeImageClosedLift, Category.assoc, hi]
  exact ClosedTransformMap.Construction.closedTransformMap_over π i.ker j.ker _

theorem schemeImageClosedLift_toImage {V Z Y X : Scheme.{u}}
    (j : V ⟶ Y) (k : V ⟶ Z) (π : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (h : j ≫ π = k ≫ i) :
    j.toImage ≫ schemeImageClosedLift j k π i h = k := by
  apply (cancel_mono i).mp
  rw [Category.assoc, schemeImageClosedLift_over, ← Category.assoc, j.toImage_imageι, h]

theorem schemeImageClosedLift_isProper {V Z Y X : Scheme.{u}}
    (j : V ⟶ Y) (k : V ⟶ Z) (π : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] [IsProper π] (h : j ≫ π = k ≫ i) :
    IsProper (schemeImageClosedLift j k π i h) := by
  let : IsProper (schemeImageClosedLift j k π i h ≫ i) :=
    (schemeImageClosedLift_over j k π i h).symm ▸ inferInstanceAs (IsProper (j.imageι ≫ π))
  exact IsProper.of_comp _ i

end

end OAI.AlgebraicGeometry.Resolution.Blowups.SchemeImageClosedLift.Construction
