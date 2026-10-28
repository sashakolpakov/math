import Mathlib.AlgebraicGeometry.ResidueField

/-! # Residue Field Square -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ResidueFieldSquare.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual residue-field square with identified points -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

theorem residueFieldMap_point_square {A B X Y : Scheme.{u}}
    (i : A ⟶ X) (j : B ⟶ Y) (f : X ⟶ Y) (r : A ⟶ B)
    (hr : r ≫ j = i ≫ f) (a : A) (b : B) (x : X)
    (ha : i a = x) (hb : j b = f x) (hab : r a = b) :
    (Y.residueFieldCongr hb.symm).hom ≫ j.residueFieldMap b ≫
      (B.residueFieldCongr hab.symm).hom ≫ r.residueFieldMap a =
      f.residueFieldMap x ≫ (X.residueFieldCongr ha.symm).hom ≫ i.residueFieldMap a := by
  subst x
  subst b
  simp only [Scheme.residueFieldCongr_refl, Iso.refl_hom, Category.id_comp]
  rw [← Scheme.residueFieldMap_comp, ← Scheme.residueFieldMap_comp]
  rw [Scheme.Hom.residueFieldMap_congr hr a]
  change (Y.residueFieldCongr hb).inv ≫ (Y.residueFieldCongr hb).hom ≫
    (i ≫ f).residueFieldMap a = (i ≫ f).residueFieldMap a
  exact Iso.inv_hom_id_assoc (Y.residueFieldCongr hb) _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ResidueFieldSquare.BundleCycles
