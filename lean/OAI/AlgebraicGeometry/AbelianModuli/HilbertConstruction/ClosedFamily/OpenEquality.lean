import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.LocalEquality

/-! # Open Equality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Ideal-defined families are determined by their restrictions to arbitrary open covers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X S : Scheme.{u}}

/-- Equality of ideal sheaves is local on any open cover. -/
theorem ClosedFamily.OpenEquality.ideal_eq_of_open_cover (C : Scheme.OpenCover.{v} X)
    (I J : X.IdealSheafData) (h : ∀ i, I.comap (C.f i) = J.comap (C.f i)) : I = J := by
  apply ClosedFamily.LocalEquality.ideal_eq_of_affine_cover C.affineRefinement
  intro i
  change I.comap ((C.X i.1).affineCover.f i.2 ≫ C.f i.1) =
    J.comap ((C.X i.1).affineCover.f i.2 ≫ C.f i.1)
  rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, h i.1]

/-- The actual flat closed family is determined by any open cover of its ambient scheme. -/
theorem Closed.Families.FlatClosedFamily.ext_on_open_cover {P : Over S} (F G : Closed.Families.FlatClosedFamily P)
    (C : Scheme.OpenCover.{v} P.left)
    (h : ∀ i, F.ideal.comap (C.f i) = G.ideal.comap (C.f i)) : F = G :=
  Closed.Families.FlatClosedFamily.ext (ClosedFamily.OpenEquality.ideal_eq_of_open_cover C F.ideal G.ideal h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
