import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverMorphisms
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Coordinate Finite Type -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoordinateFiniteType

noncomputable section

/-! Finite type of an affine scheme over a spectrum gives finite type of its coordinate algebra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem affineOverAlgebra_finiteType (C : Type u) [CommRing C]
    (X : Over (Spec (.of C))) [IsAffine X.left] [LocallyOfFiniteType X.hom] :
    Algebra.FiniteType C (OverChartPoints.affineOverAlgebra C X) := by
  let e := OverChartPoints.affineOverIso C X
  have : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
  have hs : LocallyOfFiniteType (e.inv.left ≫ X.hom) := inferInstance
  have he : e.inv.left ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap C (OverChartPoints.affineOverAlgebra C X))) := e.inv.w
  have h : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap C (OverChartPoints.affineOverAlgebra C X)))) :=
    (congrArg LocallyOfFiniteType he).mp hs
  exact RingHom.finiteType_algebraMap.mp (HasRingHomProperty.Spec_iff.mp h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoordinateFiniteType
