import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

/-! # Birational Stalk -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.BirationalStalk.BundleCycles.BirationalStalkResidueDegree

noncomputable section

/-! Native residue degrees at points where the actual stalk map is an
isomorphism, in particular the closed point of the spectrum of a stalk. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem residueDegree_of_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    [IsIso (f.stalkMap x)] : f.residueDegree x = 1 := by
  let : IsIso (f.residueFieldMap x) :=
    (IsLocalRing.ResidueField.mapEquiv
      (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom
  let := (f.residueFieldMap x).hom.toAlgebra
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
    ((ConcreteCategory.isIso_iff_bijective (f.residueFieldMap x)).mp inferInstance)

theorem fromSpecStalk_stalkMap_isIso (X : Scheme.{u}) (x : X) :
    IsIso ((X.fromSpecStalk x).stalkMap (IsLocalRing.closedPoint (X.presheaf.stalk x))) := by
  have : IsIso (Scheme.stalkClosedPointTo (X.fromSpecStalk x)) := by
    rw [Scheme.stalkClosedPointTo_fromSpecStalk]
    infer_instance
  change IsIso (((X.fromSpecStalk x).stalkMap
    (IsLocalRing.closedPoint (X.presheaf.stalk x))) ≫
      (stalkClosedPointIso (X.presheaf.stalk x)).hom) at this
  exact IsIso.of_isIso_comp_right
    ((X.fromSpecStalk x).stalkMap (IsLocalRing.closedPoint (X.presheaf.stalk x)))
    (stalkClosedPointIso (X.presheaf.stalk x)).hom

theorem fromSpecStalk_residueDegree (X : Scheme.{u}) (x : X) :
    (X.fromSpecStalk x).residueDegree (IsLocalRing.closedPoint (X.presheaf.stalk x)) = 1 := by
  let := fromSpecStalk_stalkMap_isIso X x
  exact residueDegree_of_isIso_stalkMap _ _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.BirationalStalk.BundleCycles.BirationalStalkResidueDegree
