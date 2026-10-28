import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.CanonicalRationalRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.PullbackGenericIndependence
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportOpenEvaluation

/-! # Restriction Regular Representative -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-! # LineBundleCycles: every actual regular representative computes the canonical restriction to a prime support -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable {X : Scheme.{0}} [IsIntegral X] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (a : X.functionFieldˣ) (x : X)

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.RationalSectionUnitNeighborhood.restrictionCoefficient_regular
    (D : L.RationalSectionUnitNeighborhood a x)
    (U : X.Opens) [Nonempty U] (hxU : x ∈ U) (s : Γ(L.sheaf, U))
    (hs : L.genericSectionCoefficient U s = a.val) :
    letI := Point.SupportOpenEvaluation.BundleCycles.pointSupportPreimage_nonempty X x U hxU
    D.restrictionCoefficient.val =
      (L.pullback (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x))).genericSectionCoefficient
        ((CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)) ⁻¹ᵁ U)
        (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)) L.sheaf U s) := by
  let := Point.SupportOpenEvaluation.BundleCycles.pointSupportPreimage_nonempty X x U hxU
  exact LineBundle.PullbackGenericIndependence.Cycles.lineBundlePullback_genericCoefficient_eq (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)) L
    D.openSet U D.localSection s
    (((L.genericSectionCoefficient_eq_local x D.openSet D.subordinate D.localSection).trans
      D.localSection_coefficient).trans hs.symm)

variable [AlgebraicGeometry.IsNoetherian X]

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionRestrictionCoefficient_regular (hx : coheight x = 1)
    [IsIntegrallyClosed (X.presheaf.stalk x)]
    (ha : L.rationalSectionPointDivisorWithCoefficient a x = 0)
    (U : X.Opens) [Nonempty U] (hxU : x ∈ U) (s : Γ(L.sheaf, U))
    (hs : L.genericSectionCoefficient U s = a.val) :
    letI := Point.SupportOpenEvaluation.BundleCycles.pointSupportPreimage_nonempty X x U hxU
    (L.rationalSectionRestrictionCoefficient a x hx ha).val =
      (L.pullback (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x))).genericSectionCoefficient
        ((CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)) ⁻¹ᵁ U)
        (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)) L.sheaf U s) :=
  LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.RationalSectionUnitNeighborhood.restrictionCoefficient_regular L a x
    (Classical.choice (L.rationalSectionUnitNeighborhood_nonempty a x hx ha)) U hxU s hs

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
