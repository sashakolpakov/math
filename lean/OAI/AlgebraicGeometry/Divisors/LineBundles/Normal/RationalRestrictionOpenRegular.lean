import OAI.AlgebraicGeometry.Divisors.LineBundles.RationalNormalUnitRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportOpenEvaluation

/-! # Rational Restriction Open Regular -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.RationalRestrictionOpenRegular.BundleCycles

noncomputable section

/-! # LineBundleCycles: ordinary rational restriction agrees with evaluation of any actual local representative -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (x : X) (hx : coheight x = 1) [IsIntegrallyClosed (X.presheaf.stalk x)]

theorem normalRationalRestriction_openRegular (g : X.functionFieldˣ) (hg : X.ord g.val x = 0)
    (U : X.Opens) [Nonempty U] (hxU : x ∈ U) (a : Γ(X, U))
    (ha : IsUnit (X.presheaf.germ U x hxU a))
    (hga : g.val = X.germToFunctionField U a) :
    letI := Point.SupportOpenEvaluation.BundleCycles.pointSupportPreimage_nonempty X x U hxU
    (RationalNormalUnitRestriction.BundleCycles.normalRationalRestriction X x hx g hg).val =
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).germToFunctionField
        ((CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)) ⁻¹ᵁ U)
        ((CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)).app U a) := by
  let := Point.SupportOpenEvaluation.BundleCycles.pointSupportPreimage_nonempty X x U hxU
  obtain ⟨u, hu⟩ := ha
  have huf : Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom u = g := by
    apply Units.ext
    change algebraMap (X.presheaf.stalk x) X.functionField u.val = g.val
    rw [hu, Scheme.algebraMap_germ_eq_germToFunctionField X hxU a]
    exact hga.symm
  have he : (RationalNormalUnitRestriction.BundleCycles.normalRationalRestriction X x hx g hg).val =
      (Point.SupportResidue.BundleCycles.pointSupportResidueIso X x).hom (X.evaluation U x hxU a) := by
    unfold RationalNormalUnitRestriction.BundleCycles.normalRationalRestriction
    rw [← RationalNormalUnitRestriction.BundleCycles.normalOrderZeroUnit_unique X x hx g hg u huf]
    change (Point.SupportResidue.BundleCycles.pointSupportResidueIso X x).hom
      (IsLocalRing.residue (X.presheaf.stalk x) u.val) = _
    rw [hu]
    rfl
  exact he.trans (Point.SupportOpenEvaluation.BundleCycles.pointSupportResidueIso_openEvaluation X x U hxU a)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.RationalRestrictionOpenRegular.BundleCycles
