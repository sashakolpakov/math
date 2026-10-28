import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.CanonicalRationalRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GenericCoefficientGlobalFrame
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GlobalDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.RationalRestrictionOpenRegular

/-! # Restriction Global Frame -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RestrictionGlobalFrame.Cycles

noncomputable section

/-! # LineBundleCycles: the actual restricted rational section agrees with ordinary restriction in every global frame -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable {X : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    {L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X} (e : L.sheaf ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule X)
    (a : X.functionFieldˣ) (x : X) (hx : coheight x = 1)
    [IsIntegrallyClosed (X.presheaf.stalk x)]

theorem rationalSectionUnitNeighborhood_globalFrame
    (D : L.RationalSectionUnitNeighborhood a x)
    (hb : X.ord (a * GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e).val x = 0) :
    D.restrictionCoefficient * GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient
        (PullbackIso.Cycles.lineBundlePullbackGlobalTrivialization e (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x))) =
      RationalNormalUnitRestriction.BundleCycles.normalRationalRestriction X x hx (a * GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e) hb := by
  let i := CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)
  let Z := CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)
  let ep := PullbackIso.Cycles.lineBundlePullbackGlobalTrivialization e i
  let r := GlobalFrame.Cycles.lineBundleGlobalFrame e D.openSet D.localSection
  have hr : IsUnit r := GenericCoefficientGlobalFrame.Cycles.lineBundleGlobalFrame_isUnit_of_localFrame e x D.openSet D.subordinate
    D.localSection (D.localSection_coordinate.symm ▸ D.unit.isUnit)
  have hc : L.genericSectionCoefficient D.openSet D.localSection = a.val :=
    (L.genericSectionCoefficient_eq_local x D.openSet D.subordinate D.localSection).trans D.localSection_coefficient
  have hg : (a * GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e).val = X.germToFunctionField D.openSet r := by
    rw [GenericCoefficientGlobalFrame.Cycles.genericSectionCoefficient_globalFrame e, hc]
    exact mul_comm _ _
  have hn := Normal.RationalRestrictionOpenRegular.BundleCycles.normalRationalRestriction_openRegular X x hx
    (a * GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e) hb D.openSet D.point_mem r
    (hr.map (X.presheaf.germ D.openSet x D.point_mem).hom) hg
  have hp := Module.PullbackUnitSections.BundleCycles.lineBundlePullbackGlobalTrivialization_section i e D.openSet D.localSection
  have hpg := GenericCoefficientGlobalFrame.Cycles.genericSectionCoefficient_globalFrame ep (i ⁻¹ᵁ D.openSet)
    (Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen i L.sheaf D.openSet D.localSection)
  have hv : Z.germToFunctionField (i ⁻¹ᵁ D.openSet) (i.app D.openSet r) =
      (GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient ep).val * D.restrictionCoefficient.val :=
    (congrArg (Z.germToFunctionField (i ⁻¹ᵁ D.openSet)) hp).symm.trans hpg
  apply Units.ext
  change D.restrictionCoefficient.val * (GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient ep).val = _
  exact (mul_comm _ _).trans (hv.symm.trans hn.symm)

theorem rationalSectionRestrictionCoefficient_globalFrame
    (ha : L.rationalSectionPointDivisorWithCoefficient a x = 0) :
    L.rationalSectionRestrictionCoefficient a x hx ha * GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient
        (PullbackIso.Cycles.lineBundlePullbackGlobalTrivialization e (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x))) =
      RationalNormalUnitRestriction.BundleCycles.normalRationalRestriction X x hx (a * GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e)
        ((GlobalDivisor.Cycles.lineBundleGlobal_section_order e a x).symm.trans ha) := by
  let D := Classical.choice (L.rationalSectionUnitNeighborhood_nonempty a x hx ha)
  rw [L.rationalSectionRestrictionCoefficient_eq a x hx ha D]
  exact rationalSectionUnitNeighborhood_globalFrame e a x hx D _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RestrictionGlobalFrame.Cycles
