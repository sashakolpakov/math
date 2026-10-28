import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RestrictionGlobalFrame
import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.RationalRestrictionResidue

/-! # Restriction Global Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RestrictionGlobalDivisor.Cycles

noncomputable section

/-! # LineBundleCycles: the actual restricted line-bundle divisor in a global frame is the ordinary restricted principal divisor -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable {X : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    {L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X} (e : L.sheaf ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule X)
    (a : X.functionFieldˣ) (x : X) (hx : coheight x = 1)
    [IsIntegrallyClosed (X.presheaf.stalk x)]
    (ha : L.rationalSectionPointDivisorWithCoefficient a x = 0)

theorem restrictedRationalSectionPointCycle_globalFrame :
    L.restrictedRationalSectionPointCycle a x hx ha =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm x)
        (RationalNormalUnitRestriction.BundleCycles.normalRationalRestriction X x hx (a * GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e)
          ((GlobalDivisor.Cycles.lineBundleGlobal_section_order e a x).symm.trans ha)).val := by
  change Finsupp.mapDomain (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x))
    ((L.pullback (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x))).rationalSectionPointCycleWithCoefficient
      (L.rationalSectionRestrictionCoefficient a x hx ha)) = _
  rw [GlobalDivisor.Cycles.lineBundleGlobal_section_pointCycle (PullbackIso.Cycles.lineBundlePullbackGlobalTrivialization e _),
    RestrictionGlobalFrame.Cycles.rationalSectionRestrictionCoefficient_globalFrame e a x hx ha]
  exact (Finsupp.embDomain_eq_mapDomain
    ⟨CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x),
      (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)).isClosedEmbedding.injective⟩ _).symm

theorem normalResidue_restrictedSection_globalFrame (g : X.functionFieldˣ) :
    Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm x)
        (Normal.PointResidue.BundleCycles.normalPointResidueFunction X x hx (a * GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e) g) =
      X.ord g.val x • L.restrictedRationalSectionPointCycle a x hx ha := by
  rw [restrictedRationalSectionPointCycle_globalFrame e a x hx ha]
  exact Normal.RationalRestrictionResidue.BundleCycles.normalResidue_principal_order_zero X x hx (a * GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e) g _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RestrictionGlobalDivisor.Cycles
