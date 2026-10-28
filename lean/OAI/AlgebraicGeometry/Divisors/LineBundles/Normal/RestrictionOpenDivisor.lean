import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.RationalRestrictionNaturality
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportOpenCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportDivisorRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.FunctionFieldUnits

/-! # Restriction Open Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.RestrictionOpenDivisor.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual ordinary restricted principal divisors commute with open restriction -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (i : Y ⟶ X) [IsOpenImmersion i]

omit [IsIntegral X] [IsIntegral Y] [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y] in
include i in
theorem openNormalStructure (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y) := fun y =>
  letI := hNormal (i y)
  IsIntegrallyClosed.of_equiv (asIso (i.stalkMap y)).commRingCatIsoToRingEquiv

omit [IsIntegral X] [IsIntegral Y] in
theorem pointSupportPrincipalDivisor_open (y : Y)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm (i y))).functionField) :
    Finsupp.comapDomain i (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm (i y)) g)
        i.isOpenEmbedding.injective.injOn =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm y) (Point.SupportMap.BundleCycles.pointSupportFunctionFieldMap i y g) := by
  have hs : i ⁻¹' (irreducibleSetEquivPoints.symm (i y) : Set X) =
      (irreducibleSetEquivPoints.symm y : Set Y) :=
    (Open.SupportRestriction.BundleCycles.openRestrictedSupport_coe i (irreducibleSetEquivPoints.symm (i y))).symm.trans
      (congrArg (fun W : IrreducibleCloseds Y => (W : Set Y)) (Open.SupportGenericPoint.BundleCycles.openRestrictedSupport_pointClosure i y))
  exact Point.SupportDivisorRestriction.BundleCycles.pointSupportPrincipalDivisor_comap i y i.isOpenEmbedding.injective hs
    (fun _ => inferInstance) (fun _ => coheight_eq_of_isOpenImmersion (Point.SupportMap.BundleCycles.pointSupportMap i y)) g

theorem normalRationalRestriction_principal_open (y : Y) (hx : coheight (i y) = 1) (hy : coheight y = 1)
    [IsIntegrallyClosed (X.presheaf.stalk (i y))] [IsIntegrallyClosed (Y.presheaf.stalk y)]
    (g : X.functionFieldˣ) (hg : X.ord g.val (i y) = 0)
    (hg' : Y.ord (Open.FunctionFieldUnits.BundleCycles.openFunctionFieldUnits i g).val y = 0) :
    Finsupp.comapDomain i
        (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm (i y))
          (RationalNormalUnitRestriction.BundleCycles.normalRationalRestriction X (i y) hx g hg).val) i.isOpenEmbedding.injective.injOn =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm y)
        (RationalNormalUnitRestriction.BundleCycles.normalRationalRestriction Y y hy (Open.FunctionFieldUnits.BundleCycles.openFunctionFieldUnits i g) hg').val := by
  have hd := pointSupportPrincipalDivisor_open i y (RationalNormalUnitRestriction.BundleCycles.normalRationalRestriction X (i y) hx g hg).val
  have hr := RationalRestrictionNaturality.BundleCycles.normalRationalRestriction_morphism i (genericPoint_eq_of_isOpenImmersion i) y hy hx g hg hg'
  exact hd.trans (congrArg (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm y)) hr)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.RestrictionOpenDivisor.BundleCycles
