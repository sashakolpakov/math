import OAI.AlgebraicGeometry.Cycles.Functoriality.ResidueDegree
import OAI.AlgebraicGeometry.CycleClass.Geometric.GenericPoint

/-! # Support Residue -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportResidue.BundleCycles

noncomputable section

/-!
# LineBundleCycles: a point's residue field is the function field of its reduced closure

The closed immersion of the reduced point closure identifies the residue
fields at its generic point. Composing with the generic-stalk residue
isomorphism gives the actual field isomorphism needed to regard a local
residue quotient as a rational function on the prime support.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u
variable (X : Scheme.{u}) (x : X)

def pointSupportResidueIso :
    X.residueField x ≅ (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).functionField := by
  let W := irreducibleSetEquivPoints.symm x
  have hx : CycleClass.Geometric.GenericPoint.reducedSupportι W (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) = x :=
    (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W).trans (irreducibleSetEquivPoints.apply_symm_apply x)
  exact (X.residueFieldCongr hx.symm) ≪≫
    Foundations.Scheme.ImmersionComplexPoints.residueFieldIsoOfSurjectiveOnStalks (CycleClass.Geometric.GenericPoint.reducedSupportι W) (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) ≪≫
      (Cycles.Functoriality.ResidueDegree.Construction.functionFieldResidueIso (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)).symm

/-- A nonzero residue is an actual nonzero rational function on the reduced point closure. -/
def pointSupportResidueFunction (r : (X.residueField x)ˣ) :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).functionField :=
  (pointSupportResidueIso X x).hom (r : X.residueField x)

theorem pointSupportResidueFunction_ne_zero (r : (X.residueField x)ˣ) :
    pointSupportResidueFunction X x r ≠ 0 :=
  (map_ne_zero_iff _ (ConcreteCategory.bijective_of_isIso (pointSupportResidueIso X x).hom).1).mpr r.ne_zero

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportResidue.BundleCycles
