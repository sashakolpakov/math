import OAI.AlgebraicGeometry.Divisors.LineBundles.FiniteSupport.Divisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.GenericRegularFunction

/-! # Support Regular Function -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportRegularFunction.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual section pullback and residue degree on maps of point closures
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (i : X ⟶ Y) (x : X)

theorem pointSupportMap_appTop :
    (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (i x))).appTop ≫ (SupportMap.BundleCycles.pointSupportMap i x).appTop =
      i.appTop ≫ (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)).appTop :=
  (Scheme.Hom.comp_appTop (SupportMap.BundleCycles.pointSupportMap i x)
    (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (i x)))).symm.trans
      ((congrArg Scheme.Hom.appTop (SupportMap.BundleCycles.pointSupportMap_inclusion i x)).trans
        (Scheme.Hom.comp_appTop (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)) i))

theorem pointSupportFunctionFieldMap_regular (a : Γ(Y, ⊤)) :
    SupportMap.BundleCycles.pointSupportFunctionFieldMap i x (Principal.CartierCycle.BundleCycles.supportRegularFunction a (irreducibleSetEquivPoints.symm (i x))) =
      Principal.CartierCycle.BundleCycles.supportRegularFunction (i.appTop a) (irreducibleSetEquivPoints.symm x) := by
  have hv := GenericRegularFunction.BundleCycles.genericFieldMap_globalFunction (SupportMap.BundleCycles.pointSupportMap i x)
    (SupportNaturality.BundleCycles.pointSupportMap_genericPoint i x (SupportMap.BundleCycles.pointSupportMap i x) (SupportMap.BundleCycles.pointSupportMap_inclusion i x))
    ((CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (i x))).appTop a)
  exact hv.trans (congrArg (RegularDivisor.BundleCycles.globalFunctionFieldElement (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)))
    (ConcreteCategory.congr_hom (pointSupportMap_appTop i x) a))

theorem pointSupportMap_residueDegree :
    (SupportMap.BundleCycles.pointSupportMap i x).residueDegree (genericPoint _) = i.residueDegree x := by
  have hc := congrArg
    (fun k : CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x) ⟶ Y => k.residueDegree (genericPoint _))
    (SupportMap.BundleCycles.pointSupportMap_inclusion i x)
  simpa only [IntersectionTheory.ProjectionFormula.CyclePushforward.residueDegree_comp, IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle.residueDegree_immersion,
    one_mul, mul_one, SupportNaturality.BundleCycles.pointSupport_genericPoint] using hc

theorem pointSupportFunctionFieldMap_finrank :
    letI := (SupportMap.BundleCycles.pointSupportFunctionFieldMap i x).hom.toAlgebra
    Module.finrank (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm (i x))).functionField
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).functionField = i.residueDegree x :=
  (IntersectionTheory.ProjectionFormula.Support.Fields.genericFieldMap_finrank_eq_residueDegree (SupportMap.BundleCycles.pointSupportMap i x)
    (SupportNaturality.BundleCycles.pointSupportMap_genericPoint i x (SupportMap.BundleCycles.pointSupportMap i x) (SupportMap.BundleCycles.pointSupportMap_inclusion i x))).trans
      (pointSupportMap_residueDegree i x)

theorem finitePointSupportNorm_regular [IsFinite i] (a : Γ(Y, ⊤)) :
    FiniteSupport.Divisor.BundleCycles.finitePointSupportNorm i x (Principal.CartierCycle.BundleCycles.supportRegularFunction (i.appTop a) (irreducibleSetEquivPoints.symm x)) =
      Principal.CartierCycle.BundleCycles.supportRegularFunction a (irreducibleSetEquivPoints.symm (i x)) ^ i.residueDegree x := by
  let := (SupportMap.BundleCycles.pointSupportFunctionFieldMap i x).hom.toAlgebra
  rw [← pointSupportFunctionFieldMap_regular i x a]
  change Algebra.norm (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm (i x))).functionField
    (algebraMap _ _ (Principal.CartierCycle.BundleCycles.supportRegularFunction a (irreducibleSetEquivPoints.symm (i x)))) = _
  rw [Algebra.norm_algebraMap, pointSupportFunctionFieldMap_finrank]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportRegularFunction.BundleCycles
