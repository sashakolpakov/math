import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportResidue
import OAI.AlgebraicGeometry.Divisors.LineBundles.RegularDivisor

/-! # Support Residue Evaluation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportResidueEvaluation.BundleCycles

noncomputable section

/-!
# LineBundleCycles: residue functions recover actual restrictions of regular functions

Under the residue-field/function-field isomorphism for a reduced point
closure, evaluating a global regular function gives its actual pullback
to the support and then its rational function. This connects the residue
construction to restriction of regular representatives.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u
variable (X : Scheme.{u})

theorem residueFieldCongr_globalEvaluation {x y : X} (h : x = y) (a : Γ(X, ⊤)) :
    (X.residueFieldCongr h).hom (X.Γevaluation x a) = X.Γevaluation y a := by
  subst h
  rfl

theorem pointSupportResidueIso_globalEvaluation (x : X) (a : Γ(X, ⊤)) :
    (SupportResidue.BundleCycles.pointSupportResidueIso X x).hom (X.Γevaluation x a) =
      RegularDivisor.BundleCycles.globalFunctionFieldElement (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x))
        ((CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)).appTop a) := by
  let W := irreducibleSetEquivPoints.symm x
  let Y := CycleClass.Geometric.GenericPoint.reducedSupportScheme W
  let i := CycleClass.Geometric.GenericPoint.reducedSupportι W
  have hx : i (genericPoint Y) = x :=
    (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W).trans (irreducibleSetEquivPoints.apply_symm_apply x)
  change (Cycles.Functoriality.ResidueDegree.Construction.functionFieldResidueIso Y).inv
      ((Foundations.Scheme.ImmersionComplexPoints.residueFieldIsoOfSurjectiveOnStalks i (genericPoint Y)).hom
        ((X.residueFieldCongr hx.symm).hom (X.Γevaluation x a))) = _
  rw [residueFieldCongr_globalEvaluation, Foundations.Scheme.ImmersionComplexPoints.residueFieldIsoOfSurjectiveOnStalks_hom,
    Scheme.Γevaluation_naturality_apply]
  have he : Y.Γevaluation (genericPoint Y) (i.appTop a) =
      (Cycles.Functoriality.ResidueDegree.Construction.functionFieldResidueIso Y).hom (RegularDivisor.BundleCycles.globalFunctionFieldElement Y (i.appTop a)) := rfl
  rw [he]
  exact ConcreteCategory.congr_hom (Cycles.Functoriality.ResidueDegree.Construction.functionFieldResidueIso Y).hom_inv_id _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportResidueEvaluation.BundleCycles
