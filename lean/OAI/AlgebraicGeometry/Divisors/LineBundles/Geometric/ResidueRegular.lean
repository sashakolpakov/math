import OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.ResidueFunction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportResidueEvaluation

/-! # Residue Regular -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.ResidueRegular.BundleCycles

noncomputable section

/-!
# LineBundleCycles: geometric residue functions for actual regular representatives

If a rational function is represented by a local unit coming from a
regular section, the geometric residue function is the actual restriction
of that section raised to the other function's existing Scheme.ord.
This identifies the residue construction with the proper-component term.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable (X : Scheme) (x : X)

theorem pointSupportResidueFunction_regular (a : Γ(X, ⊤)) (u : (X.presheaf.stalk x)ˣ)
    (hu : (u : X.presheaf.stalk x) = X.presheaf.germ ⊤ x (by trivial) a) :
    Point.SupportResidue.BundleCycles.pointSupportResidueFunction X x (Units.map (IsLocalRing.residue (X.presheaf.stalk x)).toMonoidHom u) =
      RegularDivisor.BundleCycles.globalFunctionFieldElement (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x))
        ((CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)).appTop a) := by
  change (Point.SupportResidue.BundleCycles.pointSupportResidueIso X x).hom
    (IsLocalRing.residue (X.presheaf.stalk x) (u : X.presheaf.stalk x)) = _
  rw [hu]
  exact Point.SupportResidueEvaluation.BundleCycles.pointSupportResidueIso_globalEvaluation X x a

variable [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
variable [IsDiscreteValuationRing (X.presheaf.stalk x)]
variable (π : X.presheaf.stalk x) (hπ : Irreducible π)

theorem geometricResidueFunction_regular (hx : coheight x = 1)
    (a : Γ(X, ⊤)) (u : (X.presheaf.stalk x)ˣ)
    (hu : (u : X.presheaf.stalk x) = X.presheaf.germ ⊤ x (by trivial) a) (h : X.functionFieldˣ) :
    ResidueFunction.BundleCycles.geometricResidueFunction X x π hπ
      (Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom u) h =
      (RegularDivisor.BundleCycles.globalFunctionFieldElement (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x))
        ((CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)).appTop a)) ^ X.ord (h : X.functionField) x := by
  have he := pointSupportResidueFunction_regular X x a u hu
  have ho : X.ord (h : X.functionField) x = SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder (X.presheaf.stalk x) (h : X.functionField) :=
    X.ord_eq_ordHom_of_coheight_eq_one hx _
  unfold ResidueFunction.BundleCycles.geometricResidueFunction
  rw [DVRResidueRegularSteinberg.BundleCycles.dvrResidueQuotient_localUnit]
  unfold Point.SupportResidue.BundleCycles.pointSupportResidueFunction
  rw [Units.val_zpow_eq_zpow_val]
  change (Point.SupportResidue.BundleCycles.pointSupportResidueIso X x).hom
    ((IsLocalRing.residue (X.presheaf.stalk x) (u : X.presheaf.stalk x)) ^
      SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder (X.presheaf.stalk x) (h : X.functionField)) = _
  exact (map_zpow₀ (Point.SupportResidue.BundleCycles.pointSupportResidueIso X x).hom.hom
    (show X.residueField x from IsLocalRing.residue (X.presheaf.stalk x) (u : X.presheaf.stalk x))
    (SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder (X.presheaf.stalk x) (h : X.functionField))).trans
      (congrArg₂ (fun z n => z ^ n) he ho.symm)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.ResidueRegular.BundleCycles
