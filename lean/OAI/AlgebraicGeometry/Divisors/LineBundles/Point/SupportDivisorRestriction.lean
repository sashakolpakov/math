import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportMap
import OAI.AlgebraicGeometry.Divisors.LineBundles.MorphismOrderStalk
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.PrincipalRestriction

/-! # Support Divisor Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportDivisorRestriction.BundleCycles

noncomputable section

/-!
# LineBundleCycles: complete support-divisor restriction from actual local isomorphisms

The inclusion square and equality of underlying support sets identify
the coefficients that survive. The actual support-stalk isomorphisms
and preserved coheights identify their native rational orders.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable {X Y : Scheme} [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (f : X ⟶ Y) (x : X)

theorem pointSupportPrincipalDivisor_comap (hf : Function.Injective f)
    (hsupport : f ⁻¹' (irreducibleSetEquivPoints.symm (f x) : Set Y) =
      (irreducibleSetEquivPoints.symm x : Set X))
    [IsIso (SupportMap.BundleCycles.pointSupportFunctionFieldMap f x)]
    (hstalk : ∀ z : CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x),
      IsIso ((SupportMap.BundleCycles.pointSupportMap f x).stalkMap z))
    (hheight : ∀ z : CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x),
      coheight (SupportMap.BundleCycles.pointSupportMap f x z) = coheight z)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm (f x))).functionField) :
    Finsupp.comapDomain f (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm (f x)) g) hf.injOn =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm x) (SupportMap.BundleCycles.pointSupportFunctionFieldMap f x g) := by
  ext q
  by_cases hq : q ∈ (irreducibleSetEquivPoints.symm x : Set X)
  · have hr : q ∈ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)) := by
      rw [CycleClass.Geometric.GenericPoint.range_reducedSupportι]
      exact hq
    obtain ⟨z, rfl⟩ := hr
    have hp := congrArg (fun j => j z) (SupportMap.BundleCycles.pointSupportMap_inclusion f x)
    change CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (f x)) (SupportMap.BundleCycles.pointSupportMap f x z) =
      f (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x) z) at hp
    change Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm (f x)) g
        (f (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x) z)) = _
    rw [← hp, Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor_at_support, Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor_at_support]
    let : IsIso ((SupportMap.BundleCycles.pointSupportMap f x).stalkMap z) := hstalk z
    let hη := SupportNaturality.BundleCycles.pointSupportMap_genericPoint f x (SupportMap.BundleCycles.pointSupportMap f x) (SupportMap.BundleCycles.pointSupportMap_inclusion f x)
    let : IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (SupportMap.BundleCycles.pointSupportMap f x) hη) :=
      inferInstanceAs (IsIso (SupportMap.BundleCycles.pointSupportFunctionFieldMap f x))
    exact congrArg (fun n : ℤ => (n : ℚ))
      (MorphismOrderStalk.BundleCycles.ord_of_stalkMap_isIso (SupportMap.BundleCycles.pointSupportMap f x) hη z (hheight z) g).symm
  · have hq' : f q ∉ (irreducibleSetEquivPoints.symm (f x) : Set Y) := by
      intro h
      apply hq
      exact (congrArg (fun S : Set X => q ∈ S) hsupport).mp h
    exact (Open.PrincipalRestriction.BundleCycles.schemePrincipalPointDivisor_off_support (irreducibleSetEquivPoints.symm (f x)) g (f q) hq').trans
      (Open.PrincipalRestriction.BundleCycles.schemePrincipalPointDivisor_off_support (irreducibleSetEquivPoints.symm x)
        (SupportMap.BundleCycles.pointSupportFunctionFieldMap f x g) q hq).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportDivisorRestriction.BundleCycles
