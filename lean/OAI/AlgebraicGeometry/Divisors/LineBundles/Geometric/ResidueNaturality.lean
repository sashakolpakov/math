import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportMap
import OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.ResidueFunction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.PointResidue

/-! # Residue Naturality -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.ResidueNaturality.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual geometric residues under morphisms identifying local fields

The morphism's stalk isomorphism transports the characterized DVR
balanced unit. Naturality of the constructed point-support field map
then transports its residue as an actual rational function.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y)
    [IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη)] (x : X) [IsIso (f.stalkMap x)]

theorem geometricResidueFunction_morphism [IsDiscreteValuationRing (X.presheaf.stalk x)]
    [IsDiscreteValuationRing (Y.presheaf.stalk (f x))]
    (π : X.presheaf.stalk x) (hπ : Irreducible π)
    (ρ : Y.presheaf.stalk (f x)) (hρ : Irreducible ρ) (g h : Y.functionFieldˣ) :
    Point.SupportMap.BundleCycles.pointSupportFunctionFieldMap f x (ResidueFunction.BundleCycles.geometricResidueFunction Y (f x) ρ hρ g h) =
      ResidueFunction.BundleCycles.geometricResidueFunction X x π hπ
        (Units.map (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toMonoidHom g)
        (Units.map (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toMonoidHom h) := by
  let e := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  let φ := (asIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη)).commRingCatIsoToRingEquiv
  have he := DVRResidueNaturality.BundleCycles.dvrResidueQuotient_equiv e φ (RationalDivisorRestriction.BundleCycles.genericFieldMap_stalk f hη x) ρ hρ π hπ g h
  let rg : (Y.residueField (f x))ˣ := DVRResidueOf.BundleCycles.dvrResidueQuotient ρ hρ g h
  have hs := congrArg
    (fun k : Y.residueField (f x) ⟶ (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).functionField =>
      k (rg : Y.residueField (f x)))
    (Point.SupportMap.BundleCycles.pointSupportFunctionFieldMap_residue f x)
  exact hs.trans (congrArg (Point.SupportResidue.BundleCycles.pointSupportResidueFunction X x) he)

variable [AlgebraicGeometry.IsNoetherian Y]

theorem normalPointResidueFunction_morphism (hx : coheight x = 1) (hy : coheight (f x) = 1)
    [IsIntegrallyClosed (X.presheaf.stalk x)] [IsIntegrallyClosed (Y.presheaf.stalk (f x))]
    (g h : Y.functionFieldˣ) :
    Point.SupportMap.BundleCycles.pointSupportFunctionFieldMap f x (Normal.PointResidue.BundleCycles.normalPointResidueFunction Y (f x) hy g h) =
      Normal.PointResidue.BundleCycles.normalPointResidueFunction X x hx
        (Units.map (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toMonoidHom g)
        (Units.map (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toMonoidHom h) := by
  let := Normal.PointResidue.BundleCycles.normal_stalk_isDVR X x hx
  let := Normal.PointResidue.BundleCycles.normal_stalk_isDVR Y (f x) hy
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk x)
  obtain ⟨ρ, hρ⟩ := IsDiscreteValuationRing.exists_irreducible (Y.presheaf.stalk (f x))
  rw [Normal.PointResidue.BundleCycles.normalPointResidueFunction_eq Y (f x) hy ρ hρ,
    Normal.PointResidue.BundleCycles.normalPointResidueFunction_eq X x hx π hπ]
  exact geometricResidueFunction_morphism f hη x π hπ ρ hρ g h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.ResidueNaturality.BundleCycles
