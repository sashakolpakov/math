import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportResidue
import OAI.AlgebraicGeometry.Divisors.LineBundles.DVRResidueNaturality
import OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChow

/-! # Residue Function -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.ResidueFunction.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual rational functions from codimension-one residue quotients

At a DVR point of an integral scheme, the local residue quotient becomes
an actual nonzero rational function on the reduced point closure. It is
independent of the local uniformizer. Its principal divisor is therefore
an actual relation in the dimension-graded Chow group.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme) [IsIntegral X]
variable (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)]
variable (π : X.presheaf.stalk x) (hπ : Irreducible π)

/-- The actual rational residue quotient on the geometric prime support. -/
def geometricResidueFunction (g h : X.functionFieldˣ) :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).functionField :=
  Point.SupportResidue.BundleCycles.pointSupportResidueFunction X x (DVRResidueOf.BundleCycles.dvrResidueQuotient π hπ g h)

theorem geometricResidueFunction_ne_zero (g h : X.functionFieldˣ) :
    geometricResidueFunction X x π hπ g h ≠ 0 :=
  Point.SupportResidue.BundleCycles.pointSupportResidueFunction_ne_zero X x _

theorem geometricResidueFunction_independent (ρ : X.presheaf.stalk x) (hρ : Irreducible ρ)
    (g h : X.functionFieldˣ) :
    geometricResidueFunction X x π hπ g h = geometricResidueFunction X x ρ hρ g h :=
  congrArg (Point.SupportResidue.BundleCycles.pointSupportResidueFunction X x) (DVRResidueOf.BundleCycles.dvrResidueQuotient_independent π hπ ρ hρ g h)

variable [AlgebraicGeometry.IsNoetherian X]

/-- The residue construction supplies a genuine principal-divisor relation on the support. -/
theorem geometricResidueFunction_principal_chow_zero (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ)
    (hx : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f = d + 1)
    (g h : X.functionFieldˣ) :
    DimensionChow.BundleCycles.dimensionCycleToChowQ f d
      (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d (irreducibleSetEquivPoints.symm x)
        (geometricResidueFunction X x π hπ g h)) = 0 :=
  DimensionChow.BundleCycles.dimensionCycleToChowQ_principal f d _ hx _ (geometricResidueFunction_ne_zero X x π hπ g h)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.ResidueFunction.BundleCycles
