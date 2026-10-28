import OAI.AlgebraicTopology.Duality.Poincare.Property
import OAI.AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains
import OAI.AlgebraicGeometry.CycleClass.Geometric.Point

/-! # Empty -/

namespace OAI.AlgebraicTopology.Duality.Poincare.Empty

/-!
# Canonical Poincare duality on the empty space

Both groups of the canonical cap map vanish on an empty manifold. The
cohomology calculation uses the actual compact-support cochain complex; the
homology calculation uses the actual rational singular chain complex.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Compact-support singular cohomology of an empty space vanishes in every
degree and for every coefficient module. -/
theorem compactSupportedCohomology_isZero_of_isEmpty
    {R : Type} [CommRing R] (A : ModuleCat.{0} R)
    (X : TopCat.{0}) [IsEmpty X] (n : ℕ) :
    IsZero (CompactSupportCohomology.compactSupportedCohomology A X n) := by
  have h : IsZero (CompactSupportCohomology.compactSupportedCochains A X) :=
    (CompactSupportCohomology.singularCochains_isZero_of_isEmpty A X).of_iso
      (CompactSupportCohomology.compactSupportedCochainIso A X)
  exact (HomologicalComplex.homologyFunctor (ModuleCat.{0} R)
    (ComplexShape.up ℕ) n).map_isZero h

/-- Ordinary rational singular homology of an empty space vanishes. -/
theorem rationalSingularHomology_isZero_of_isEmpty
    (X : TopCat.{0}) [IsEmpty X] (n : ℕ) :
    IsZero ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n) := by
  have h : IsZero (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) :=
    ((AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules.mapHomologicalComplex (ComplexShape.down ℕ)).map_isZero
      (AlgebraicGeometry.CycleClass.Geometric.Point.Cycles.integralSingularChains_isZero_of_isEmpty X)).of_iso
        (AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso X).symm
  exact (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ)
    (ComplexShape.down ℕ) n).map_isZero h

/-- The full canonical cap-duality induction property holds for an empty
complex manifold, including every higher-degree vanishing assertion. -/
theorem hasCanonicalPoincareDuality_of_isEmpty
    (d : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M] [IsEmpty M] :
    Property.HasCanonicalPoincareDuality d M := by
  constructor
  · intro p q hpq
    exact (compactSupportedCohomology_isZero_of_isEmpty
      (ModuleCat.of ℚ ℚ) (TopCat.of M) p).isIso
      (rationalSingularHomology_isZero_of_isEmpty (TopCat.of M) q)
      (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) p q hpq)
  · intro p _
    exact compactSupportedCohomology_isZero_of_isEmpty
      (ModuleCat.of ℚ ℚ) (TopCat.of M) p

end OAI.AlgebraicTopology.Duality.Poincare.Empty
