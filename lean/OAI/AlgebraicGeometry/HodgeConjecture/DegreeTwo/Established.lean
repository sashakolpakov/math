import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Chern
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph
import OAI.AlgebraicGeometry.Albanese.Construction.Mon
import OAI.AlgebraicGeometry.Albanese.HodgeComparisonIs
import OAI.AlgebraicGeometry.DivisorClass.Chern.Lefschetz

/-! # Established -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Established.Constructions

/-!
# DegreeTwo: proved instances of the complete upstream propositions

The input propositions remain available to the existing conditional proofs.
These theorems discharge them using the actual unconditional HolomorphicAlgebraicity–ChernClass proofs.
The HodgeComparison adapters identify the complete pointed universal property and both
canonical Hodge pieces. The geometric adapter uses the same algebraic line
bundle and the independently defined class of its original divisor.
-/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.CM

/-- The exact HolomorphicAlgebraicity input follows from the proved algebraization theorem. -/
theorem e06Input : Transport.Constructions.HolomorphicAlgebraicityInput :=
  ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.CM.holomorphic_group_hom_is_algebraic

/-- The exact Construction input includes the original pointed universal property. -/
theorem e07Input : Transport.Constructions.ConstructionInput :=
  Albanese.Construction.Mon.exists_albanese

/-- DegreeTwo and HodgeComparison use the same complete pointed Albanese property. -/
theorem isAlbaneseMap_iff_e08 (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : 𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver) :
    Transport.Constructions.IsAlbaneseMap X x₀ A a ↔ Albanese.HodgeComparisonIs.CM.Construction.IsAlbaneseMap X x₀ A a :=
  Iff.rfl

/-- DegreeTwo and HodgeComparison identify both Hodge pieces by the same complexification. -/
theorem isCanonicalH1_iff_e08 (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (V.rationalCohomology 1)) :
    Transport.Constructions.IsCanonicalH1 V H ↔ Albanese.HodgeComparisonIs.CM.Construction.IsCanonicalH1 V H :=
  Iff.rfl

/-- HodgeComparison supplies the actual rational pullback and its Hodge-preserving inverse. -/
theorem e08Input : Transport.Constructions.HodgeComparisonInput := by
  intro X x₀ A a ha
  obtain ⟨HA, HX, e, hA, hX, he, hh, hi⟩ :=
    Albanese.HodgeComparisonIs.CM.Construction.albanese_h1_hodge_iso X x₀ A a
      ((isAlbaneseMap_iff_e08 X x₀ A a).mp ha)
  exact ⟨HA, HX, e, (isCanonicalH1_iff_e08 A.variety HA).mpr hA,
    (isCanonicalH1_iff_e08 X HX).mpr hX, he, hh, hi⟩

/-- The exact full ChernClass Lefschetz proposition is now proved. -/
theorem e09Input : Chern.Constructions.ChernClassInput :=
  DivisorClass.Chern.Lefschetz.lefschetz_one_one

/-- The original divisor class of an algebraic line bundle has an actual
geometric codimension-one cycle representative in DegreeTwo's cycle type. -/
theorem algebraicDivisorClass_is_geometric (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (L : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle V.presentation) :
    ∃ z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle V 1,
      V.geometricCycleClassMap 1 z = L.algebraicDivisorClass := by
  obtain ⟨z, hz⟩ := ChernGeometric.Constructions.firstChernClassQ_is_geometric V L
  exact ⟨z, hz.trans L.firstChernClassQ_eq_algebraicDivisorClass⟩

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Established.Constructions
