import OAI.AlgebraicGeometry.HodgeConjecture.GeometricNormalization
import OAI.Geometry.ComplexTorus.RiemannProjectivity.Realization
import OAI.AlgebraicGeometry.AbelianVariety.ExteriorCohomology
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.ChowNaturality
import OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.GraphPullback
import OAI.AlgebraicGeometry.CycleClass.Thom.Exterior
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph
import OAI.AlgebraicGeometry.Albanese.Construction.Mon
import OAI.AlgebraicGeometry.Albanese.HodgeComparisonIs
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicWeight
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Chern

/-! # Intrinsic Composition -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.IntrinsicComposition.LefschetzNormalization.Geometry

noncomputable section

/-!
# Native composition for LefschetzNormalization

The actual CM realizations and all tensor/cycle interface laws are constructed.
RiemannProjectivity, ScalarDescent, HolomorphicAlgebraicity, Construction, HodgeComparison, ExteriorCohomology, LineBundleCycles and ThomClass are composed with their proved
native declarations. This intermediate module exposes the full reviewed ChernClass
Lefschetz proposition as its sole explicit result-level input.
`LefschetzInput` supplies that proposition from the proved native theorem,
and `LefschetzNormalizationFinal` composes the unconditional normalization result.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Classical TensorProduct
open OAI.AlgebraicGeometry.Albanese.Construction.Mon

theorem exteriorCohomology_proved : ComplexMultiplication.KnownExteriorCohomology.CM.KnownResults.AbelianExteriorCohomology :=
  AbelianVariety.ExteriorCohomology.CM.abelian_exterior_cohomology

theorem cyclePullback_proved : CMReduction.CycleOperations.CM.Construction.LineBundleCyclesInput := by
  intro X Y f p
  refine ⟨Divisors.LineBundles.Geometric.CycleClass.BundleCycles.geometricCycleClassQ X p, Divisors.LineBundles.Geometric.CycleClass.BundleCycles.geometricCycleClassQ Y p,
    Divisors.LineBundles.Graph.ChowPullback.BundleCycles.graphChowPullback f p,
    Divisors.LineBundles.Geometric.CycleClass.BundleCycles.geometricCycleClassQ_isGeometric X p, Divisors.LineBundles.Geometric.CycleClass.BundleCycles.geometricCycleClassQ_isGeometric Y p,
    Divisors.LineBundles.Geometric.GraphPullback.BundleCycles.graphChowPullback_isGeometric f p, ?_, Divisors.LineBundles.Graph.ChowNaturality.BundleCycles.graphChowPullback_cycleClass f p⟩
  intro clX clY pull hX hY hpull
  exact ⟨Divisors.LineBundles.Geometric.CycleClass.BundleCycles.geometricCycleClassQ_eq_of_isGeometric X p clX hX,
    Divisors.LineBundles.Geometric.CycleClass.BundleCycles.geometricCycleClassQ_eq_of_isGeometric Y p clY hY,
    Divisors.LineBundles.Geometric.MapCharacterization.BundleCycles.isGeometricGraphPullback_unique f p pull (Divisors.LineBundles.Graph.ChowPullback.BundleCycles.graphChowPullback f p) hpull
      (Divisors.LineBundles.Geometric.GraphPullback.BundleCycles.graphChowPullback_isGeometric f p)⟩

theorem exteriorCycleClasses_proved : CMReduction.CycleOperations.CM.Construction.ExteriorInput :=
  CycleClass.Thom.Exterior.cycle_class_exterior

theorem DegreeTwoHolomorphicAlgebraicityproved : DegreeTwo.Transport.Constructions.HolomorphicAlgebraicityInput :=
  ComplexGroups.HolomorphicAlgebraicity.ProjectiveGraph.CM.holomorphic_group_hom_is_algebraic

theorem DegreeTwoConstructionproved : DegreeTwo.Transport.Constructions.ConstructionInput :=
  Albanese.Construction.Mon.exists_albanese

theorem DegreeTwoHodgeComparisonproved : DegreeTwo.Transport.Constructions.HodgeComparisonInput := by
  intro X x₀ A a ha
  exact Albanese.HodgeComparisonIs.CM.Construction.albanese_h1_hodge_iso X x₀ A a ha

theorem of_ChernClass (hChernClass : DegreeTwo.Chern.Constructions.ChernClassInput) : GeometricNormalization.Lefschetz.Geometry.Conclusions :=
  ⟨DegreeTwo.IntrinsicWeight.Constructions.weight_one_algebraicity
      DegreeTwoHolomorphicAlgebraicityproved DegreeTwoConstructionproved DegreeTwoHodgeComparisonproved,
    DegreeTwo.Transport.Constructions.albanese_h1_identification DegreeTwoConstructionproved DegreeTwoHodgeComparisonproved,
    DegreeTwo.Chern.Constructions.degree_two_algebraicity hChernClass⟩

variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]

/-- A genuine abelian realization for every odd sign type, using RiemannProjectivity's
proved lattice, projectivity, algebraization and cohomology comparisons. -/
def canonicalRealizations : GeometricFour.LefschetzNormalization.Geometry.RealizationFamily E := fun v =>
  Classical.choice (Geometry.ComplexTorus.RiemannProjectivity.Realization.CM.realization_of_cm_sign_type E v.val v.property)

/-- Concrete manuscript normalization, conditional only on the full ChernClass
Lefschetz proposition; every geometric interface is discharged. -/
theorem normalization_of_active_embedding_of_ChernClass
    (hChernClass : DegreeTwo.Chern.Constructions.ChernClassInput)
    (R : GeometricFour.LefschetzNormalization.Geometry.RealizationFamily E) (s : ℕ)
    (hdegree : Fintype.card (LefschetzNormalization.G E) = 2 * s)
    (v : LefschetzNormalization.FourTypes E)
    (hbalance : ∀ τ : LefschetzNormalization.G E,
      ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val τ) =
        ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val τ)) :
    GeometricNormalization.Lefschetz.Geometry.Normalization E R s v :=
  GeometricNormalization.Lefschetz.Geometry.normalization_on_realized_products E (of_ChernClass hChernClass)
    exteriorCohomology_proved cyclePullback_proved exteriorCycleClasses_proved
    R s hdegree v hbalance

/-- No realization-existence input is required. The normalized statement
and its nonzero original embedding line use these identical actual factors. -/
theorem canonical_normalization_of_ChernClass
    (hChernClass : DegreeTwo.Chern.Constructions.ChernClassInput) (s : ℕ)
    (hdegree : Fintype.card (LefschetzNormalization.G E) = 2 * s)
    (v : LefschetzNormalization.FourTypes E)
    (hbalance : ∀ τ : LefschetzNormalization.G E,
      ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val τ) =
        ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val τ)) :
    GeometricNormalization.Lefschetz.Geometry.Normalization E (canonicalRealizations E) s v ∧
      GeometricFour.LefschetzNormalization.Geometry.fourClass E (fun i => canonicalRealizations E (v i))
        (CMVariety.Products.CM.Abelian.fourProduct (fun i => (canonicalRealizations E (v i)).abelianVariety)).variety
        (CMVariety.Products.CM.Abelian.fourProjection _) (LefschetzNormalization.switchLabels E) ≠ 0 :=
  ⟨normalization_of_active_embedding_of_ChernClass E hChernClass (canonicalRealizations E) s hdegree v hbalance,
    GeometricNormalization.Lefschetz.Geometry.fourClass_ne_zero E _ _ _ (CMVariety.Products.CM.Abelian.fourProductIsLimit _) (LefschetzNormalization.switchLabels E)⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.IntrinsicComposition.LefschetzNormalization.Geometry
