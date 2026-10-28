import OAI.AlgebraicTopology.Products.RelativeReversal
import OAI.AlgebraicTopology.Products.CupGradedCommutativity
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology

/-! # Relative Cup Graded Commutativity -/

namespace OAI.AlgebraicTopology.Products.RelativeCupGradedCommutativity

noncomputable section

/-!
# Graded commutativity in actual relative cohomology

The actual signed-reversal homotopy preserves the kernels defining relative
cochains. Its cochain cup identity therefore descends inside those kernels,
rather than merely after forgetting support. This provides the relative
cup transposition used in the direct trace construction.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology.Cycles

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [CommRing R]

/-- The actual reversal cup identity holds in the relative kernel itself. -/
theorem relativeReversalCochainMap_cup (X : TopCat.{0}) (A : Set X) {p q : ℕ}
    (a : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X).X p)
    (b : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X A).X q) :
    (RelativeReversal.relativeReversalCochainMap (ModuleCat.of R R) X A).f (p + q)
        (AlgebraicGeometry.CycleClass.Geometric.RelativeCup.Cycles.absoluteRelativeCup X A p q a b) =
      (-1 : R) ^ (p * q) •
        AlgebraicGeometry.CycleClass.Geometric.RelativeCup.Cycles.relativeCochainCast (ModuleCat.of R R) X A (Nat.add_comm q p)
          (AlgebraicGeometry.CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup X A q p
            ((RelativeReversal.relativeReversalCochainMap (ModuleCat.of R R) X A).f q b)
            ((SingularReversalHomotopy.singularReversalCochainMap (ModuleCat.of R R) X).f p a)) := by
  apply AlgebraicGeometry.CycleClass.Geometric.RelativeCochainHomotopy.Cohomology.relativeCochainInclusion_injective (ModuleCat.of R R) X A (p + q)
  simpa only [map_smul, RelativeReversal.relativeReversalCochainMap_inclusion_apply,
    AlgebraicGeometry.CycleClass.Geometric.RelativeCup.Cycles.absoluteRelativeCup, AlgebraicGeometry.CycleClass.Geometric.RelativeCup.Cycles.absoluteRelativeCupWith_inclusion,
    AlgebraicGeometry.CycleClass.Geometric.RelativeCup.Cycles.relativeCochainCast_inclusion, AlgebraicGeometry.CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCup,
    AlgebraicGeometry.CycleClass.Geometric.RelativeCup.Cycles.relativeAbsoluteCupWith_inclusion, Cup.singularCup, Cup.cup] using
      CupGradedCommutativity.singularReversalCochainMap_cup X a ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of R R) X A).f q b)

/-- Reversal interchanges the actual ordinary/relative products on cohomology. -/
theorem relativeReversalCochainMap_cup_cohomology (X : TopCat.{0}) (A : Set X)
    {p q : ℕ} (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X p)
    (b : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of R R) X A q) :
    HomologicalComplex.homologyMap (RelativeReversal.relativeReversalCochainMap (ModuleCat.of R R) X A)
        (p + q) (AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology.Cycles.absoluteRelativeCohomologyCup X A p q a b) =
      (-1 : R) ^ (p * q) •
        AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeCohomologyCast (ModuleCat.of R R) X A (Nat.add_comm q p)
          (AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup X A q p
            (HomologicalComplex.homologyMap
              (RelativeReversal.relativeReversalCochainMap (ModuleCat.of R R) X A) q b)
            (HomologicalComplex.homologyMap
              (SingularReversalHomotopy.singularReversalCochainMap (ModuleCat.of R R) X) p a)) := by
  obtain ⟨a, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective (Cohomology.Singular.Basic.singularCochains (ModuleCat.of R R) X) p a
  obtain ⟨b, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective
    (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X A) q b
  simp only [AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology.Cycles.absoluteRelativeCohomologyCup, AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup]
  rw [AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology.Cycles.absoluteRelativeCohomologyCupWith_class_class, Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality,
    Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality,
    AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCupWith_class_class, AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeCohomologyCast_class,
    ← map_smul]
  apply congrArg (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of R R) X A) (p + q))
  apply Subtype.ext
  simp only [Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap_val, AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology.Cycles.absoluteRelativeCocycleCupWith_val,
    Submodule.coe_smul, AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeCocycleCast_val, AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCocycleCupWith_val]
  exact relativeReversalCochainMap_cup X A a.val b.val

/-- Graded commutativity is an equality in relative cohomology, with the
support retained throughout the homotopy. -/
theorem absoluteRelativeCohomologyCup_graded_comm (X : TopCat.{0}) (A : Set X)
    {p q : ℕ} (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X p)
    (b : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of R R) X A q) :
    AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology.Cycles.absoluteRelativeCohomologyCup X A p q a b =
      (-1 : R) ^ (p * q) •
        AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeCohomologyCast (ModuleCat.of R R) X A (Nat.add_comm q p)
          (AlgebraicGeometry.CycleClass.Geometric.RelativeCupCohomology.Cycles.relativeAbsoluteCohomologyCup X A q p b a) := by
  have h := relativeReversalCochainMap_cup_cohomology X A a b
  simpa only [RelativeReversal.relativeReversalCochainMap_homologyMap,
    SingularReversalHomotopy.singularReversalCochainMap_homologyMap, ModuleCat.id_apply] using h

end

end OAI.AlgebraicTopology.Products.RelativeCupGradedCommutativity
