import OAI.AlgebraicTopology.Duality.Poincare.Manifold
import OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace

/-! # Intrinsic Top Pushforward -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicTopPushforward.Constructions

noncomputable section

/-!
# Actual pushforward of compact top cohomology via native cap duality

This degree-specific map is conjugate to ordinary zeroth-homology
pushforward. Its trace, composition, and open-extension laws use the
actual native cap maps. It is not a general Gysin theorem.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {d e : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
variable [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]
variable [ChartedSpace (Fin d → ℂ) M] [ChartedSpace (Fin e → ℂ) N]
variable [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M] [IsManifold 𝓘(ℂ, Fin e → ℂ) 1 N]

def nativeTopCohomologyPushforward (f : TopCat.of M ⟶ TopCat.of N) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) (2*d) ⟶
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) (2*e) :=
  (AlgebraicTopology.Duality.Poincare.Manifold.complexManifoldPoincareDuality d (M := M) (2*d) 0 rfl).hom ≫
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f 0 ≫
    (AlgebraicTopology.Duality.Poincare.Manifold.complexManifoldPoincareDuality e (M := N) (2*e) 0 rfl).inv

theorem nativeTopCohomologyPushforward_cap (f : TopCat.of M ⟶ TopCat.of N) :
    nativeTopCohomologyPushforward (d := d) (e := e) f ≫
      (AlgebraicTopology.Duality.Poincare.Manifold.complexManifoldPoincareDuality e (M := N) (2*e) 0 rfl).hom =
    (AlgebraicTopology.Duality.Poincare.Manifold.complexManifoldPoincareDuality d (M := M) (2*d) 0 rfl).hom ≫
      AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f 0 := by
  simp only [nativeTopCohomologyPushforward, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem nativeTopCohomologyPushforward_trace (f : TopCat.of M ⟶ TopCat.of N) :
    nativeTopCohomologyPushforward (d := d) (e := e) f ≫
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace e (M := N) = AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace d (M := M) := by
  change nativeTopCohomologyPushforward (d := d) (e := e) f ≫
    ((AlgebraicTopology.Duality.Poincare.Manifold.complexManifoldPoincareDuality e (M := N) (2*e) 0 rfl).hom ≫ AlgebraicTopology.Duality.Poincare.CapAugmentation.rationalH0Augmentation (TopCat.of N)) = _
  rw [← Category.assoc, nativeTopCohomologyPushforward_cap, Category.assoc,
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.rationalH0Augmentation_naturality]
  rfl

theorem nativeTopCohomologyPushforward_open (U : Opens M) :
    nativeTopCohomologyPushforward (M := U) (N := M) (d := d) (e := d)
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) U) = AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of M) U (2*d) := by
  apply (cancel_mono (AlgebraicTopology.Duality.Poincare.Manifold.complexManifoldPoincareDuality d (M := M) (2*d) 0 rfl).hom).mp
  rw [nativeTopCohomologyPushforward_cap]
  exact (AlgebraicTopology.Duality.Poincare.CanonicalCapNaturality.complexManifoldCompactSupportCap_open d U (2*d) 0 rfl).symm

variable {k : ℕ} {L : Type} [TopologicalSpace L] [T2Space L] [SecondCountableTopology L]
variable [ChartedSpace (Fin k → ℂ) L] [IsManifold 𝓘(ℂ, Fin k → ℂ) 1 L]

theorem nativeTopCohomologyPushforward_comp (f : TopCat.of M ⟶ TopCat.of N)
    (g : TopCat.of N ⟶ TopCat.of L) :
    nativeTopCohomologyPushforward (d := d) (e := e) f ≫
      nativeTopCohomologyPushforward (d := e) (e := k) g =
    nativeTopCohomologyPushforward (d := d) (e := k) (f ≫ g) := by
  unfold nativeTopCohomologyPushforward
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  rw [← Category.assoc]
  congr 1
  change AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.simplicialHomologyPushforward (R := ℚ) (TopCat.toSSet.map f) 0 ≫
      AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.simplicialHomologyPushforward (R := ℚ) (TopCat.toSSet.map g) 0 =
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.simplicialHomologyPushforward (R := ℚ) (TopCat.toSSet.map (f ≫ g)) 0
  simp only [Functor.map_comp, AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.simplicialHomologyPushforward, AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap,
    SSet.chainComplexMap, Functor.map_comp, HomologicalComplex.homologyMap_comp]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicTopPushforward.Constructions
