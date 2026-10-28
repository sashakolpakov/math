import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicTopPushforward
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportAnd

/-! # Intrinsic Gysin Adjunction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicGysinAdjunction.Constructions

noncomputable section

section

/-!
# Compact cohomology pushforward through actual native cap duality

All complementary degrees and their equalities are explicit. Adjunction
uses the genuine ordinary cohomology pullback and homology pushforward.
The definition does not assert the remaining global Thom cup identity.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Duality.Poincare.CompactSupportAnd
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {d e : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
variable [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]
variable [ChartedSpace (Fin d → ℂ) M] [ChartedSpace (Fin e → ℂ) N]
variable [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M] [IsManifold 𝓘(ℂ, Fin e → ℂ) 1 N]

def nativeCompactCohomologyPushforward (f : TopCat.of M ⟶ TopCat.of N)
    (s t r : ℕ) (hs : s+r=2*d) (ht : t+r=2*e) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) s ⟶
      AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) t :=
  (AlgebraicTopology.Duality.Poincare.Manifold.complexManifoldPoincareDuality d (M := M) s r hs).hom ≫
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f r ≫
    (AlgebraicTopology.Duality.Poincare.Manifold.complexManifoldPoincareDuality e (M := N) t r ht).inv

theorem nativeCompactCohomologyPushforward_cap (f : TopCat.of M ⟶ TopCat.of N)
    (s t r : ℕ) (hs : s+r=2*d) (ht : t+r=2*e) :
    nativeCompactCohomologyPushforward (d := d) (e := e) f s t r hs ht ≫
      (AlgebraicTopology.Duality.Poincare.Manifold.complexManifoldPoincareDuality e (M := N) t r ht).hom =
    (AlgebraicTopology.Duality.Poincare.Manifold.complexManifoldPoincareDuality d (M := M) s r hs).hom ≫
      AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f r := by
  simp only [nativeCompactCohomologyPushforward, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem nativeCompactCohomologyPushforward_adjunction (f : TopCat.of M ⟶ TopCat.of N)
    (s t r : ℕ) (hs : s+r=2*d) (ht : t+r=2*e)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) s)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N) r) :
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation e r t (by omega) b
      (nativeCompactCohomologyPushforward (d := d) (e := e) f s t r hs ht a) =
    AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation d r s (by omega)
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f r b) a := by
  have hc := ConcreteCategory.congr_hom
    (nativeCompactCohomologyPushforward_cap (d := d) (e := e) f s t r hs ht) a
  have he := congrArg (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of N) r b) hc
  exact he.trans (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularEvaluation_naturality (ModuleCat.of ℚ ℚ) f r b
    (AlgebraicTopology.Duality.Poincare.ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) s r hs a)).symm

end

/-! Composition and actual open-extension squares for native cap-duality pushforward in all degrees. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Duality.Poincare.CompactSupportAnd
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {d e k : ℕ} {M N L : Type}
variable [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace L]
variable [T2Space M] [T2Space N] [T2Space L]
variable [SecondCountableTopology M] [SecondCountableTopology N] [SecondCountableTopology L]
variable [ChartedSpace (Fin d → ℂ) M] [ChartedSpace (Fin e → ℂ) N] [ChartedSpace (Fin k → ℂ) L]
variable [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M] [IsManifold 𝓘(ℂ, Fin e → ℂ) 1 N]
variable [IsManifold 𝓘(ℂ, Fin k → ℂ) 1 L]

theorem nativeCompactCohomologyPushforward_open (U : Opens M)
    (s r : ℕ) (hs : s+r=2*d) :
    nativeCompactCohomologyPushforward (M := U) (N := M) (d := d) (e := d)
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) U) s s r hs hs =
        AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of M) U s := by
  apply (cancel_mono (AlgebraicTopology.Duality.Poincare.Manifold.complexManifoldPoincareDuality d (M := M) s r hs).hom).mp
  rw [nativeCompactCohomologyPushforward_cap]
  exact (AlgebraicTopology.Duality.Poincare.CanonicalCapNaturality.complexManifoldCompactSupportCap_open d U s r hs).symm

theorem nativeCompactCohomologyPushforward_comp
    (f : TopCat.of M ⟶ TopCat.of N) (g : TopCat.of N ⟶ TopCat.of L)
    (s t u r : ℕ) (hs : s+r=2*d) (ht : t+r=2*e) (hu : u+r=2*k) :
    nativeCompactCohomologyPushforward (d := d) (e := e) f s t r hs ht ≫
      nativeCompactCohomologyPushforward (d := e) (e := k) g t u r ht hu =
    nativeCompactCohomologyPushforward (d := d) (e := k) (f ≫ g) s u r hs hu := by
  unfold nativeCompactCohomologyPushforward
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  rw [← Category.assoc]
  congr 1
  change AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.simplicialHomologyPushforward (R := ℚ) (TopCat.toSSet.map f) r ≫
      AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.simplicialHomologyPushforward (R := ℚ) (TopCat.toSSet.map g) r =
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.simplicialHomologyPushforward (R := ℚ) (TopCat.toSSet.map (f ≫ g)) r
  simp only [Functor.map_comp, AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.simplicialHomologyPushforward, AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap,
    SSet.chainComplexMap, Functor.map_comp, HomologicalComplex.homologyMap_comp]

theorem nativeCompactCohomologyPushforward_openSquare (U : Opens M) (V : Opens N)
    (fU : TopCat.of U ⟶ TopCat.of V) (f : TopCat.of M ⟶ TopCat.of N)
    (h : fU ≫ CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) V = CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) U ≫ f)
    (s t r : ℕ) (hs : s+r=2*d) (ht : t+r=2*e) :
    nativeCompactCohomologyPushforward (M := U) (N := V) (d := d) (e := e) fU s t r hs ht ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of N) V t =
    AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of M) U s ≫
      nativeCompactCohomologyPushforward (M := M) (N := N) (d := d) (e := e) f s t r hs ht := by
  have hL := nativeCompactCohomologyPushforward_comp (M := U) (N := V) (L := N)
    (d := d) (e := e) (k := e) fU (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) V) s t t r hs ht ht
  have hR := nativeCompactCohomologyPushforward_comp (M := U) (N := M) (L := N)
    (d := d) (e := d) (k := e) (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) U) f s s t r hs hs ht
  have hc := congrArg (fun g => nativeCompactCohomologyPushforward
    (M := U) (N := N) (d := d) (e := e) g s t r hs ht) h
  rw [nativeCompactCohomologyPushforward_open] at hL hR
  exact hL.trans (hc.trans hR.symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicGysinAdjunction.Constructions
