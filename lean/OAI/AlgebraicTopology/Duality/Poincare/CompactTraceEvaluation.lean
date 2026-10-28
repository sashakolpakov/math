import OAI.AlgebraicTopology.Duality.Poincare.CompactFundamentalTrace
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology
import OAI.AlgebraicTopology.Products.CapTranspose

/-! # Compact Trace Evaluation -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CompactTraceEvaluation

noncomputable section

/-!
# Evaluation of the actual compact-relative trace of ordinary cap

For an even ordinary cohomological degree, testing the actual compact-relative
trace of cap with the ambient fundamental class is exactly the canonical
compact-support evaluation on the open submanifold. The proof uses the
intrinsic compact fundamental class and the proved relative cap transposition.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Products.CapTranspose
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem compactFundamentalClass_degreeCast
    (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]
    (K : Compacts M) {i j : ℕ} (h : i = j) (hi : i = 2 * d) (hj : j = 2 * d) :
    (eqToHom (congrArg
      (fun n => AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology (TopCat.of M) (K : Set M)ᶜ n) h))
        (ComplexManifoldCap.complexCompactClassInDegree d (M := M) i hi K) =
      ComplexManifoldCap.complexCompactClassInDegree d (M := M) j hj K := by
  subst j
  rfl

/-- Every relative test of the actual compact trace of ordinary cap is
the corresponding compact-support evaluation on the open submanifold.
The even-degree hypothesis is precisely what removes the cap transposition sign. -/
theorem complexManifoldOrdinaryCap_openCompactRelativeTrace_evaluation
    (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]
    (U : Opens M) (K : Compacts U) (p q : ℕ) (hpq : p + q = 2 * d) (hp : Even p)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p)
    (b : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) (K : Set U)ᶜ q) :
    AlgebraicGeometry.CycleClass.Geometric.RelativeChainD.Cycles.relativeUniversalCoefficientEquiv ℚ (TopCat.of U) (K : Set U)ᶜ q b
        (CompactFundamentalTrace.openCompactRelativeTrace (X := TopCat.of M) U K q
          (CompactMeaning.complexManifoldOrdinaryCap d (M := M) p q hpq a)) =
      CompactSupportDualCohomology.compactSupportEvaluation d (M := U) p q hpq
        (Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
          (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)) p a)
        (CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of U) K q b) := by
  rw [CompactFundamentalTrace.complexManifoldOrdinaryCap_openCompactRelativeTrace,
    Products.CapTranspose.relativeCapTranspose_of_even_left (TopCat.of U) (K : Set U)ᶜ
      K.isCompact.isClosed.isOpen_compl p q hp,
    compactFundamentalClass_degreeCast d K (Nat.add_comm p q) hpq (by omega),
    CompactSupportDualCohomology.compactSupportEvaluation_stage]

end

end OAI.AlgebraicTopology.Duality.Poincare.CompactTraceEvaluation
