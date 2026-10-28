import OAI.AlgebraicGeometry.Comparison.Betti.Open.ChartEvaluation
import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldDolbeault

/-! # Pure Differential -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.PureDifferential.Hodge

noncomputable section

/-! The actual exterior derivative of a pure open form has its two
neighboring types, and its antiholomorphic component is the original operator. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

theorem openDerivative_pure_decomposition (U : Opens M) (n : ℕ) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) (ha : a ∈ ChartEvaluation.Hodge.openPureFormsInDegree U n i) :
    ∃ b c : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U (n + 1),
      b ∈ ChartEvaluation.Hodge.openPureFormsInDegree U (n + 1) (Analysis.HodgeTheory.Decomposition.Dolbeault.Constructions.advanceHolomorphic i) ∧
      c ∈ ChartEvaluation.Hodge.openPureFormsInDegree U (n + 1) (Analysis.HodgeTheory.Decomposition.Dolbeault.Constructions.advanceAntiholomorphic i) ∧
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a = b + c := by
  obtain ⟨b, c, hb, hc, hd⟩ := ManifoldFilteredDifferential.Hodge.manifoldDerivative_pure_decomposition E U n i
    (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n a) ha
  refine ⟨(Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U (n + 1)).symm b,
    (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U (n + 1)).symm c, ?_, ?_, ?_⟩
  · change Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U (n + 1) ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U (n + 1)).symm b) ∈
      ManifoldFormFiltration.Hodge.pureFormsInDegree E U (n + 1) (Analysis.HodgeTheory.Decomposition.Dolbeault.Constructions.advanceHolomorphic i)
    rwa [LinearEquiv.apply_symm_apply]
  · change Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U (n + 1) ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U (n + 1)).symm c) ∈
      ManifoldFormFiltration.Hodge.pureFormsInDegree E U (n + 1) (Analysis.HodgeTheory.Decomposition.Dolbeault.Constructions.advanceAntiholomorphic i)
    rwa [LinearEquiv.apply_symm_apply]
  · apply (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U (n + 1)).injective
    rw [map_add, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      ← Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_d]
    exact hd

theorem openDolbeaultD_eq_component (U : Opens M) (n p q : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) (b c : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U (n + 1))
    (hb : DivisorClass.Chern.Open.ManifoldBidegree.OpenManifoldHasBidegree (p + 1) q b)
    (hc : DivisorClass.Chern.Open.ManifoldBidegree.OpenManifoldHasBidegree p (q + 1) c)
    (hd : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a = b + c) : DivisorClass.Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD p q n a = c := by
  apply ChartEvaluation.Hodge.openForm_eq_of_inChart
  intro e he y hy
  rw [DivisorClass.Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD_inChart p q a e he hy]
  have hde := congrArg (ChartEvaluation.Hodge.openChartEvaluation U (n + 1) e y) hd
  rw [map_add] at hde
  change (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a).extension.inChart e y =
    b.extension.inChart e y + c.extension.inChart e y at hde
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d_inChart a e he hy] at hde
  rw [hde]
  apply AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultDoublePrimeProjection_of_characters
  · ext v
    exact hb e he y hy AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit v
  · ext v
    exact hc e he y hy AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.dolbeaultIUnit v

theorem openTypeProjection_d_doublePrime (U : Opens M) (n : ℕ) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) (ha : a ∈ ChartEvaluation.Hodge.openPureFormsInDegree U n i) :
    FiltrationDescent.Hodge.openTypeProjection U (n + 1) (Analysis.HodgeTheory.Decomposition.Dolbeault.Constructions.advanceAntiholomorphic i) (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a) =
      DivisorClass.Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD i.val.1 i.val.2 n a := by
  obtain ⟨b, c, hb, hc, hd⟩ := openDerivative_pure_decomposition U n i a ha
  have he := openDolbeaultD_eq_component U n i.val.1 i.val.2 a b c
    ((ChartEvaluation.Hodge.mem_openPureFormsInDegree_iff U (n + 1) (Analysis.HodgeTheory.Decomposition.Dolbeault.Constructions.advanceHolomorphic i) b).mp hb)
    ((ChartEvaluation.Hodge.mem_openPureFormsInDegree_iff U (n + 1) (Analysis.HodgeTheory.Decomposition.Dolbeault.Constructions.advanceAntiholomorphic i) c).mp hc) hd
  rw [hd, map_add, ChartEvaluation.Hodge.openTypeProjection_identity U (n + 1) _ c hc,
    ChartEvaluation.Hodge.openTypeProjection_other U (n + 1) _ _ (by
      intro h
      have hh := congrArg (fun j : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree (n + 1) => j.val.1) h
      change i.val.1 = i.val.1 + 1 at hh
      omega) b hb, zero_add, he]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.PureDifferential.Hodge
