import OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricTailCauchy
import OAI.AlgebraicGeometry.Comparison.Betti.ZeroJetDifferential

/-! # Parametric Series Directional Derivative -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricSeriesDirectionalDerivative.Dolbeault

noncomputable section

section

/-! The actual directional parameter derivative of a corrected tail
is the sum of the original directional derivatives of its terms. -/

open _root_.TopologicalSpace Set _root_.Metric
open scoped ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

theorem correctedOpenParametricCauchyTail_parameter_fderiv (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ Set.univ))
    (m : ℕ) {q : P × ℂ} (hq : q ∈ interior (ParameterExhaustion.Dolbeault.openParameterCompact S m) ×ˢ ball (0 : ℂ) (m : ℝ)) (v : P) :
    fderiv ℝ (fun x => ∑' n, ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg (n + m) x) q (v, 0) =
      ∑' n, fderiv ℝ (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg (n + m)) q (v, 0) := by
  let e := (continuousMultilinearCurryFin0 ℝ P F).toContinuousLinearEquiv
  have h := e.hasFDerivAt.comp q (ParametricTailCauchy.Dolbeault.hasFDerivAt_openParametricTailJet S g hg m 0 0 hq)
  have he : e ∘ ParametricTailCauchy.Dolbeault.openParametricTailJet S g hg m 0 0 =
      (fun x => ∑' n, ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg (n + m) x) :=
    funext (fun x => ParametricTailCauchy.Dolbeault.openParametricTailJet_zero_value S g hg m x)
  rw [he] at h
  rw [h.fderiv]
  change (continuousMultilinearCurryFin0 ℝ P F)
    ((MixedJetDifferential.Dolbeault.mixedJetParameterDifferential (P := P) (F := F) 0 (ParametricTailCauchy.Dolbeault.openParametricTailJet S g hg m 1 0 q) +
      MixedJetDifferential.Dolbeault.mixedJetLineDifferential (P := P) (F := F) 0 (ParametricTailCauchy.Dolbeault.openParametricTailJet S g hg m 0 1 q)) (v, 0)) = _
  rw [ZeroJetDifferential.Dolbeault.zeroJet_differential_parameter_apply]
  let L : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => P) F →L[ℂ] F :=
    OperatorParameterJets.Dolbeault.realMultilinearComplexEvaluation (fun _ => v)
  have hs : Summable (fun n => MixedJetAlgebra.Dolbeault.mixedParameterJet (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg (n + m)) 1 0 q) :=
    (summable_nat_add_iff m).mpr (ParametricSeriesConvergence.Dolbeault.correctedOpenParametricMixedJets_summable (q := q) S g hg 1 0
      (ParameterExhaustion.Dolbeault.openParameterCompact_subset S m (interior_subset hq.1)))
  change L (∑' n, MixedJetAlgebra.Dolbeault.mixedParameterJet (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg (n + m)) 1 0 q) = _
  rw [L.map_tsum hs]
  apply tsum_congr
  intro n
  exact ZeroJetDifferential.Dolbeault.parameterJet_one_apply (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg (n + m)) q v

end

/-! Parameter differentiation of the entire corrected series equals
the convergent series of its actual parameter derivatives on the domain. -/

open _root_.TopologicalSpace Set _root_.Metric Filter
open scoped ContDiff _root_.Topology

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

theorem correctedOpenParametricCauchySeries_parameter_fderiv (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) (q : P × ℂ) (hq : q.1 ∈ S) (v : P) :
    fderiv ℝ (fun x => ∑' n, ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n x) q (v, 0) =
      ∑' n, fderiv ℝ (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n) q (v, 0) := by
  obtain ⟨m, hm⟩ := ParameterExhaustion.Dolbeault.exists_openParameterCompact_product_neighborhood (q := q) S hq
  have hpoint : ((S : Set P) ×ˢ univ) ∈ 𝓝 q :=
    (S.isOpen.prod isOpen_univ).mem_nhds ⟨hq, mem_univ _⟩
  have he : (fun x => ∑' n, ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n x) =ᶠ[𝓝 q]
      (fun x => (∑ n ∈ Finset.range m, ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n x) +
        ∑' n, ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg (n + m) x) := by
    filter_upwards [hpoint] with x hx
    exact ((ParametricSeriesConvergence.Dolbeault.correctedOpenParametricCauchyDifference_summable (q := x) S g hg hx.1).sum_add_tsum_nat_add m).symm
  have hf (n : ℕ) : DifferentiableAt ℝ (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n) q :=
    ((ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference_smooth S g hg n).contDiffAt hpoint).differentiableAt (by simp)
  have hfin : DifferentiableAt ℝ (fun x => ∑ n ∈ Finset.range m, ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n x) q :=
    ((ContDiffOn.sum (fun n _ => ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference_smooth S g hg n)).contDiffAt hpoint).differentiableAt (by simp)
  have ht : DifferentiableAt ℝ (fun x => ∑' n, ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg (n + m) x) q :=
    ((ParametricTailCauchy.Dolbeault.correctedOpenParametricCauchyTail_smooth S g hg m).contDiffAt
      ((isOpen_interior.prod isOpen_ball).mem_nhds hm)).differentiableAt (by simp)
  let L : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => P) F →L[ℂ] F :=
    OperatorParameterJets.Dolbeault.realMultilinearComplexEvaluation (fun _ => v)
  have hd : Summable (fun n => fderiv ℝ (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n) q (v, 0)) :=
    (L.summable (ParametricSeriesConvergence.Dolbeault.correctedOpenParametricMixedJets_summable (q := q) S g hg 1 0 hq)).congr
      (fun n => ZeroJetDifferential.Dolbeault.parameterJet_one_apply (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n) q v)
  rw [he.fderiv_eq, fderiv_fun_add hfin ht, add_apply, fderiv_fun_sum (fun n _ => hf n), sum_apply,
    correctedOpenParametricCauchyTail_parameter_fderiv S g hg m hm v]
  exact hd.sum_add_tsum_nat_add m

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricSeriesDirectionalDerivative.Dolbeault
