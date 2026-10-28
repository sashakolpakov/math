import OAI.AlgebraicGeometry.Comparison.Betti.PuncturedCauchy

/-! # Punctured Parametric Dbar Primitive -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.PuncturedParametricDbarPrimitive.Dolbeault

noncomputable section

/-! A global antiholomorphic primitive on a punctured complex line,
jointly smooth over an arbitrary open complex parameter domain. -/

open _root_.TopologicalSpace Set _root_.Metric
open scoped ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

def puncturedParametricCauchyCandidate (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ))) (q : P × ℂ) : F :=
  Open.ParametricSeriesConvergence.Dolbeault.openParametricCauchyCandidate S (PuncturedCauchy.Dolbeault.puncturedCauchyOuterInput g) (PuncturedCauchy.Dolbeault.puncturedCauchyOuterInput_smooth S hg) q +
    Open.ParametricSeriesConvergence.Dolbeault.openParametricCauchyCandidate S (PuncturedCauchy.Dolbeault.puncturedCauchyInnerInput g) (PuncturedCauchy.Dolbeault.puncturedCauchyInnerInput_smooth S hg) (q.1, q.2⁻¹)

theorem puncturedParametricCauchyCandidate_smooth (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ))) :
    ContDiffOn ℝ ∞ (puncturedParametricCauchyCandidate S g hg)
      ((S : Set P) ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ)) := by
  intro q hq
  have hA := (Open.ParametricTailCauchy.Dolbeault.openParametricCauchyCandidate_smooth S _ (PuncturedCauchy.Dolbeault.puncturedCauchyOuterInput_smooth S hg)).contDiffAt
    ((S.isOpen.prod isOpen_univ).mem_nhds (show q ∈ (S : Set P) ×ˢ univ from ⟨hq.1, mem_univ _⟩))
  have hB := (Open.ParametricTailCauchy.Dolbeault.openParametricCauchyCandidate_smooth S _ (PuncturedCauchy.Dolbeault.puncturedCauchyInnerInput_smooth S hg)).contDiffAt
    ((S.isOpen.prod isOpen_univ).mem_nhds (show (q.1, q.2⁻¹) ∈ (S : Set P) ×ˢ univ from ⟨hq.1, mem_univ _⟩))
  exact (hA.add (hB.comp q (contDiffAt_fst.prodMk (contDiffAt_snd.inv hq.2)))).contDiffWithinAt

theorem puncturedParametricCauchyCandidate_dbar (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ)))
    {p : P} (hp : p ∈ S) {z : ℂ} (hz : z ≠ 0) :
    VectorDbar.Dolbeault.vectorDbar (fun w => puncturedParametricCauchyCandidate S g hg (p, w)) z = g (p, z) := by
  let A := Open.ParametricSeriesConvergence.Dolbeault.openParametricCauchyCandidate S (PuncturedCauchy.Dolbeault.puncturedCauchyOuterInput g) (PuncturedCauchy.Dolbeault.puncturedCauchyOuterInput_smooth S hg)
  let B := Open.ParametricSeriesConvergence.Dolbeault.openParametricCauchyCandidate S (PuncturedCauchy.Dolbeault.puncturedCauchyInnerInput g) (PuncturedCauchy.Dolbeault.puncturedCauchyInnerInput_smooth S hg)
  have hA : DifferentiableAt ℝ (fun w => A (p, w)) z :=
    (Open.ExpandingParametricPrimitives.Dolbeault.contDiff_slice_of_contDiffOn_product
      (Open.ParametricTailCauchy.Dolbeault.openParametricCauchyCandidate_smooth S _ (PuncturedCauchy.Dolbeault.puncturedCauchyOuterInput_smooth S hg)) hp).differentiable (by simp) z
  have hB : DifferentiableAt ℝ (fun w => B (p, w)) z⁻¹ :=
    (Open.ExpandingParametricPrimitives.Dolbeault.contDiff_slice_of_contDiffOn_product
      (Open.ParametricTailCauchy.Dolbeault.openParametricCauchyCandidate_smooth S _ (PuncturedCauchy.Dolbeault.puncturedCauchyInnerInput_smooth S hg)) hp).differentiable (by simp) z⁻¹
  have hBinv : DifferentiableAt ℝ (fun w => B (p, w⁻¹)) z :=
    hB.comp z ((hasDerivAt_inv hz).differentiableAt.restrictScalars ℝ)
  change VectorDbar.Dolbeault.vectorDbar (fun w => A (p, w) + B (p, w⁻¹)) z = _
  rw [CauchyHolomorphicLocus.Dolbeault.vectorDbar_add hA hBinv, VectorDbarHolomorphicPullback.Dolbeault.vectorDbar_comp_inv hB hz]
  have heA : VectorDbar.Dolbeault.vectorDbar (fun w => A (p, w)) z = PuncturedCauchy.Dolbeault.puncturedCauchyOuterInput g (p, z) :=
    Open.ParametricTailCauchy.Dolbeault.openParametricCauchyCandidate_dbar S _ (PuncturedCauchy.Dolbeault.puncturedCauchyOuterInput_smooth S hg) hp z
  have heB : VectorDbar.Dolbeault.vectorDbar (fun w => B (p, w)) z⁻¹ = PuncturedCauchy.Dolbeault.puncturedCauchyInnerInput g (p, z⁻¹) :=
    Open.ParametricTailCauchy.Dolbeault.openParametricCauchyCandidate_dbar S _ (PuncturedCauchy.Dolbeault.puncturedCauchyInnerInput_smooth S hg) hp z⁻¹
  rw [heA, heB]
  change (1 - (PuncturedCauchy.Dolbeault.puncturedCauchyBump z : ℂ)) • g (p, z) +
    PuncturedCauchy.Dolbeault.complexInversionJacobian z • (PuncturedCauchy.Dolbeault.complexInversionJacobian z⁻¹ •
      ((PuncturedCauchy.Dolbeault.puncturedCauchyBump z⁻¹⁻¹ : ℂ) • g (p, z⁻¹⁻¹))) = _
  rw [inv_inv, smul_smul, PuncturedCauchy.Dolbeault.complexInversionJacobian_inverse_product hz, one_smul,
    ← add_smul, sub_add_cancel, one_smul]

theorem exists_punctured_parametric_vectorDbar_primitive (S : Opens P) {g : P × ℂ → F}
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ))) :
    ∃ G : P × ℂ → F, ContDiffOn ℝ ∞ G ((S : Set P) ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ)) ∧
      ∀ p ∈ S, ∀ z : ℂ, z ≠ 0 → VectorDbar.Dolbeault.vectorDbar (fun w => G (p, w)) z = g (p, z) :=
  ⟨puncturedParametricCauchyCandidate S g hg, puncturedParametricCauchyCandidate_smooth S g hg,
    fun _ hp _ hz => puncturedParametricCauchyCandidate_dbar S g hg hp hz⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.PuncturedParametricDbarPrimitive.Dolbeault
