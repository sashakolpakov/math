import OAI.Analysis.PDE.Dirichlet.C2HolderPeriodicSmooth

open Set Module Filter
open scoped ContDiff Topology
noncomputable section

namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {m s : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {Ω K : Set (CoordinateSpace m s)} {hΩK : Ω ⊆ K} {α : ℝ}
  {e : CoordinateSpace m s ≃L[ℝ] P × V} {b : Basis ι ℝ P}

omit [Fintype ι] in
/-- The nonlinear periodic equation admits a smooth local solution map whenever
its actual derivative is a continuous linear equivalence.  No smoothness of
the periodic target map is included among the hypotheses. -/
theorem periodicMooreDirichlet_localInverse
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ closure Ω)
    (hΩper : LatticePeriodic e b (fun x ↦ x ∈ Ω))
    (hKper : LatticePeriodic e b (fun x ↦ x ∈ K))
    (hα : 0 ≤ α) (slots : Fin s → Q) (v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (hv : LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v)))
    (u : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b)
    (L : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b ≃L[ℝ]
      OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := K) (α := α) e b)
    (hL : fderiv ℝ (periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα slots v hv) u =
      L.toContinuousLinearMap) :
    let F := periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα slots v hv
    ∃ G : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := K) (α := α) e b →
      OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b,
      ContDiffAt ℝ ∞ G (F u) ∧ G (F u) = u ∧
      (∀ᶠ y in 𝓝 (F u), F (G y) = y) ∧
      (∀ᶠ z in 𝓝 u, G (F z) = z) := by
  let : Fact (IsOpen Ω) := ⟨hΩ⟩
  dsimp only
  let F := periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα slots v hv
  have hF : ContDiff ℝ ∞ F :=
    contDiff_periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα slots v hv
  have hd : HasFDerivAt F L.toContinuousLinearMap u := by
    rw [← hL]
    exact (hF.differentiable (by simp) u).hasFDerivAt
  have hs := hF.contDiffAt.hasStrictFDerivAt' hd (by simp)
  refine ⟨hF.contDiffAt.localInverse hd (by simp),
    hF.contDiffAt.to_localInverse hd (by simp), ?_, ?_, ?_⟩
  · exact hF.contDiffAt.localInverse_apply_image hd (by simp)
  · exact hs.eventually_right_inverse
  · exact hs.eventually_left_inverse

omit [Fintype ι] in
/-- Local solvability remains inside any prescribed open set of admissible
potentials.  This is the openness step for a continuity method. -/
theorem periodicMooreDirichlet_image_mem_nhds
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ closure Ω)
    (hΩper : LatticePeriodic e b (fun x ↦ x ∈ Ω))
    (hKper : LatticePeriodic e b (fun x ↦ x ∈ K))
    (hα : 0 ≤ α) (slots : Fin s → Q) (v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (hv : LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v)))
    (u : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b)
    (L : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b ≃L[ℝ]
      OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := K) (α := α) e b)
    (hL : fderiv ℝ (periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα slots v hv) u =
      L.toContinuousLinearMap)
    {U : Set (OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b)}
    (hU : U ∈ 𝓝 u) :
    (periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα slots v hv) '' U ∈
      𝓝 (periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα slots v hv u) := by
  let F := periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα slots v hv
  obtain ⟨G, hG, hGu, hr, _⟩ :=
    periodicMooreDirichlet_localInverse hΩ hKΩ hΩper hKper hα slots v hv u L hL
  have ht : Tendsto G (𝓝 (F u)) (𝓝 u) := by
    simpa only [ContinuousAt, hGu] using hG.continuousAt
  change F '' U ∈ 𝓝 (F u)
  filter_upwards [ht hU, hr] with y hy hxy
  exact ⟨G y, hy, hxy⟩

omit [Fintype ι] in
theorem isOpen_image_periodicMooreDirichlet
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ closure Ω)
    (hΩper : LatticePeriodic e b (fun x ↦ x ∈ Ω))
    (hKper : LatticePeriodic e b (fun x ↦ x ∈ K))
    (hα : 0 ≤ α) (slots : Fin s → Q) (v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (hv : LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value v)))
    {U : Set (OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b)}
    (hU : IsOpen U)
    (hL : ∀ u ∈ U, ∃ L :
      OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b ≃L[ℝ]
        OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := K) (α := α) e b,
      fderiv ℝ (periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα slots v hv) u =
        L.toContinuousLinearMap) :
    IsOpen ((periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα slots v hv) '' U) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨L, hL⟩ := hL u hu
  exact periodicMooreDirichlet_image_mem_nhds hΩ hKΩ hΩper hKper hα slots v hv u L hL
    (hU.mem_nhds hu)

end OAI.Analysis.PDE.Dirichlet
