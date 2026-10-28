import OAI.Analysis.PDE.Schauder.Calculus.Periodic.ParameterSmooth
import OAI.Analysis.PDE.Schauder.Calculus.HolderPeriodicity

open Set Module
open scoped ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder

variable {Z : Type} {E P V ι : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Smooth parameter-dependent coefficients of the pulled-back second-order jet.
Their geometric meaning is supplied pointwise, allowing local physical charts. -/
structure ParameterJetFields (r : E → ℝ) (α : ℝ) (U : Set Z)
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) where
  jacobian : Z → OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E) α
  curvature : Z → OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] E) α
  background : Z → OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] ℝ) α
  source : Z → OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} ℝ α
  jacobian_smooth : ContDiffOn ℝ ∞ jacobian U
  curvature_smooth : ContDiffOn ℝ ∞ curvature U
  background_smooth : ContDiffOn ℝ ∞ background U
  source_smooth : ContDiffOn ℝ ∞ source U
  jacobian_periodic : ∀ z ∈ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value (jacobian z)))
  curvature_periodic : ∀ z ∈ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value (curvature z)))
  background_periodic : ∀ z ∈ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value (background z)))
  source_periodic : ∀ z ∈ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value (source z)))

theorem exists_parameterJetFields
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) {U : Set Z} (hU : IsOpen U)
    (J : Z × E → E →L[ℝ] E) (T : Z × E → E →L[ℝ] E →L[ℝ] E)
    (B : Z × E → E →L[ℝ] E →L[ℝ] ℝ) (f : Z × E → ℝ)
    (hJ : ContDiffOn ℝ ∞ J {p | p.1 ∈ U}) (hT : ContDiffOn ℝ ∞ T {p | p.1 ∈ U})
    (hB : ContDiffOn ℝ ∞ B {p | p.1 ∈ U}) (hf : ContDiffOn ℝ ∞ f {p | p.1 ∈ U})
    (hpJ : ∀ z ∈ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => J (z,x)))
    (hpT : ∀ z ∈ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => T (z,x)))
    (hpB : ∀ z ∈ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => B (z,x)))
    (hpf : ∀ z ∈ U, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => f (z,x))) :
    ∃ C : ParameterJetFields r α U e b,
      (∀ z ∈ U, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.jacobian z) x = J (z,x)) ∧
      (∀ z ∈ U, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.curvature z) x = T (z,x)) ∧
      (∀ z ∈ U, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.background z) x = B (z,x)) ∧
      (∀ z ∈ U, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.source z) x = f (z,x)) := by
  obtain ⟨Jh,hJs,hJv⟩ := exists_smooth_periodic_parameter_family e b hK hr hrp hbounded hα hα1 hU J hJ hpJ
  obtain ⟨Th,hTs,hTv⟩ := exists_smooth_periodic_parameter_family e b hK hr hrp hbounded hα hα1 hU T hT hpT
  obtain ⟨Bh,hBs,hBv⟩ := exists_smooth_periodic_parameter_family e b hK hr hrp hbounded hα hα1 hU B hB hpB
  obtain ⟨fh,hfs,hfv⟩ := exists_smooth_periodic_parameter_family e b hK hr hrp hbounded hα hα1 hU f hf hpf
  refine ⟨⟨Jh,Th,Bh,fh,hJs,hTs,hBs,hfs,?_,?_,?_,?_⟩,hJv,hTv,hBv,hfv⟩
  · exact fun z hz => holder_periodic_of_actual e b hrp (Jh z) _ (hpJ z hz) (hJv z hz)
  · exact fun z hz => holder_periodic_of_actual e b hrp (Th z) _ (hpT z hz) (hTv z hz)
  · exact fun z hz => holder_periodic_of_actual e b hrp (Bh z) _ (hpB z hz) (hBv z hz)
  · exact fun z hz => holder_periodic_of_actual e b hrp (fh z) _ (hpf z hz) (hfv z hz)

end OAI.Analysis.PDE.Schauder
