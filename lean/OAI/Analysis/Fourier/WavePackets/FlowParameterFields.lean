import OAI.Analysis.Fourier.WavePackets.FlowPeriodicity
import OAI.Analysis.PDE.Schauder.Calculus.Parameter.JetFields

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Metric Module OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Dirichlet.ParameterDeformation
open OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder
open scoped ContDiff

variable {Z T : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {m : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 → ℝ} {α : ℝ} {U : Set Z}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4

omit [CompleteSpace T] in
/-- Add any smooth periodic internal flow to a smooth external family of
inverse-map coefficients, and construct the actual combined Hölder fields. -/
theorem exists_flow_parameterJetFields
    (D : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b r)
    {C : Set V} (hC : IsCompact C) (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hU : IsOpen U)
    (J : Z × E → E →L[ℝ] E) (K : Z × E → E →L[ℝ] E →L[ℝ] E)
    (B : Z × E → E →L[ℝ] E →L[ℝ] ℝ) (F : Z × E → ℝ)
    (hJ : ContDiff ℝ ∞ J) (hK : ContDiff ℝ ∞ K)
    (hB : ContDiff ℝ ∞ B) (hF : ContDiff ℝ ∞ F)
    (hJp : ∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => J (z,x)))
    (hKp : ∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => K (z,x)))
    (hBp : ∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => B (z,x)))
    (hFp : ∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => F (z,x))) :
    ∃ C : OAI.Analysis.PDE.Schauder.ParameterJetFields r α (U ×ˢ {t : T | ‖t‖ < D.radius}) e b,
      (∀ z ∈ U ×ˢ {t : T | ‖t‖ < D.radius}, ∀ x : {x | r x ≤ 0},
        OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.jacobian z) x = flowJacobian D.map J (z,x)) ∧
      (∀ z ∈ U ×ˢ {t : T | ‖t‖ < D.radius}, ∀ x : {x | r x ≤ 0},
        OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.curvature z) x = flowCurvature D.map J K (z,x)) ∧
      (∀ z ∈ U ×ˢ {t : T | ‖t‖ < D.radius}, ∀ x : {x | r x ≤ 0},
        OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.background z) x = flowPullback D.map B (z,x)) ∧
      (∀ z ∈ U ×ˢ {t : T | ‖t‖ < D.radius}, ∀ x : {x | r x ≤ 0},
        OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.source z) x = flowPullback D.map F (z,x)) := by
  have hI : IsOpen {t : T | ‖t‖ < D.radius} := isOpen_lt continuous_norm continuous_const
  apply OAI.Analysis.PDE.Schauder.exists_parameterJetFields e b hC hr hrp hbounded hα hα1 (hU.prod hI)
    (flowJacobian D.map J) (flowCurvature D.map J K) (flowPullback D.map B) (flowPullback D.map F)
  · exact (contDiffOn_flowJacobian hI D.smooth D.inverse_smooth hJ).mono (fun p hp => hp.2)
  · exact (contDiffOn_flowCurvature hI D.smooth D.inverse_smooth hJ hK).mono (fun p hp => hp.2)
  · exact (contDiff_flowPullback D.smooth hB).contDiffOn
  · exact (contDiff_flowPullback D.smooth hF).contDiffOn
  · intro p hp
    exact flowJacobian_periodic D hJp p.1 p.2 hp.2
  · intro p hp
    exact flowCurvature_periodic D hJp hKp p.1 p.2 hp.2
  · intro p hp
    exact flowPullback_periodic D hBp p.1 p.2
  · intro p hp
    exact flowPullback_periodic D hFp p.1 p.2

end OAI.Analysis.Fourier.WavePackets
