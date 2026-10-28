import OAI.Analysis.PDE.Dirichlet.Rough.Joint.ParameterExtraction
import OAI.Analysis.Normed.Function.Holder.C2HolderJointClosedChart

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet.ParameterDeformation

open OAI.Analysis.Normed.Function.Holder

variable {Z T E X F : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [Nontrivial E] in
/-- The actual combined implicit family supplies all mixed external and
tangential derivatives as joint C² functions on one fixed closed chart. -/
theorem contDiffOn_mixed_closed_chart_parameter
    {S : Set Z} {W : Set (Z × T)} (hS : IsOpen S) (hW : IsOpen W)
    (hSW : ∀ z ∈ S, (z,(0:T)) ∈ W)
    {r : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hr : ContDiff ℝ 3 r) (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (U : Z × T → OAI.Analysis.Normed.Function.Holder.C2Holder (F := F) hΩK α) (hU : ContDiffOn ℝ ∞ U W)
    {Q : Set X} (G : X → E) (hG : ContDiffOn ℝ 2 G Q)
    (hGQ : MapsTo G Q {x | r x ≤ 0})
    (f : Z × X → F) (A : T →L[ℝ] X)
    (he : ∀ z ∈ S, ∀ x (hx : x ∈ Q),
      (fun s : Z × T ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U ((z,0)+s))
        ⟨G x,hGQ hx⟩) =ᶠ[𝓝 0] fun s ↦ f (z+s.1,x+A s.2))
    (N : ℕ) (v : Fin N → Z × T) :
    ContDiffOn ℝ 2 (fun p : Z × X ↦ iteratedFDeriv ℝ N
      (fun s : Z × T ↦ f (p.1+s.1,p.2+A s.2)) 0 v) (S ×ˢ Q) := by
  have hd : ContDiffOn ℝ ∞ (fun z ↦ iteratedFDeriv ℝ N U (z,0) v) S :=
    (ParameterDeformation.contDiffOn_mixed_derivative hW hU N v).comp
      (contDiffOn_id.prodMk contDiffOn_const) hSW
  apply (OAI.Analysis.Normed.Function.Holder.C2Holder.contDiffOn_joint_value_closed_chart hS hr hreg
    (fun z ↦ iteratedFDeriv ℝ N U (z,0) v) (hd.of_le (by simp)) G hG hGQ).congr
  intro p hp
  rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ (hGQ hp.2)]
  exact (ParameterDeformation.value_mixed_parameter_eq_of_germ
    ((hU (p.1,0) (hSW p.1 hp.1)).contDiffAt (hW.mem_nhds (hSW p.1 hp.1)))
    ⟨G p.2,hGQ hp.2⟩ _ (he p.1 hp.1 p.2 hp.2) N v).symm

end OAI.Analysis.PDE.Dirichlet.ParameterDeformation
