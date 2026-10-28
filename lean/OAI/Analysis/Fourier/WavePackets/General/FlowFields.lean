import OAI.Analysis.Fourier.WavePackets.General.Family.Extensions
import OAI.Analysis.Fourier.WavePackets.General.FlowGeometry
import OAI.Analysis.Fourier.WavePackets.FlowParameterFields

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module Filter OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder
open OAI.Analysis.PDE.Dirichlet.ParameterDeformation
open scoped Topology ContDiff

variable {Z T : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {P V ι : Type*} {m : ℕ}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {D : Z → PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b} {z₀ : Z} {U C : Set Z}
  {G : LocalDirichletFamily D z₀ U}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4

structure GeneralFlowFields (A : SmoothFamilyCoefficients G C)
    (H : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b (D z₀).defining) (W : Set Z) (α : ℝ) where
  analytic : OAI.Analysis.PDE.Schauder.ParameterJetFields (D z₀).defining α (W ×ˢ {t : T | ‖t‖ < H.radius}) e b
  jacobian_value : ∀ p ∈ W ×ˢ {t : T | ‖t‖ < H.radius}, ∀ x : {x | (D z₀).defining x ≤ 0},
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (analytic.jacobian p) x = flowJacobian H.map A.jacobian (p,x)
  curvature_value : ∀ p ∈ W ×ˢ {t : T | ‖t‖ < H.radius}, ∀ x : {x | (D z₀).defining x ≤ 0},
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (analytic.curvature p) x = flowCurvature H.map A.jacobian A.curvature (p,x)
  background_value : ∀ p ∈ W ×ˢ {t : T | ‖t‖ < H.radius}, ∀ x : {x | (D z₀).defining x ≤ 0},
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (analytic.background p) x = flowPullback H.map A.background (p,x)
  source_value : ∀ p ∈ W ×ˢ {t : T | ‖t‖ < H.radius}, ∀ x : {x | (D z₀).defining x ≤ 0},
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (analytic.source p) x = flowPullback H.map A.source (p,x)

omit [CompleteSpace T] in
theorem nonempty_generalFlowFields (A : SmoothFamilyCoefficients G C)
    (H : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b (D z₀).defining)
    {W : Set Z} {α : ℝ} (hW : IsOpen W) (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    Nonempty (GeneralFlowFields A H W α) := by
  obtain ⟨F,hJ,hK,hB,hF⟩ := exists_flow_parameterJetFields H (D z₀).compact
    (D z₀).defining_smooth.continuous (D z₀).defining_periodic (D z₀).bounded
    hα hα1 hW A.jacobian A.curvature A.background A.source A.jacobian_smooth
    A.curvature_smooth A.background_smooth A.source_smooth A.jacobian_periodic
    A.curvature_periodic A.background_periodic A.source_periodic
  exact ⟨⟨F,hJ,hK,hB,hF⟩⟩

omit [CompleteSpace T] in
theorem GeneralFlowFields.base_values {A : SmoothFamilyCoefficients G C}
    {H : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b (D z₀).defining}
    {W : Set Z} {α : ℝ} (F : GeneralFlowFields A H W α)
    (hzW : z₀ ∈ W) (hzC : z₀ ∈ C) (x : {x | (D z₀).defining x ≤ 0}) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (F.analytic.jacobian (z₀,0)) x = ContinuousLinearMap.id ℝ E ∧
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (F.analytic.curvature (z₀,0)) x = 0 ∧
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (F.analytic.background (z₀,0)) x =
      fderiv ℝ (fderiv ℝ (D z₀).background) x ∧
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (F.analytic.source (z₀,0)) x = (D z₀).density x := by
  have hp : (z₀,(0:T)) ∈ W ×ˢ {t : T | ‖t‖ < H.radius} :=
    ⟨hzW,by simpa only [Set.mem_ofPred_eq,norm_zero] using H.radius_pos⟩
  have h := A.exact_germs z₀ hzC x x.property
  refine ⟨?_,?_,?_,?_⟩
  · rw [F.jacobian_value _ hp,flowJacobian_zero H.at_zero,h.1.eq_of_nhds]
    exact G.rawJacobian_base x.property
  · rw [F.curvature_value _ hp,flowCurvature_zero H.at_zero,h.2.1.eq_of_nhds]
    exact G.rawCurvature_base x.property
  · rw [F.background_value _ hp,flowPullback_zero H.at_zero,h.2.2.1.eq_of_nhds]
    exact G.rawBackground_base x.property
  · rw [F.source_value _ hp,flowPullback_zero H.at_zero,h.2.2.2.eq_of_nhds]
    exact G.rawSource_base x.property

omit [CompleteSpace T] in
theorem GeneralFlowFields.inverse_coefficient_values {A : SmoothFamilyCoefficients G C}
    {H : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b (D z₀).defining}
    {W : Set Z} {α : ℝ} (F : GeneralFlowFields A H W α)
    {z : Z} (hz : z ∈ U) (hzC : z ∈ C) {t : T}
    (hp : (z,t) ∈ W ×ˢ {t : T | ‖t‖ < H.radius})
    (x : {x | (D z₀).defining x ≤ 0}) (y : E)
    (hmap : H.map (t,x) = G.backward (z,y)) (hy : (D z).defining y ≤ 0) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (F.analytic.jacobian (z,t)) x = fderiv ℝ (G.flowInverse H z t) y ∧
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (F.analytic.curvature (z,t)) x = fderiv ℝ (fderiv ℝ (G.flowInverse H z t)) y ∧
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (F.analytic.background (z,t)) x = fderiv ℝ (fderiv ℝ (D z).background) y ∧
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (F.analytic.source (z,t)) x = (D z).density y := by
  have hx := (H.closed_domain t hp.2 x).mpr x.property
  have hback : G.forward (z,H.map (t,x)) = y := by
    rw [hmap]
    exact G.forward_backward (z,y) (G.target_closed ⟨hz,hy⟩)
  have he := A.exact_germs z hzC (H.map (t,x)) hx
  have hj : A.jacobian (z,H.map (t,x)) = fderiv ℝ (fun q => G.backward (z,q)) y := by
    rw [he.1.eq_of_nhds]
    exact congrArg (fderiv ℝ (fun q => G.backward (z,q))) hback
  have hk : A.curvature (z,H.map (t,x)) = fderiv ℝ (fderiv ℝ (fun q => G.backward (z,q))) y := by
    rw [he.2.1.eq_of_nhds]
    exact congrArg (fderiv ℝ (fderiv ℝ (fun q => G.backward (z,q)))) hback
  have hi : ContDiffAt ℝ 2 (OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseFamily H.map t) (H.map (t,x)) :=
    (OAI.Analysis.PDE.Dirichlet.ParameterDeformation.contDiff_inverseFamily_slice (U := {s : T | ‖s‖ < H.radius})
      (Φ := H.map) H.inverse_smooth hp.2).contDiffAt.of_le (by norm_num)
  have hΨ : ContDiffAt ℝ 2 (fun q => G.backward (z,q)) y :=
    (G.backward_slice_contDiffAt hz hy).of_le (by norm_num)
  refine ⟨?_,?_,?_,?_⟩
  · rw [F.jacobian_value _ hp]
    exact flowJacobian_eq_fderiv H.map _ A.jacobian z t x y hmap.symm hi hΨ hj
  · rw [F.curvature_value _ hp]
    exact flowCurvature_eq_second_fderiv H.map _ A.jacobian A.curvature z t x y hmap.symm hi hΨ hj hk
  · rw [F.background_value _ hp]
    change A.background (z,H.map (t,x)) = _
    rw [he.2.2.1.eq_of_nhds]
    exact congrArg (fderiv ℝ (fderiv ℝ (D z).background)) hback
  · rw [F.source_value _ hp]
    change A.source (z,H.map (t,x)) = _
    rw [he.2.2.2.eq_of_nhds]
    exact congrArg (D z).density hback

end OAI.Analysis.Fourier.WavePackets
