import OAI.Analysis.Fourier.WavePackets.General.FlowFields
import OAI.Analysis.PDE.Schauder.Calculus.LocalFamilyPushback

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
  {D : Z → PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b} {z₀ : Z} {U C W : Set Z}
  {G : LocalDirichletFamily D z₀ U} {α : ℝ}
  {hΩK : {x | (D z₀).defining x < 0} ⊆ {x | (D z₀).defining x ≤ 0}}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4
local notation "X" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b

omit [CompleteSpace T] in
theorem GeneralFlowFields.pushback_identified {A : SmoothFamilyCoefficients G C}
    {H : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b (D z₀).defining}
    (F : GeneralFlowFields A H W α) (J : OAI.Analysis.PDE.Schauder.LatticeJetLifts hΩK α e b) (hα : 0 ≤ α)
    {z : Z} (hz : z ∈ U) (hzC : z ∈ C) {t : T}
    (hp : (z,t) ∈ W ×ˢ {t : T | ‖t‖ < H.radius}) (w : X)
    (hzero : F.analytic.periodicOperator J (D z₀).defining_periodic hα ((z,t),w) = 0)
    (hpos : F.analytic.PositiveAt J hα ((z,t),w)) (S : PeriodicQuaternionicSolution (D z)) :
    ∀ y, (D z).defining y ≤ 0 →
      OAI.Analysis.PDE.Schauder.physicalPushback (D z).background (G.flowInverse H z t) w y =
        (D z).background y + S.u y := by
  have hc : MapsTo (G.flowInverse H z t) {y | (D z).defining y ≤ 0}
      {x | (D z₀).defining x ≤ 0} := fun y hy => G.flowInverse_into_closed H hz hp.2 hy
  have hv (y : E) (hy : (D z).defining y ≤ 0) :=
    F.inverse_coefficient_values hz hzC hp ⟨G.flowInverse H z t y,hc hy⟩ y
      (G.flowInverse_map H z hp.2 y) hy
  exact F.analytic.local_family_pushback_identified J hα (D z₀).defining_smooth.continuous
    (D z₀).defining_periodic hp w hzero hpos S (G.flowInverse H z t)
    (fun y hy => (G.flowInverse_contDiffAt H hz hp.2 hy).of_le (by simp))
    (fun y hy => G.flowInverse_into_domain H hz hp.2 hy) hc
    (fun y hy => G.flowInverse_into_boundary H hz hp.2 hy)
    (G.flowInverse_periodic H z hp.2)
    (fun y hy => (hv y hy).2.2.1) (fun y hy => (hv y hy).1)
    (fun y hy => (hv y hy).2.1) (fun y hy => (hv y hy).2.2.2)

omit [CompleteSpace T] in
theorem GeneralFlowFields.referenceValue_eq_of_branch {A : SmoothFamilyCoefficients G C}
    {H : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b (D z₀).defining}
    (F : GeneralFlowFields A H W α) (J : OAI.Analysis.PDE.Schauder.LatticeJetLifts hΩK α e b) (hα : 0 ≤ α)
    {z : Z} (hz : z ∈ U) (hzC : z ∈ C) {t : T}
    (hp : (z,t) ∈ W ×ˢ {t : T | ‖t‖ < H.radius}) (w : X)
    (hzero : F.analytic.periodicOperator J (D z₀).defining_periodic hα ((z,t),w) = 0)
    (hpos : F.analytic.PositiveAt J hα ((z,t),w)) (S : DirichletSolutionFamily D)
    (x : {x | (D z₀).defining x ≤ 0}) :
    OAI.Analysis.Normed.Function.Holder.C2Holder.value w.val x = G.referenceValue S (z,H.map (t,x)) := by
  have hx := (H.closed_domain t hp.2 x).mpr x.property
  let y := G.forward (z,H.map (t,x))
  have hy : (D z).defining y ≤ 0 := G.forward_closed z hz _ hx
  have hv := F.pushback_identified J hα hz hzC hp w hzero hpos (S z) y hy
  have hinv : G.flowInverse H z t y = x := by
    apply (H.bijective t hp.2).injective
    exact (G.flowInverse_map H z hp.2 y).trans
      (G.backward_forward (z,H.map (t,x)) (G.source_closed ⟨hz,hx⟩))
  change (D z).background y + OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value w.val)
    (G.flowInverse H z t y) = (D z).background y + (S z).u y at hv
  rw [hinv,OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply (x := (x:E)) _ x.property] at hv
  exact add_left_cancel hv

end OAI.Analysis.Fourier.WavePackets
