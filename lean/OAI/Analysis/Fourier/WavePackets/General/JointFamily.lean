import OAI.Analysis.Fourier.WavePackets.General.FlowIdentification
import OAI.Analysis.Fourier.WavePackets.Dirichlet.ParameterFamily
import OAI.Analysis.PDE.Dirichlet.Rough.Joint.GeometricFamilies
import OAI.Analysis.PDE.Schauder.Calculus.LatticeJets

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Metric Module Filter OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder
open OAI.Analysis.PDE.Dirichlet.ParameterDeformation
open scoped Topology ContDiff

variable {Z T : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {P V ι : Type*} {m : ℕ}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Nontrivial V] [Fintype ι]
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {D : Z → PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b} {z₀ : Z} {U : Set Z}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4
attribute [local instance] OAI.Analysis.PDE.Schauder.latticeJetsDualGroup OAI.Analysis.PDE.Schauder.latticeJetsDualSpace
  OAI.Analysis.PDE.Schauder.latticeJetsSecondGroup OAI.Analysis.PDE.Schauder.latticeJetsSecondSpace

/-- The actual Dirichlet solution family, pulled back by a local closure
diffeomorphism, has smooth combined parameter/spatial-flow families. The
implicit branch is constructed from the proved linear inverse and is
identified with independently chosen classical solutions by uniqueness. -/
theorem LocalDirichletFamily.hasJointGeometricSolutionFamiliesAt
    (G : LocalDirichletFamily D z₀ U) (S : DirichletSolutionFamily D)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hΩK : {x | (D z₀).defining x < 0} ⊆ {x | (D z₀).defining x ≤ 0}) :
    OAI.Analysis.PDE.Dirichlet.ParameterDeformation.HasJointGeometricSolutionFamiliesAt (T := T) e b (D z₀).defining
      (G.referenceValue S) hΩK α z₀ := by
  by_cases hne : Nonempty {x | (D z₀).defining x ≤ 0}
  · let := hne
    obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp (G.open_parameter.mem_nhds G.base_mem)
    have hρ : 0 < δ / 2 := half_pos hδ
    have hclosed : closedBall z₀ (δ/2) ⊆ U :=
      (closedBall_subset_ball (by linarith)).trans hsub
    obtain ⟨A⟩ := G.nonempty_smoothFamilyCoefficients (isCompact_closedBall z₀ (δ/2)) hclosed
    obtain ⟨J⟩ := OAI.Analysis.PDE.Schauder.nonempty_latticeJetLifts (by have := (D z₀).dimension; omega : 0 < m)
      e b (D z₀).compact (D z₀).defining_smooth (D z₀).defining_periodic
      (D z₀).bounded (D z₀).regular hΩK hα hα1.le
    intro H
    obtain ⟨F⟩ := nonempty_generalFlowFields A H
      (isOpen_ball (x := z₀) (ε := δ/2)) hα.le hα1.le
    have hp₀ : (z₀,(0:T)) ∈ ball z₀ (δ/2) ×ˢ {t : T | ‖t‖ < H.radius} :=
      ⟨mem_ball_self hρ,by simpa only [norm_zero,Set.mem_ofPred_eq] using H.radius_pos⟩
    have hb := F.base_values (mem_ball_self hρ) (mem_closedBall_self hρ.le)
    obtain ⟨w,W,hW,hW₀,hWsub,hw,_,hsolve⟩ := (S z₀).exists_positive_parameter_family
      F.analytic J hα hα1 (isOpen_ball.prod (isOpen_lt continuous_norm continuous_const)) hp₀
      (fun x => (hb x).1) (fun x => (hb x).2.1) (fun x => (hb x).2.2.1)
      (fun x => (hb x).2.2.2)
    let inc := (OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet (hΩK := hΩK) (α := α) e b).subtypeL
    refine ⟨fun p => inc (w p),W,hW,hW₀,inc.contDiff.comp_contDiffOn hw,?_⟩
    filter_upwards [hW.mem_nhds hW₀] with p hp
    intro x
    exact F.referenceValue_eq_of_branch J hα.le
      (hclosed (ball_subset_closedBall (hWsub hp).1))
      (ball_subset_closedBall (hWsub hp).1) (hWsub hp) (w p)
      (hsolve p hp).1 (hsolve p hp).2 S x
  · intro H
    refine ⟨fun _ => 0,univ,isOpen_univ,mem_univ _,contDiffOn_const,?_⟩
    filter_upwards [] with p
    intro x
    exact False.elim (hne ⟨x⟩)

end OAI.Analysis.Fourier.WavePackets
