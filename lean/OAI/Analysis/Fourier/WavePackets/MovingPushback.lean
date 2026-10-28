import OAI.Analysis.Fourier.WavePackets.PeriodicDirichlet
import OAI.Analysis.PDE.Schauder.Calculus.PhysicalPushback

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder
open scoped ContDiff ComplexOrder

variable {m : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 → ℝ} {α : ℝ}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4
local notation "X" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b

/-- Comparison identifies a pushed-forward Banach solution on a different
physical fiber. The inverse map needs smoothness only in that fiber and
continuity on its closure; no global diffeomorphism extension is assumed. -/
theorem movingPushback_identified
    {D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b} (S : PeriodicQuaternionicSolution D)
    (hr : Continuous r) (Ψ : E → E)
    (hΨ : ContDiffOn ℝ 2 Ψ {x | D.defining x < 0})
    (hΨc : ContinuousOn Ψ {x | D.defining x ≤ 0})
    (hopen : MapsTo Ψ {x | D.defining x < 0} {x | r x < 0})
    (hclosed : MapsTo Ψ {x | D.defining x ≤ 0} {x | r x ≤ 0})
    (hboundary : MapsTo Ψ {x | D.defining x = 0} {x | r x = 0})
    (hperiodic : ∀ l : Submodule.span ℤ (Set.range b), ∀ x,
      Ψ (x + e.symm ((l : P),0)) = Ψ x + e.symm ((l : P),0))
    (v : X)
    (hpos : ∀ x, D.defining x < 0 →
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.Analysis.PDE.Schauder.physicalPushback D.background Ψ v) x)).PosDef)
    (heq : ∀ x, D.defining x < 0 →
      OAI.LinearAlgebra.Moore.mooreDet m (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.Analysis.PDE.Schauder.physicalPushback D.background Ψ v) x) = D.density x) :
    ∀ x, D.defining x ≤ 0 → OAI.Analysis.PDE.Schauder.physicalPushback D.background Ψ v x = D.background x + S.u x := by
  have hu : ContDiffOn ℝ 2 (OAI.Analysis.PDE.Schauder.physicalPushback D.background Ψ v) {x | D.defining x < 0} :=
    (D.background_smooth.of_le (by simp)).contDiffOn.add
      ((OAI.Analysis.Normed.Function.Holder.C2Holder.contDiffOn_value (isOpen_lt hr continuous_const) v.val).comp hΨ hopen)
  have huc : ContinuousOn (OAI.Analysis.PDE.Schauder.physicalPushback D.background Ψ v) {x | D.defining x ≤ 0} :=
    D.background_smooth.continuous.continuousOn.add
      ((OAI.Analysis.Normed.Function.Holder.continuousOn_boundedZeroExtension _).comp hΨc hclosed)
  apply OAI.Analysis.PDE.Dirichlet.quaternionic_dirichlet_uniqueness_continuous_lattice D.dimension e b D.compact
    hu ((D.background_smooth.add S.smooth).of_le (by simp)).contDiffOn
    (D.defining_smooth.of_le (by simp)) huc
    (D.background_smooth.add S.smooth).continuous.continuousOn D.bounded
    D.defining_periodic (OAI.Analysis.PDE.Schauder.latticePeriodic_physicalPushback D.background_periodic hperiodic v)
    (D.background_periodic.add S.periodic)
    (fun x hx => D.defining_positive x hx.le) hpos S.admissible
    (fun x hx => (heq x hx).trans (S.equation x hx).symm)
  intro x hx
  have hx' : r (Ψ x) = 0 := hboundary hx
  unfold OAI.Analysis.PDE.Schauder.physicalPushback
  rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply (OAI.Analysis.Normed.Function.Holder.C2Holder.value v.val)
    (show Ψ x ∈ {x | r x ≤ 0} from hx'.le),S.boundary x hx,add_zero]
  have hz := v.property.1 (⟨Ψ x,hx'.le⟩ : {x | r x ≤ 0})
    (show Ψ x ∉ {x | r x < 0} by simp only [Set.mem_ofPred_eq,hx',lt_self_iff_false,not_false_eq_true])
  rw [hz,add_zero]

end OAI.Analysis.Fourier.WavePackets
