import OAI.Analysis.PDE.Dirichlet.C2HolderQuaternion
import OAI.Analysis.Normed.Function.Holder.C2HolderPeriodicity

open Set Module
open scoped Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder

/-- The genuine continuous boundary Hessian, not a boundary derivative of
the zero extension, inherits the lattice periodicity of the potential. -/
theorem quaternionHessianField_latticePeriodic {n s : ℕ} {P V ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    {Ω K : Set (CoordinateSpace n s)} {hΩK : Ω ⊆ K} {α : ℝ}
    {e : CoordinateSpace n s ≃L[ℝ] P × V} {b : Basis ι ℝ P}
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ closure Ω)
    (hΩper : LatticePeriodic e b (fun x ↦ x ∈ Ω))
    (hKper : LatticePeriodic e b (fun x ↦ x ∈ K))
    (slots : Fin s → Q) (f : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (hf : LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value f))) :
    LatticePeriodic e b
      (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK α slots f))) := by
  apply OAI.Analysis.Normed.Function.Holder.latticePeriodic_boundary_field hΩK hKΩ hΩper hKper (hf.quaternionHessian slots)
  intro x hx
  rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ (hΩK hx)]
  exact quaternionHessianField_eq hΩ hΩK α slots f hx

end OAI.Analysis.PDE.Dirichlet
