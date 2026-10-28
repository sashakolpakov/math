import OAI.Analysis.Fourier.WavePackets.Dirichlet.Closed
import OAI.Analysis.Normed.Function.Holder.C2HolderEquationLimit
import OAI.Analysis.PDE.Dirichlet.UnconditionalLinear

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore
open scoped ContDiff Matrix.Norms.Elementwise

variable {m : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Nontrivial V]
  [Fintype ι]
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b}
  {α : ℝ} {hΩK : {x | D.defining x < 0} ⊆ {x | D.defining x ≤ 0}}

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V] in
theorem PeriodicQuaternionicData.closed_subset_closure (D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b) :
    {x | D.defining x ≤ 0} ⊆ closure {x | D.defining x < 0} := by
  rw [OAI.Analysis.PDE.Weak.closure_strict_sublevel_of_regular D.defining
    (D.defining_smooth.of_le (by simp)) D.regular]

local notation "H" => OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α
local notation "X" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b

omit [FiniteDimensional ℝ P] in
theorem PeriodicQuaternionicSolution.full_jet_inverse
    [Nonempty {x | D.defining x ≤ 0}]
    (S : PeriodicQuaternionicSolution D) (hα : 0 < α) (hα1 : α < 1)
    (g : H) (hg : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value g)))
    (hg₂ : ∀ x : {x | D.defining x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative g x =
      fderiv ℝ (fderiv ℝ (fun y => D.background y + S.u y)) x) :
    (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.periodicMooreDirichletOperator
      (isOpen_lt D.defining_smooth.continuous continuous_const) D.closed_subset_closure
      (D.defining_periodic.comp (fun t => t < 0))
      (D.defining_periodic.comp (fun t => t ≤ 0)) hα.le OAI.Analysis.Calculus.Quaternion.fourSlots g hg) (0 : X)).IsInvertible := by
  have hH (x : {x | D.defining x ≤ 0}) :
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (OAI.Analysis.PDE.Dirichlet.quaternionHessianField hΩK α OAI.Analysis.Calculus.Quaternion.fourSlots (g + (0 : X).val)) x =
        OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => D.background y + S.u y) x := by
    simp only [ZeroMemClass.coe_zero,add_zero]
    exact OAI.Analysis.PDE.Dirichlet.quaternionHessianField_eq_of_secondDerivative_eq OAI.Analysis.Calculus.Quaternion.fourSlots g _ x (hg₂ x)
  obtain ⟨L,hL⟩ := OAI.Analysis.PDE.Dirichlet.exists_periodicMooreDirichlet_derivative_equiv_unconditional
    D.dimension e b D.compact D.defining_smooth D.defining_periodic D.bounded D.regular
    D.defining_positive D.closed_subset_closure hα hα1 (fun y => D.background y + S.u y)
    ((D.background_smooth.add S.smooth).of_le (by simp))
    (D.background_periodic.add S.periodic) S.closed_positive g hg (0 : X) hH
  exact ⟨L,hL.symm⟩

end OAI.Analysis.Fourier.WavePackets
