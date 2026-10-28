import OAI.Analysis.PDE.Dirichlet.C2HolderPeriodicDerivative

noncomputable section
open Set Module
open scoped ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {m s : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {Ω K : Set (CoordinateSpace m s)} {hΩK : Ω ⊆ K} {α : ℝ}
  {e : CoordinateSpace m s ≃L[ℝ] P × V} {b : Basis ι ℝ P}
local notation "H" => OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α
local notation "X" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b

local instance shiftFirstGroup : NormedAddCommGroup (CoordinateSpace m s →L[ℝ] ℝ) := inferInstance
local instance shiftFirstSpace : NormedSpace ℝ (CoordinateSpace m s →L[ℝ] ℝ) := inferInstance
local instance shiftSecondGroup : NormedAddCommGroup
    (CoordinateSpace m s →L[ℝ] CoordinateSpace m s →L[ℝ] ℝ) := inferInstance
local instance shiftSecondSpace : NormedSpace ℝ
    (CoordinateSpace m s →L[ℝ] CoordinateSpace m s →L[ℝ] ℝ) := inferInstance
local instance shiftC2Group : NormedAddCommGroup H := inferInstance
local instance shiftC2Space : NormedSpace ℝ H := inferInstance
local instance shiftC2AddZeroClass : AddZeroClass H := inferInstance
local instance shiftC2Module : Module ℝ H := inferInstance
local instance shiftC2Bounded : IsBoundedSMul ℝ H := NormedSpace.toIsBoundedSMul
local instance shiftC2Continuous : ContinuousSMul ℝ H := IsBoundedSMul.continuousSMul

omit [Fintype ι] in
/-- Changing the background from B to B+u and moving the base point to
zero leaves the actual Moore derivative unchanged. -/
theorem fderiv_periodicMooreDirichletOperator_shift
    (hΩ : IsOpen Ω) (hKΩ : K ⊆ closure Ω)
    (hΩper : LatticePeriodic e b (fun x ↦ x ∈ Ω))
    (hKper : LatticePeriodic e b (fun x ↦ x ∈ K))
    (hα : 0 ≤ α) (slots : Fin s → Q) (B g : H)
    (hB : LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value B)))
    (hg : LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value g)))
    (u : X) (he : g = B + u.val) :
    fderiv ℝ (periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα slots g hg) 0 =
      fderiv ℝ (periodicMooreDirichletOperator hΩ hKΩ hΩper hKper hα slots B hB) u := by
  ext w : 1
  apply Subtype.ext
  have hleft := fderiv_periodicMooreDirichletOperator_coe hΩ hKΩ hΩper hKper hα slots g hg (0 : X) w
  have hright := fderiv_periodicMooreDirichletOperator_coe hΩ hKΩ hΩper hKper hα slots B hB u w
  have heq : g + (0 : X).val = B + u.val := by simpa only [ZeroMemClass.coe_zero,add_zero] using he
  exact hleft.trans ((congrArg
    (fun z : H ↦ fderiv ℝ (mooreDirichletOperator hα slots) z w.val) heq).trans hright.symm)

end OAI.Analysis.PDE.Dirichlet
