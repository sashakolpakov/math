import OAI.Analysis.PDE.Schauder.Calculus.Deformation.Differential
import OAI.Analysis.PDE.Dirichlet.C2HolderPeriodicDerivative

open Set Module
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ} {α : ℝ} {I : Set ℝ}
  {Φ : ℝ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4}
  {B₀ f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ}
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local notation "X" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b
local notation "H" => OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α
local instance inverseDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance inverseDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance inverseSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance inverseC2Group : NormedAddCommGroup H := inferInstance
local instance inverseC2Space : NormedSpace ℝ H := inferInstance
local instance inverseC2Module : Module ℝ H := inferInstance
local instance inverseC2AddZero : AddZeroClass H := inferInstance
local instance inverseC2Bounded : IsBoundedSMul ℝ H := NormedSpace.toIsBoundedSMul
local instance inverseC2Continuous : ContinuousSMul ℝ H := IsBoundedSMul.continuousSMul

/-- The transformed operator has exactly the original linearization. This
identity assumes only the actual C2 Holder jets, not C3 regularity. -/
theorem PeriodicDeformationFields.partial_fderiv_zero
    (C : PeriodicDeformationFields r α I Φ B₀ f e b) (J : LatticeJetLifts hΩK α e b)
    (hr : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r) (hα : 0 ≤ α) (hI : IsOpen I) (h0 : 0 ∈ I)
    (hΦ : ∀ x, Φ (0,x) = x)
    (hΩ : IsOpen {x | r x < 0}) (hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0})
    (hΩper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => r x < 0))
    (hKper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => r x ≤ 0))
    (g : H) (hg : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value g)))
    (v₀ : X) (hbase : C.fields.background 0 + J.second v₀ = OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM g) :
    (fderiv ℝ (C.periodicOperator J hr hα) (0,v₀)).comp
      (ContinuousLinearMap.inr ℝ ℝ X) =
        fderiv ℝ (OAI.Analysis.PDE.Dirichlet.periodicMooreDirichletOperator hΩ hclosure hΩper hKper hα OAI.Analysis.Calculus.Quaternion.fourSlots g hg) 0 := by
  ext w : 1
  apply Subtype.ext
  have hleft := C.coe_partial_fderiv_zero J hr hα hI h0 hΦ g v₀ w hbase
  have hright := OAI.Analysis.PDE.Dirichlet.fderiv_periodicMooreDirichletOperator_coe
    hΩ hclosure hΩper hKper hα OAI.Analysis.Calculus.Quaternion.fourSlots g hg (0 : X) w
  have heq : g + (0 : X).val = g := by simp only [ZeroMemClass.coe_zero,add_zero]
  exact hleft.trans ((congrArg
    (fun z : H => fderiv ℝ (OAI.Analysis.PDE.Dirichlet.mooreDirichletOperator hα OAI.Analysis.Calculus.Quaternion.fourSlots) z w.val) heq).symm.trans
      hright.symm)

theorem PeriodicDeformationFields.partial_fderiv_zero_isInvertible
    (C : PeriodicDeformationFields r α I Φ B₀ f e b) (J : LatticeJetLifts hΩK α e b)
    (hr : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r) (hα : 0 ≤ α) (hI : IsOpen I) (h0 : 0 ∈ I)
    (hΦ : ∀ x, Φ (0,x) = x)
    (hΩ : IsOpen {x | r x < 0}) (hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0})
    (hΩper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => r x < 0))
    (hKper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x => r x ≤ 0))
    (g : H) (hg : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value g)))
    (v₀ : X) (hbase : C.fields.background 0 + J.second v₀ = OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM g)
    (hinv : (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.periodicMooreDirichletOperator hΩ hclosure hΩper hKper hα OAI.Analysis.Calculus.Quaternion.fourSlots g hg) 0).IsInvertible) :
    ((fderiv ℝ (C.periodicOperator J hr hα) (0,v₀)).comp
      (ContinuousLinearMap.inr ℝ ℝ X)).IsInvertible := by
  rw [C.partial_fderiv_zero J hr hα hI h0 hΦ hΩ hclosure hΩper hKper g hg v₀ hbase]
  exact hinv

end OAI.Analysis.PDE.Schauder
