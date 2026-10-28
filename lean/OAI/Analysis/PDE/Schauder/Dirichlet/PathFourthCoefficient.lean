import OAI.Analysis.PDE.Schauder.Calculus.Interior.PathData
import OAI.Analysis.Normed.Function.Holder.C2HolderCompactLimit
import OAI.Analysis.Normed.Function.Holder.DirichletFourthSourceHolder

noncomputable section
open Set Module
open scoped Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local instance fourthPathCoefficient1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fourthPathCoefficient1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fourthPathCoefficient2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthPathCoefficient2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthPathCoefficientEndGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance fourthPathCoefficientEndSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance

/-- The actual linearized determinant coefficient has one uniform Hölder
bound at the compactness exponent, derived only from the existing C² jets. -/
theorem InteriorThirdPathData.uniform_det_coefficient_half
    {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P}
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK) :
    ∃ N > 0, ∀ s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁,
      ∃ A : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E) (d.exponent/2),
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value A x =
          OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => B₀ y+s.u y) x)) ∧ ‖A‖ ≤ N := by
  have hg : ContDiff ℝ 1 (fun H : E →L[ℝ] E →L[ℝ] ℝ =>
      OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots H)) :=
    (OAI.Analysis.PDE.Dirichlet.contDiff_detRealOperator n 1).comp (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM (m := n) OAI.Analysis.Calculus.Quaternion.fourSlots).contDiff
  have hα : 0 ≤ d.exponent/2 := (half_pos d.exponent_pos).le
  have hd : 0 ≤ d.normBound := d.normBound_pos.le
  have hR : 0 ≤ 2*d.normBound := by positivity
  obtain ⟨C,hC,hcomp⟩ := OAI.Analysis.Normed.Function.Holder.HolderMap.exists_compose_contDiff_bound
    (X := {x | r x ≤ 0}) hg hα hR
  refine ⟨C*(1+2*d.normBound)+1,by positivity,?_⟩
  intro s
  let J := OAI.Analysis.Normed.Function.Holder.C2Holder.lowerHalf d.exponent_pos.le (d.jets s)
  let U := OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM J
  have hUn : ‖U‖ ≤ 2*d.normBound :=
    (OAI.Analysis.Normed.Function.Holder.C2Holder.norm_hessianCLM_apply_le J).trans
      ((OAI.Analysis.Normed.Function.Holder.C2Holder.norm_lowerHalf_le_twice d.exponent_pos.le (d.jets s)).trans
        (mul_le_mul_of_nonneg_left (d.jet_norm s) (by norm_num)))
  obtain ⟨A,hA,hAn⟩ := hcomp U hUn
  refine ⟨A,?_,?_⟩
  · intro x
    rw [hA]
    change OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative J x)) = _
    rw [OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative_lowerHalf,d.jet_second]
    rfl
  · calc
      ‖A‖ ≤ C*(1+‖U‖) := hAn
      _ ≤ C*(1+2*d.normBound) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hUn) hC
      _ ≤ C*(1+2*d.normBound)+1 := by linarith

end OAI.Analysis.PDE.Schauder
