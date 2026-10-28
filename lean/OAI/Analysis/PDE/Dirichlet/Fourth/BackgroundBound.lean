import OAI.Analysis.PDE.Dirichlet.Fourth.CoefficientJet
import OAI.Analysis.PDE.Dirichlet.Fourth.FieldBackground

noncomputable section
open scoped Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Nonlinear OAI.Analysis.PDE.Elliptic OAI.Analysis.Normed.Function.Holder OAI.Analysis.Normed.Function.Holder.HolderMap

variable {n : ℕ} {X : Type} [MetricSpace X] {α : ℝ}
local notation "E" => CoordinateSpace n 4
local notation "H2" => (E →L[ℝ] E →L[ℝ] ℝ)
local instance bgFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance bgFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance bgSecondGroup : NormedAddCommGroup H2 := inferInstance
local instance bgSecondSpace : NormedSpace ℝ H2 := inferInstance

def mooreTraceJetExpression (p : H2 × H2) : ℝ :=
  ∑ i : Fin n × Fin 4, ∑ j : Fin n × Fin 4,
    mooreCoefficientJetMap p.1 i j * p.2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

theorem contDiff_mooreTraceJetExpression (k : WithTop ℕ∞) :
    ContDiff ℝ k (mooreTraceJetExpression (n := n)) := by
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact (contDiff_pi.mp (contDiff_pi.mp
    ((contDiff_mooreCoefficientJetMap k).comp contDiff_fst) i) j).mul
    ((contDiff_snd.clm_apply contDiff_const).clm_apply contDiff_const)

/-- Uniform Hölder control of the actual linearized operator applied to
any fixed test function, from the two Hessian fields. -/
theorem exists_moore_trace_holder_bound (hα : 0 ≤ α) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U W : OAI.Analysis.Normed.Function.Holder.HolderMap X H2 α, ‖U‖ ≤ R → ‖W‖ ≤ R →
      ∃ F : OAI.Analysis.Normed.Function.Holder.HolderMap X ℝ α,
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value F x = mooreTraceJetExpression (OAI.Analysis.Normed.Function.Holder.HolderMap.value U x,OAI.Analysis.Normed.Function.Holder.HolderMap.value W x)) ∧ ‖F‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := OAI.Analysis.Normed.Function.Holder.HolderMap.exists_compose_contDiff_bound (X := X)
    (contDiff_mooreTraceJetExpression (n := n) 1) hα hR
  refine ⟨C*(1+R),by positivity,?_⟩
  intro U W hU hW
  have hn := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_pair_le_of_le hα hU hW
  obtain ⟨F,hF,hFn⟩ := hbound (OAI.Analysis.Normed.Function.Holder.HolderMap.pair U W) hn
  refine ⟨F,?_,hFn.trans (mul_le_mul_of_nonneg_left (by linarith) hC)⟩
  intro x
  simpa only [OAI.Analysis.Normed.Function.Holder.HolderMap.value_pair] using hF x

theorem mooreTraceJetExpression_actual (u w : E → ℝ) (x : E) :
    mooreTraceJetExpression (fderiv ℝ (fderiv ℝ u) x,fderiv ℝ (fderiv ℝ w) x) =
      indexedNondivergenceOperator
        (fun y => mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)) w x := rfl

end OAI.Analysis.PDE.Dirichlet
