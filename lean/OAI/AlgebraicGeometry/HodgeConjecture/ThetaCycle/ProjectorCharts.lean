import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MatrixCalculus
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! # Projector Charts -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ProjectorCharts.CM

noncomputable section

/-! ThetaCycle: recover period matrices continuously from nearby graph projectors. -/

open scoped Classical _root_.Matrix _root_.Topology _root_.Matrix.Norms.Elementwise
open Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def graphTop (P : Matrix (Sum ι ι) (Sum ι ι) ℂ) (Z : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (P * Matrix.fromRows Z 1).toRows₁

def graphBottom (P : Matrix (Sum ι ι) (Sum ι ι) ℂ) (Z : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (P * Matrix.fromRows Z 1).toRows₂

def projectorGraphChart (P : Matrix (Sum ι ι) (Sum ι ι) ℂ) (Z : Matrix ι ι ℂ) :
    Matrix ι ι ℂ := graphTop P Z * (graphBottom P Z)⁻¹

theorem graph_top_continuous (Z : Matrix ι ι ℂ) : Continuous (fun P => graphTop P Z) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun P : Matrix (Sum ι ι) (Sum ι ι) ℂ =>
    ∑ k, P (Sum.inl i) k * (Matrix.fromRows Z 1) k j)
  fun_prop

theorem graph_bottom_continuous (Z : Matrix ι ι ℂ) : Continuous (fun P => graphBottom P Z) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun P : Matrix (Sum ι ι) (Sum ι ι) ℂ =>
    ∑ k, P (Sum.inr i) k * (Matrix.fromRows Z 1) k j)
  fun_prop

theorem projector_chart_at_base (P : Matrix (Sum ι ι) (Sum ι ι) ℂ) (Z : Matrix ι ι ℂ)
    (h : P * Matrix.fromRows Z 1 = Matrix.fromRows Z 1) :
    graphTop P Z = Z ∧ graphBottom P Z = 1 ∧ projectorGraphChart P Z = Z := by
  have ht : graphTop P Z = Z :=
    congrArg (fun M : Matrix (Sum ι ι) ι ℂ => M.toRows₁) h
  have hb : graphBottom P Z = 1 :=
    congrArg (fun M : Matrix (Sum ι ι) ι ℂ => M.toRows₂) h
  exact ⟨ht, hb, by simp [projectorGraphChart, ht, hb]⟩

theorem projector_chart_continuousAt (P : Matrix (Sum ι ι) (Sum ι ι) ℂ) (Z : Matrix ι ι ℂ)
    (h : P * Matrix.fromRows Z 1 = Matrix.fromRows Z 1) :
    ContinuousAt (fun Q => projectorGraphChart Q Z) P := by
  have hb := (projector_chart_at_base P Z h).2.1
  have hd : (graphBottom P Z).det ≠ 0 := by rw [hb, Matrix.det_one]; exact one_ne_zero
  have hi : ContinuousAt (Inv.inv : Matrix ι ι ℂ → Matrix ι ι ℂ) (graphBottom P Z) :=
    continuousAt_matrix_inv _ (by simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hd)
  have hinv : ContinuousAt (fun Q => (graphBottom Q Z)⁻¹) P :=
    hi.comp (f := fun Q => graphBottom Q Z) (graph_bottom_continuous Z).continuousAt
  exact (graph_top_continuous Z).continuousAt.mul hinv

theorem projector_chart_eventually_invertible
    (P : Matrix (Sum ι ι) (Sum ι ι) ℂ) (Z : Matrix ι ι ℂ)
    (h : P * Matrix.fromRows Z 1 = Matrix.fromRows Z 1) :
    ∀ᶠ Q in 𝓝 P, (graphBottom Q Z).det ≠ 0 := by
  apply (graph_bottom_continuous Z).matrix_det.continuousAt.eventually_ne
  rw [(projector_chart_at_base P Z h).2.1, Matrix.det_one]
  exact one_ne_zero

/-- If the projected columns lie in the graph of Z, their chart matrix is Z
whenever their lower block is invertible. This applies to actual period subspaces. -/
theorem projector_chart_of_graph
    (P : Matrix (Sum ι ι) (Sum ι ι) ℂ) (Z₀ Z : Matrix ι ι ℂ)
    (hgraph : graphTop P Z₀ = Z * graphBottom P Z₀)
    (hdet : (graphBottom P Z₀).det ≠ 0) : projectorGraphChart P Z₀ = Z := by
  unfold projectorGraphChart
  rw [hgraph]
  exact Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_iff_ne_zero.mpr hdet)

/-- Convergent projectors give convergent period matrices in the fixed
reference coordinates; no convergence of the chosen rational bases is needed. -/
theorem period_matrices_tendsto_of_projectors
    {A : Type*} {l : Filter A}
    (P : A → Matrix (Sum ι ι) (Sum ι ι) ℂ) (Z : A → Matrix ι ι ℂ)
    (P₀ : Matrix (Sum ι ι) (Sum ι ι) ℂ) (Z₀ : Matrix ι ι ℂ)
    (hbase : P₀ * Matrix.fromRows Z₀ 1 = Matrix.fromRows Z₀ 1)
    (hP : Tendsto P l (𝓝 P₀))
    (hgraph : ∀ a, graphTop (P a) Z₀ = Z a * graphBottom (P a) Z₀) :
    Tendsto Z l (𝓝 Z₀) := by
  have hc := (projector_chart_continuousAt P₀ Z₀ hbase).tendsto.comp hP
  rw [(projector_chart_at_base P₀ Z₀ hbase).2.2] at hc
  apply hc.congr'
  filter_upwards [hP (projector_chart_eventually_invertible P₀ Z₀ hbase)] with a ha
  exact projector_chart_of_graph (P a) Z₀ (Z a) (hgraph a) ha

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ProjectorCharts.CM
