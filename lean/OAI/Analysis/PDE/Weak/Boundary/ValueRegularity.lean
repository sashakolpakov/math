import OAI.Analysis.PDE.Weak.Boundary.RegularityVector
import OAI.Analysis.PDE.Weak.Boundary.H1WeakGradient

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem H1Zero.value_regular_of_gradient_regular
    {Ω Ω₀ : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {p : H1Pair m} (hp : p ∈ H1Zero Ω₀)
    {N : ℕ} (hgrad : WeakRegularity Ω N p.2) : WeakRegularity Ω (N + 1) p.1 := by
  intro j
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m + 1) => ℝ)).toContinuousLinearMap
  let pr : OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] ℝ := (ContinuousLinearMap.proj j).comp e
  refine ⟨pr.compLp p.2, ?_, hgrad.map pr⟩
  intro φ hφ hs hsub
  have he := OAI.Analysis.PDE.Weak.H1Zero.weak_derivative hp j φ hφ hs
  have hleft : (∫ x, (pr.compLp p.2) x * φ x) = ∫ x, p.2 x j * φ x := by
    apply integral_congr_ae
    filter_upwards [pr.coeFn_compLp p.2] with x hx
    rw [hx]
    rfl
  simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using hleft.trans he

end OAI.Analysis.PDE.Weak
