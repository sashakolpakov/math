import OAI.Analysis.PDE.Weak.Boundary.NormalDiagonal
import OAI.Analysis.PDE.Weak.Boundary.Weak.Vector

/-! Full normal weak differentiation of the H¹ gradient, from its
tangential weak derivatives and the elliptic equation. -/

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem H1Zero.normal_gradient_derivative
    {Ω Ω₀ : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω) {p : H1Pair m}
    (hp : p ∈ H1Zero Ω₀) (k : Fin (m + 1))
    (a : Fin (m + 1) → Fin (m + 1) → OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    {M D lam : ℝ} (hlam : 0 < lam)
    (hM : ∀ i j x, ‖a i j x‖ ≤ M)
    (hD : ∀ i j l x, ‖fderiv ℝ (a i j) x (Pi.single l 1)‖ ≤ D)
    (hpos : ∀ x, lam ≤ a k k x)
    (H : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m) (hH : MemLp H 2 volume)
    (hcoef : ∀ x i, H x i = ∑ j, a i j x * p.2 x j)
    (f : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hf : MemLp f 2 volume)
    (hweak : WeakDivergenceEquation Ω H f)
    (g : Fin (m + 1) → OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m)
    (hg : ∀ i, MemLp (g i) 2 volume)
    (hd : ∀ i, i ≠ k → HasWeakDirectionalDerivativeOn volume Ω (Pi.single i 1) p.2 (g i)) :
    ∃ G : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m, MemLp G 2 volume ∧
      HasWeakDirectionalDerivativeOn volume Ω (Pi.single k 1) p.2 G := by
  obtain ⟨G, hG, hGD⟩ := OAI.Analysis.PDE.Weak.H1Zero.normal_diagonal_derivative hΩ hp k a ha hlam hM hD hpos
    H hH hcoef f hf hweak g hg hd
  let W : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m :=
    fun x => WithLp.toLp 2 (fun j => if j = k then G x else g j x k)
  have hW : MemLp W 2 volume := by
    apply MemLp.of_eval_piLp
    intro j
    by_cases hj : j = k
    · subst j
      simpa [W] using hG
    · simpa [W, hj] using memLp_cell_component (hg j) k
  refine ⟨W, hW, OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivativeOn.of_scalar_components (Lp.memLp p.2) hW ?_⟩
  intro j
  by_cases hj : j = k
  · subst j
    simpa [W] using hGD
  · simpa [W, hj] using
      OAI.Analysis.PDE.Weak.H1Zero.mixed_weak_derivative hΩ hp j k (g j) (hg j) (hd j hj)

end OAI.Analysis.PDE.Weak
