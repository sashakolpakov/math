import OAI.Analysis.PDE.Schauder.Calculus.Boundary.NormalizedFamily
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.UniformFreeze

/-! A uniformly chosen scale at which every coefficient in an elliptic
Hölder family becomes an absorbable boundary-preserving perturbation. -/

noncomputable section
open Set Metric Matrix
open scoped Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

theorem nondivergenceOperator_congr_at {m : ℕ}
    (A B : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (x) (h : A x = B x) :
    nondivergenceOperator A u x = nondivergenceOperator B u x := by
  simp only [nondivergenceOperator, h]

structure BoundaryFrozenData {m : ℕ} {α : ℝ}
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (x₀ : EuclideanSpace ℝ (Fin m)) (k : Fin m) (r P ell Λ : ℝ) where
  L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)
  B : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α
  c : ℝ
  c_pos : 0 < c
  normal : ∀ x, L x k = c * x k
  norm_L : ‖L.toContinuousLinearMap‖ ≤ Real.sqrt Λ
  norm_inv : ‖L.symm.toContinuousLinearMap‖ ≤ (Real.sqrt ell)⁻¹
  norm_B : ‖B‖ ≤ 1
  small_B : P * (m : ℝ) * m * ‖B‖ * (1 + (3 : ℝ)^α) ≤ 1 / 2
  support_B : ∀ x, x ∉ closedBall 0 2 → OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = 0
  equation : ∀ (u : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ 2 u →
    ∀ x, ‖x‖ ≤ 1 →
      nondivergenceOperator (fun y => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y)
        (fun y => u (x₀ + L (r • y))) x =
      r^2 * nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A) u (x₀ + L (r • x))

theorem exists_uniform_boundary_frozen_data {m : ℕ} {α ell Λ N P ρ : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hell : 0 < ell) (hΛ : 0 ≤ Λ)
    (hN : 0 ≤ N) (hP : 0 ≤ P) (hρ : 0 < ρ) :
    ∃ r > 0, r < ρ ∧
      ∀ (A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α),
      ‖A‖ ≤ N → ∀ (x₀ : EuclideanSpace ℝ (Fin m)) (k : Fin m),
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x₀).PosDef →
      (∀ x : EuclideanSpace ℝ (Fin m), ell * ‖x‖^2 ≤
        inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x₀) x)) →
      (∀ x : EuclideanSpace ℝ (Fin m),
        inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x₀) x) ≤ Λ * ‖x‖^2) →
      Nonempty (BoundaryFrozenData A x₀ k r P ell Λ) := by
  let N' := ((m : ℝ)^2 * ((Real.sqrt ell)⁻¹)^2 * (1 + (Real.sqrt Λ)^α)) * N
  have hN' : 0 ≤ N' := by dsimp only [N']; positivity
  obtain ⟨r, hr, hrρ, hfreeze⟩ := exists_uniform_absorbable_halfspace_freezing
    (m := m) hα hα1 hN' hP hρ
  refine ⟨r, hr, hrρ, ?_⟩
  intro A hAn x₀ k hA hlower hupper
  obtain ⟨L, Q, c, hc, hnormal, hLn, hLin, hzero, hnorm, heq⟩ :=
    exists_boundary_normalized_holder_field hα.le hell hΛ hN A hAn x₀ k hA hlower hupper
  let A' := normalizedHolderCoefficient hα.le A x₀ L.toContinuousLinearMap Q
  obtain ⟨B, hBn, hBsmall, hBval, hBs⟩ := hfreeze A' hnorm hzero
  refine ⟨⟨L, B, c, hc, hnormal, hLn, hLin, hBn, hBsmall, hBs, ?_⟩⟩
  intro u hu x hx
  let w := fun y => u (x₀ + L y)
  have hw : ContDiff ℝ 2 w := hu.comp (contDiff_const.add L.contDiff)
  have hd := nondivergence_dilate (OAI.Analysis.Normed.Function.Holder.HolderMap.value A') w hw 0 x r
  simp only [zero_add] at hd
  calc
    _ = nondivergenceOperator (fun y => OAI.Analysis.Normed.Function.Holder.HolderMap.value A' (r • y)) (fun y => w (r • y)) x :=
      nondivergenceOperator_congr_at _ _ _ x (hBval x hx)
    _ = r^2 * nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A') w (r • x) := hd
    _ = _ := by rw [heq u hu]

end OAI.Analysis.PDE.Schauder
