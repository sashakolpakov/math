import OAI.Analysis.PDE.Elliptic.Boundary.Third.LocalRecovery
import OAI.Analysis.PDE.Elliptic.Boundary.HalfPatch
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.DriftJet
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.HolderPullback
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.CutoffOperators

/-! A genuine local third-order boundary estimate. Tangential second-derivative
Schauder estimates and the normal differentiated equation control the entire
third derivative, with an arbitrarily small outer-cutoff error. -/

noncomputable section
open Set Metric InnerProductSpace
open scoped Matrix.Norms.Elementwise BoundedContinuousFunction
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder OAI.Analysis.PDE.Dirichlet

local instance thirdLocalFirstGroup {m : ℕ} : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance thirdLocalFirstSpace {m : ℕ} : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance thirdLocalSecondGroup {m : ℕ} : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance thirdLocalSecondSpace {m : ℕ} : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance

theorem uniform_boundary_third_schauder {m : ℕ} (hm : 3 ≤ m) (k : Fin m)
    {α ell Λ N μ ρ : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hell : 0 < ell) (hΛ : 0 ≤ Λ) (hN : 0 ≤ N) (hμ : 0 < μ) (hρ : 0 < ρ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ r < ρ/(Real.sqrt Λ+1) ∧ ∃ δ > 0,
      ∀ ε > 0, ∃ D > 0,
      ∀ A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α,
      ‖A‖ ≤ N → ∀ x₀ : EuclideanSpace ℝ (Fin m), x₀ k = 0 →
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x₀).PosDef →
      (∀ v : EuclideanSpace ℝ (Fin m), ell*‖v‖^2 ≤
        inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x₀) v)) →
      (∀ v : EuclideanSpace ℝ (Fin m),
        inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x₀) v) ≤ Λ*‖v‖^2) →
      (∀ x ∈ ball x₀ ρ, 0 ≤ x k → μ ≤ OAI.Analysis.Normed.Function.Holder.HolderMap.value A x k k) →
      ∃ L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
        (∃ c > 0, ∀ z, L z k = c*z k) ∧
        ‖L.toContinuousLinearMap‖ ≤ Real.sqrt Λ ∧
        ‖L.symm.toContinuousLinearMap‖ ≤ (Real.sqrt ell)⁻¹ ∧
        ∀ u : EuclideanSpace ℝ (Fin m) → ℝ, ContDiff ℝ 4 u →
        (∀ i, i ≠ k → ∀ x ∈ ball x₀ ρ, x k = 0 →
          OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1) x = 0) →
        ∀ F : Fin m → OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α,
        ∀ H M Q, 0 ≤ H → 0 ≤ M → 0 ≤ Q → (∀ i, ‖F i‖ ≤ Q) →
        (∀ i, i ≠ k → ∀ x ∈ ball x₀ ρ, 0 ≤ x k →
          |OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1) x| ≤ M) →
        (∀ i, ∀ x ∈ ball x₀ ρ, 0 < x k →
          OAI.Analysis.PDE.Schauder.nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A)
            (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1)) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value (F i) x) →
        (∀ i, i ≠ k → ∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
          ‖fderiv ℝ (fderiv ℝ (fun z => OAI.Analysis.PDE.Schauder.radialCutoff (1/2) z *
              OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1) (x₀+L (r • z)))) x -
            fderiv ℝ (fderiv ℝ (fun z => OAI.Analysis.PDE.Schauder.radialCutoff (1/2) z *
              OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1) (x₀+L (r • z)))) y‖ ≤
                H*‖x-y‖^α) →
        (∀ x ∈ ball x₀ δ, 0 ≤ x k →
          ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤ ε*H+D*(Q+M)) ∧
        ∀ x ∈ ball x₀ δ, 0 ≤ x k → ∀ y ∈ ball x₀ δ, 0 ≤ y k →
          ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x-
            fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y‖ ≤ (ε*H+D*(Q+M))*‖x-y‖^α := by
  classical
  let E := EuclideanSpace ℝ (Fin m)
  obtain ⟨C, hC, hthird⟩ := exists_local_third_holder (m := m) hα.le hμ hN
  obtain ⟨r, hr, hrone, hrnear, δ₀, hδ₀, hlocal⟩ :=
    OAI.Analysis.PDE.Schauder.uniform_boundary_local_jet_schauder_with_drift hm k hα hα1 hell hΛ hN
      (Nb := 0) le_rfl hρ
  let δ := min δ₀ ρ
  have hδ : 0 < δ := lt_min hδ₀ hρ
  refine ⟨r, hr, hrone, hrnear, δ, hδ, ?_⟩
  intro ε hε
  obtain ⟨D₀, hD₀, hlocal⟩ := hlocal (ε/C) (div_pos hε hC)
  refine ⟨C*(D₀+1), mul_pos hC (by linarith), ?_⟩
  intro A hAn x₀ hx₀ hA hlo hhi hdiag
  obtain ⟨L, hLn, hL, hLi, hlocal⟩ := hlocal A hAn x₀ hx₀ hA hlo hhi
  refine ⟨L, hLn, hL, hLi, ?_⟩
  intro u hu hz F H M Q hH hM hQ hFn hb he hcut
  let w (i : Fin m) := OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1)
  have hw (i) : ContDiff ℝ 3 (w i) :=
    OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (m := 3) (by norm_num) _
  have heclosed (i) : ∀ x ∈ ball x₀ ρ, 0 ≤ x k →
      OAI.Analysis.PDE.Schauder.nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A) (w i) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value (F i) x :=
    equation_on_nonnegative_coordinate_patch k isOpen_ball
      (continuous_nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A).continuous
        ((hw i).of_le (by norm_num))) (OAI.Analysis.Normed.Function.Holder.HolderMap.value (F i)).continuous (he i)
  let J := ε/C*H+D₀*(Q+M)
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have htangent (i) (hi : i ≠ k) :
      (∀ x ∈ ball x₀ δ, 0 ≤ x k → ‖fderiv ℝ (fderiv ℝ (w i)) x‖ ≤ J) ∧
      ∀ x ∈ ball x₀ δ, 0 ≤ x k → ∀ y ∈ ball x₀ δ, 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ (w i)) x-fderiv ℝ (fderiv ℝ (w i)) y‖ ≤ J*‖x-y‖^α := by
    obtain ⟨hj, hh⟩ := hlocal 0 (by simp) (w i) (hw i) (hz i hi)
      (F i) H M hH hM (hb i hi) (by
        intro x hx hxk
        change OAI.Analysis.PDE.Schauder.nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A) (w i) x =
          OAI.Analysis.Normed.Function.Holder.HolderMap.value (F i) x + fderiv ℝ (w i) x 0
        simpa only [map_zero, add_zero] using heclosed i x hx hxk) (hcut i hi)
    have hmore : ε/C*H+D₀*(‖F i‖+M) ≤ J := by
      dsimp only [J]
      gcongr
      exact hFn i
    constructor
    · intro x hx hxk
      exact (hj x ((ball_subset_ball (min_le_left _ _)) hx) hxk).2.2.trans hmore
    · intro x hx hxk y hy hyk
      exact (hh x ((ball_subset_ball (min_le_left _ _)) hx) hxk
        y ((ball_subset_ball (min_le_left _ _)) hy) hyk).trans
        (mul_le_mul_of_nonneg_right hmore (Real.rpow_nonneg (norm_nonneg _) _))
  let S : Set E := ball x₀ δ ∩ {x | 0 ≤ x k}
  have hSc (x : S) : (x : E) ∈ ball x₀ ρ :=
    (ball_subset_ball (min_le_right _ _)) x.property.1
  obtain ⟨T, hT, hTn⟩ := hthird S u (hu.of_le (by norm_num)) k A hAn (F k)
    J Q hJ hQ (hFn k)
    (fun i hi x => (htangent i hi).1 x x.property.1 x.property.2)
    (by
      intro i hi x y
      change _ ≤ J*dist (x : E) (y : E)^α
      rw [dist_eq_norm]
      exact (htangent i hi).2 x x.property.1 x.property.2 y y.property.1 y.property.2)
    (fun x => hdiag x (hSc x) x.property.2)
    (fun x => heclosed k x (hSc x) x.property.2)
  have hbudget : C*(J+Q) ≤ ε*H+(C*(D₀+1))*(Q+M) := by
    have hCe : C*(ε/C) = ε := by field_simp
    dsimp only [J]
    nlinarith [mul_nonneg hC.le hM]
  have hTbound : ‖T‖ ≤ ε*H+(C*(D₀+1))*(Q+M) := hTn.trans hbudget
  constructor
  · intro x hx hxk
    let xs : S := ⟨x, hx, hxk⟩
    rw [← hT xs]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le T xs).trans hTbound
  · intro x hx hxk y hy hyk
    let xs : S := ⟨x, hx, hxk⟩
    let ys : S := ⟨y, hy, hyk⟩
    rw [← hT xs, ← hT ys]
    have hh := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le T xs ys
    have hd : dist xs ys = ‖x-y‖ := by
      change dist x y = ‖x-y‖
      exact dist_eq_norm x y
    rw [hd] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hTbound (Real.rpow_nonneg (norm_nonneg _) α))

end OAI.Analysis.PDE.Elliptic
