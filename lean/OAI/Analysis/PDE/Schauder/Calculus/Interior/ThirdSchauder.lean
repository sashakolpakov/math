import OAI.Analysis.PDE.Schauder.Calculus.Interior.LocalJet
import OAI.Analysis.PDE.Schauder.Calculus.Interior.ThirdTensor

noncomputable section
open Set Metric
open scoped Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet

local instance interiorSchauderFirstGroup {m : ℕ} : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance interiorSchauderFirstSpace {m : ℕ} : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance interiorSchauderSecondGroup {m : ℕ} : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance interiorSchauderSecondSpace {m : ℕ} : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance interiorSchauderThirdGroup {m : ℕ} : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance interiorSchauderThirdSpace {m : ℕ} : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance

/-- Apply one common normalization to every differentiated equation.
The unknown third-order size appears only through the arbitrarily small
outer-cutoff error; the controlled terms use the original first jet and
the differentiated sources. -/
theorem uniform_interior_third_schauder {m : ℕ} (hm : 3 ≤ m)
    {α ell Λ N ρ : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hell : 0 < ell) (hΛ : 0 ≤ Λ) (hN : 0 ≤ N) (hρ : 0 < ρ) :
    ∃ (r : ℝ), r > 0 ∧ r ≤ 1 ∧ r < ρ/(2*Real.sqrt Λ+1) ∧ ∃ δ > 0,
      ∀ ε > 0, ∃ D > 0,
      ∀ A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α,
      ‖A‖ ≤ N → ∀ x₀ : EuclideanSpace ℝ (Fin m),
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x₀).PosDef →
      (∀ x : EuclideanSpace ℝ (Fin m), ell*‖x‖^2 ≤
        inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x₀) x)) →
      (∀ x : EuclideanSpace ℝ (Fin m),
        inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x₀) x) ≤ Λ*‖x‖^2) →
      ∃ L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
        ‖L.toContinuousLinearMap‖ ≤ Real.sqrt Λ ∧
        ‖L.symm.toContinuousLinearMap‖ ≤ (Real.sqrt ell)⁻¹ ∧
      ∀ u : EuclideanSpace ℝ (Fin m) → ℝ, ContDiff ℝ 4 u →
      ∀ (F : Fin m → OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α) (B Q H : ℝ),
      0 ≤ B → 0 ≤ Q → 0 ≤ H → (∀ j, ‖F j‖ ≤ B) →
      (∀ x ∈ ball x₀ ρ, ‖fderiv ℝ u x‖ ≤ Q) →
      (∀ j x, x ∈ ball x₀ ρ → nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A)
        (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.basisFun (Fin m) ℝ j)) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value (F j) x) →
      (∀ j x y,
        ‖fderiv ℝ (fderiv ℝ (fun z => radialCutoff (1/2) z *
          OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.basisFun (Fin m) ℝ j) (x₀+L (r • z)))) x-
          fderiv ℝ (fderiv ℝ (fun z => radialCutoff (1/2) z *
          OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.basisFun (Fin m) ℝ j) (x₀+L (r • z)))) y‖ ≤ H*‖x-y‖^α) →
      (∀ x ∈ ball x₀ δ, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤ ε*H+D*(B+Q)) ∧
      (∀ x ∈ ball x₀ δ, ∀ y ∈ ball x₀ δ,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y‖ ≤
          (ε*H+D*(B+Q))*‖x-y‖^α) := by
  let b := EuclideanSpace.basisFun (Fin m) ℝ
  obtain ⟨r, hr, hrone, _, hrnear, δ, hδ, hlocal⟩ :=
    uniform_interior_local_jet_schauder hm (⟨0, by omega⟩ : Fin m) hα hα1 hell hΛ hN hρ
  refine ⟨r, hr, hrone, hrnear, δ, hδ, ?_⟩
  intro ε hε
  let ε' := ε/((m:ℝ)+1)
  have hε' : 0 < ε' := div_pos hε (by positivity)
  obtain ⟨D₀, hD₀, hestimate⟩ := hlocal ε' hε'
  let D := (m:ℝ)*D₀+1
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro A hAn x₀ hA hlower hupper
  obtain ⟨L, hL, hLi, hLest⟩ := hestimate A hAn x₀ hA hlower hupper
  refine ⟨L, hL, hLi, ?_⟩
  intro u hu F B Q H hB hQ hH hFn hDu heq hh
  have hu3 : ContDiff ℝ 3 u := hu.of_le (by norm_num)
  have hcomponent (j : Fin m) := hLest (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (b j))
    (OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (by norm_num) (b j)) (F j) H Q hH hQ (by
      intro x hx
      have hv := (fderiv ℝ u x).le_opNorm (b j)
      have hnorm : ‖b j‖ = 1 := b.norm_eq_one j
      have hw : |OAI.Analysis.PDE.Dirichlet.directionalDerivative u (b j) x| ≤ ‖fderiv ℝ u x‖ := by
        simpa only [OAI.Analysis.PDE.Dirichlet.directionalDerivative, Real.norm_eq_abs, hnorm, mul_one] using hv
      exact hw.trans (hDu x hx)) (heq j) (hh j)
  have hbudget : (m:ℝ)*(ε'*H+D₀*(B+Q)) ≤ ε*H+D*(B+Q) := by
    have he : (m:ℝ)*ε' ≤ ε := by
      dsimp only [ε']
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    have hh := mul_le_mul_of_nonneg_right he hH
    dsimp only [D]
    nlinarith
  have hcomponent_bound (j : Fin m) : ε'*H+D₀*(‖F j‖+Q) ≤ ε'*H+D₀*(B+Q) := by
    gcongr
    exact hFn j
  constructor
  · intro x hx
    have ht := third_norm_le_of_directional_hessians b u hu3 x (ε'*H+D₀*(B+Q)) (fun j =>
      ((hcomponent j).1 x hx).2.2.trans (hcomponent_bound j))
    have ht' : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤
        (m:ℝ)*(ε'*H+D₀*(B+Q)) := by
      simpa only [Fintype.card_fin] using ht
    exact ht'.trans hbudget
  · intro x hx y hy
    have ht := third_difference_le_of_directional_hessians b u hu3 x y
      ((ε'*H+D₀*(B+Q))*‖x-y‖^α) (by
        intro j
        exact ((hcomponent j).2 x hx y hy).trans
          (mul_le_mul_of_nonneg_right (hcomponent_bound j) (Real.rpow_nonneg (norm_nonneg _) _)))
    have ht' : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y‖ ≤
        ((m:ℝ)*(ε'*H+D₀*(B+Q)))*‖x-y‖^α := by
      simpa only [Fintype.card_fin, mul_assoc] using ht
    exact ht'.trans (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg (norm_nonneg _) _))

end OAI.Analysis.PDE.Schauder
