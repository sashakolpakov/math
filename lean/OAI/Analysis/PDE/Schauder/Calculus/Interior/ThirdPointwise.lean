import OAI.Analysis.PDE.Schauder.Calculus.Interior.ThirdJet
import OAI.Analysis.PDE.Dirichlet.InteriorPointwise

open Set Metric InnerProductSpace
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local instance thirdPointwiseFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance thirdPointwiseFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance thirdPointwiseSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdPointwiseSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdPointwiseThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdPointwiseThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- Interior third-order estimate for an actual differentiated system.
The only uncontrolled quantity is the actual third-jet Hölder norm, with
an arbitrarily small coefficient. The constants are chosen before the
coefficients, solution, and its third jet. -/
theorem interior_third_pointwise_schauder (hm : 3 ≤ m)
    {Ω K : Set E} (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K) {α ell Λ N ρ : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hell : 0 < ell)
    (hΛ : 0 ≤ Λ) (hN : 0 ≤ N) (hρ : 0 < ρ)
    (x₀ : E) (hball : closedBall x₀ ρ ⊆ K) :
    ∃ δ > 0, ∀ ε > 0, ∃ D > 0,
      ∀ A : E → E →L[ℝ] E,
      (∀ x ∈ K, (A x).toLinearMap.IsSymmetric) →
      (∀ x ∈ K, ‖A x‖ ≤ N) →
      (∀ x ∈ K, ∀ y ∈ K, ‖A x-A y‖ ≤ N*‖x-y‖^α) →
      (∀ z, ell*‖z‖^2 ≤ inner ℝ z (A x₀ z)) →
      (∀ z, inner ℝ z (A x₀ z) ≤ Λ*‖z‖^2) →
      ∀ u : E → ℝ, ContDiff ℝ 4 u → ∀ F : Fin m → E → ℝ,
      ∀ T : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x) →
      ∀ B Q, 0 ≤ B → 0 ≤ Q →
      (∀ x ∈ K, ‖fderiv ℝ u x‖ ≤ Q) →
      (∀ x ∈ K, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ Q) →
      (∀ j x, x ∈ K → ‖F j x‖ ≤ B) →
      (∀ j x, x ∈ K → ∀ y ∈ K, ‖F j x-F j y‖ ≤ B*‖x-y‖^α) →
      (∀ j x, x ∈ K → OAI.Analysis.PDE.Elliptic.ellipticTrace A
        (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.basisFun (Fin m) ℝ j)) x = F j x) →
      (∀ x ∈ closedBall x₀ δ, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤ ε*‖T‖+D*(B+Q)) ∧
      (∀ x ∈ closedBall x₀ δ, ∀ y ∈ closedBall x₀ δ,
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y‖ ≤
          (ε*‖T‖+D*(B+Q))*‖x-y‖^α) := by
  let b := EuclideanSpace.basisFun (Fin m) ℝ
  obtain ⟨δ,hδ,hlocal⟩ := OAI.Analysis.PDE.Dirichlet.interior_pointwise_schauder (hΩK := hΩK)
    hm hα hα1 hell hΛ hN hρ x₀ hball
  refine ⟨δ,hδ,?_⟩
  intro ε hε
  let ε' := ε/((m:ℝ)+1)
  have hε' : 0 < ε' := div_pos hε (by positivity)
  obtain ⟨D₀,hD₀,hest⟩ := hlocal ε' hε'
  let D := (m:ℝ)*(D₀+ε')+1
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨D,hD,?_⟩
  intro A hAs hAn hAh hlower hupper u hu F T hT B Q hB hQ hDu hD₂u hFn hFh heq
  have hu3 : ContDiff ℝ 3 u := hu.of_le (by norm_num)
  have hdir (j : Fin m) := exists_directional_C2Holder hΩ hΩK hα.le hQ u hu3 T hT hDu hD₂u
    (b j) (by simpa only [b.norm_eq_one] using (le_refl (1:ℝ)))
  choose U hUn hU₀ hU₁ hU₂ using hdir
  have hc j := hest A hAs hAn hAh hlower hupper
    (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (b j)) (OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (by norm_num) (b j))
    (F j) (U j) (hU₀ j) (hU₁ j) (hU₂ j) B Q hB hQ (by
      intro x hx
      exact ((fderiv ℝ u x).le_opNorm (b j)).trans
        (by simpa only [b.norm_eq_one,mul_one] using hDu x hx)) (hFn j) (hFh j) (heq j)
  have hcb j : ε'*‖U j‖+D₀*(B+Q) ≤ ε'*(Q+‖T‖)+D₀*(B+Q) := by
    exact add_le_add (mul_le_mul_of_nonneg_left (hUn j) hε'.le) le_rfl
  have hbudget : (m:ℝ)*(ε'*(Q+‖T‖)+D₀*(B+Q)) ≤ ε*‖T‖+D*(B+Q) := by
    have he : (m:ℝ)*ε' ≤ ε := by
      dsimp only [ε']
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    have ht := mul_le_mul_of_nonneg_right he (norm_nonneg T)
    have hb : 0 ≤ (m:ℝ)*ε'*B := by positivity
    dsimp only [D]
    nlinarith
  constructor
  · intro x hx
    have ht := third_norm_le_of_directional_hessians b u hu3 x
      (ε'*(Q+‖T‖)+D₀*(B+Q)) (fun j => ((hc j).1 x hx).2.2.trans (hcb j))
    have ht' : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤
        (m:ℝ)*(ε'*(Q+‖T‖)+D₀*(B+Q)) := by
      simpa only [Fintype.card_fin] using ht
    exact ht'.trans hbudget
  · intro x hx y hy
    have ht := third_difference_le_of_directional_hessians b u hu3 x y
      ((ε'*(Q+‖T‖)+D₀*(B+Q))*‖x-y‖^α) (by
        intro j
        exact ((hc j).2 x hx y hy).trans
          (mul_le_mul_of_nonneg_right (hcb j) (Real.rpow_nonneg (norm_nonneg _) _)))
    have ht' : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y‖ ≤
        ((m:ℝ)*(ε'*(Q+‖T‖)+D₀*(B+Q)))*‖x-y‖^α := by
      simpa only [Fintype.card_fin,mul_assoc] using ht
    exact ht'.trans (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg (norm_nonneg _) _))

end OAI.Analysis.PDE.Schauder
