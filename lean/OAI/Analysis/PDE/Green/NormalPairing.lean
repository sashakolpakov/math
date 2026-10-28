import OAI.Analysis.PDE.Green.SmallGreen
import OAI.Analysis.PDE.Green.GreenAlgebra

/-! The real conormal flux equals the quaternionic normal-row pairing. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Matrix OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Matrix.Norms.Elementwise

theorem realCoefficients_bilinear {n s : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (e : Fin s → Quaternion ℝ)
    (ξ η : Fin n × Fin s → ℝ) :
    (∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e A p q * (ξ p * η q)) =
      ((star (OAI.Analysis.Calculus.Quaternion.gradientMap e ξ) ᵥ* A) ⬝ᵥ OAI.Analysis.Calculus.Quaternion.gradientMap e η).re := by
  simp only [dotProduct, Matrix.vecMul, OAI.Analysis.Calculus.Quaternion.gradientMap, Pi.star_apply, star_sum,
    Quaternion.star_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, OAI.LinearAlgebra.Moore.quaternion_re_sum, Quaternion.re_smul, OAI.Analysis.Calculus.Quaternion.realCoefficients,
    Fintype.sum_prod_type, smul_eq_mul]
  symm
  calc
    _ = ∑ j, ∑ i, ∑ α, ∑ β,
        ξ (i, α) * (η (j, β) * (star (e α) * A i j * e β).re) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro β _
      ring
    _ = ∑ i, ∑ j, ∑ α, ∑ β,
        ξ (i, α) * (η (j, β) * (star (e α) * A i j * e β).re) := by
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ α, ∑ j, ∑ β,
        ξ (i, α) * (η (j, β) * (star (e α) * A i j * e β).re) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro β _
      ring

theorem normalRealFlux_quaternion {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (r u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
    normalRealFlux OAI.Analysis.PDE.Dirichlet.coordinateVector (fun p q y => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A y) p q) r u x =
      ((star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ᵥ* A x) ⬝ᵥ OAI.Analysis.PDE.Dirichlet.quaternionGradient e u x).re := by
  change normalRealFlux OAI.Analysis.PDE.Dirichlet.coordinateVector (fun p q y => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A y) p q) r u x =
    ((star (OAI.Analysis.Calculus.Quaternion.gradientMap e (fun p => fderiv ℝ r x (OAI.Analysis.PDE.Dirichlet.coordinateVector p))) ᵥ* A x) ⬝ᵥ
      OAI.Analysis.Calculus.Quaternion.gradientMap e (fun p => fderiv ℝ u x (OAI.Analysis.PDE.Dirichlet.coordinateVector p))).re
  rw [← realCoefficients_bilinear]
  simp only [normalRealFlux, realFlux, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem norm_quaternion_re_le (q : Quaternion ℝ) : ‖q.re‖ ≤ ‖q‖ := by
  simpa only [Quaternion.inner_def, star_one, mul_one, norm_one, mul_one] using
    norm_inner_le_norm (𝕜 := ℝ) q (1 : Quaternion ℝ)

theorem quaternion_dotProduct_norm_le {ι : Type*} [Fintype ι]
    (u v : ι → Quaternion ℝ) :
    ‖u ⬝ᵥ v‖ ≤ (Fintype.card ι : ℝ) * ‖u‖ * ‖v‖ := by
  classical
  calc
    _ ≤ ∑ i, ‖u i * v i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, ‖u‖ * ‖v‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul (norm_le_pi_norm u i) (norm_le_pi_norm v i)
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp [mul_assoc]

theorem normalRealFlux_norm_le {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (r u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
    ‖normalRealFlux OAI.Analysis.PDE.Dirichlet.coordinateVector (fun p q y => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A y) p q) r u x‖ ≤
      (n : ℝ) * ‖star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ᵥ* A x‖ * ‖OAI.Analysis.PDE.Dirichlet.quaternionGradient e u x‖ := by
  rw [normalRealFlux_quaternion]
  exact (norm_quaternion_re_le _).trans (by
    simpa using quaternion_dotProduct_norm_le
      (star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ᵥ* A x) (OAI.Analysis.PDE.Dirichlet.quaternionGradient e u x))

theorem normalRealFlux_bound {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (r u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)
    {ε G : ℝ} (hrow : ‖star (OAI.Analysis.PDE.Dirichlet.quaternionGradient e r x) ᵥ* A x‖ ≤ ε)
    (hgrad : ‖OAI.Analysis.PDE.Dirichlet.quaternionGradient e u x‖ ≤ G) :
    ‖normalRealFlux OAI.Analysis.PDE.Dirichlet.coordinateVector (fun p q y => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A y) p q) r u x‖ ≤
      (n : ℝ) * ε * G := by
  apply (normalRealFlux_norm_le e A r u x).trans
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul hrow hgrad (norm_nonneg _) ((norm_nonneg _).trans hrow)) (Nat.cast_nonneg n)

end OAI.Analysis.PDE.Green
