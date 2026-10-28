import OAI.RepresentationTheory.Weil.Local.GenerationSymplectic
import Mathlib.Algebra.Polynomial.Roots

/-! # Polynomial Matrix Avoidance -/

namespace OAI.RepresentationTheory.Weil.Local.PolynomialMatrixAvoidance.Construction

noncomputable section

/-! Simultaneously avoid finitely many singular matrix conditions along symmetric affine lines. -/

open _root_.Matrix _root_.Polynomial

variable {k : Type} [Field k] {n : ℕ}

def affineDeterminantPolynomial (A B : Matrix (Fin n) (Fin n) k) : k[X] :=
  (A.map Polynomial.C + (Polynomial.X : k[X]) • B.map Polynomial.C).det

theorem affineDeterminantPolynomial_eval (A B : Matrix (Fin n) (Fin n) k) (t : k) :
    (affineDeterminantPolynomial A B).eval t = (A + t • B).det := by
  change (Polynomial.evalRingHom t) (affineDeterminantPolynomial A B) = _
  rw [affineDeterminantPolynomial, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply]
  ring

theorem exists_parameter_all_polynomials_ne_zero [Infinite k]
    {ι : Type*} (s : Finset ι) (p : ι → k[X]) (hp : ∀ i ∈ s, p i ≠ 0) :
    ∃ t : k, ∀ i ∈ s, (p i).eval t ≠ 0 := by
  classical
  have hprod : ∏ i ∈ s, p i ≠ 0 := Finset.prod_ne_zero_iff.mpr hp
  have ht : ∃ t : k, (∏ i ∈ s, p i).eval t ≠ 0 := by
    by_contra! hzero
    apply hprod
    apply Polynomial.funext
    intro t
    simpa only [Polynomial.eval_zero] using hzero t
  obtain ⟨t, ht⟩ := ht
  refine ⟨t, ?_⟩
  rw [Polynomial.eval_prod, Finset.prod_ne_zero_iff] at ht
  exact ht

theorem exists_symmetric_all_determinants_ne_zero [Infinite k]
    {ι : Type*} (s : Finset ι) (A B : ι → Matrix (Fin n) (Fin n) k)
    (h : ∀ i ∈ s, ∃ X : Matrix (Fin n) (Fin n) k, X.IsSymm ∧ (A i + X * B i).det ≠ 0) :
    ∃ X : Matrix (Fin n) (Fin n) k, X.IsSymm ∧ ∀ i ∈ s, (A i + X * B i).det ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, isSymm_zero, by simp⟩
  | @insert i s his ih =>
    obtain ⟨X, hX, hXs⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    obtain ⟨Y, hY, hYi⟩ := h i (Finset.mem_insert_self i s)
    let p (j : ι) := affineDeterminantPolynomial (A j + X * B j) ((Y - X) * B j)
    have he (j : ι) (t : k) : (p j).eval t = (A j + (X + t • (Y - X)) * B j).det := by
      dsimp only [p]
      rw [affineDeterminantPolynomial_eval]
      congr 1
      rw [add_mul, smul_mul_assoc, add_assoc]
    have hp (j : ι) (hj : j ∈ insert i s) : p j ≠ 0 := by
      intro hp0
      rcases Finset.mem_insert.mp hj with hji | hj
      · subst j
        have hh := he i 1
        rw [hp0, Polynomial.eval_zero] at hh
        have hxy : X + (1 : k) • (Y - X) = Y := by simp
        rw [hxy] at hh
        exact hYi hh.symm
      · have hh := he j 0
        rw [hp0, Polynomial.eval_zero, zero_smul, add_zero] at hh
        exact hXs j hj hh.symm
    obtain ⟨t, ht⟩ := exists_parameter_all_polynomials_ne_zero (insert i s) p hp
    refine ⟨X + t • (Y - X), hX.add ((hY.sub hX).smul t), ?_⟩
    intro j hj
    rw [← he]
    exact ht j hj

end

end OAI.RepresentationTheory.Weil.Local.PolynomialMatrixAvoidance.Construction
