import OAI.AlgebraicGeometry.Comparison.Betti.CovectorPurePolynomial
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! # Covector Complex Projection -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.CovectorComplexProjection.Holomorphic

noncomputable section

section

/-! The pure highest complex character makes each argument of a real multilinear covector complex-linear. -/

open scoped BigOperators

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  {n : ℕ} (ω : MultilinearMap ℝ (fun _ : Fin n => E) ℂ)

def covectorProjectionSum (s : Finset (Fin n)) (v : Fin n → E) : ℂ :=
  ∑ t ∈ s.powerset, CovectorPurePolynomial.Holomorphic.covectorProjectionTerm ω v t

theorem covectorProjectionSum_insert_rotate (s : Finset (Fin n)) (k : Fin n) (hk : k ∉ s)
    (v : Fin n → E) :
    covectorProjectionSum ω (insert k s) (Function.update v k (Complex.I • v k)) =
      Complex.I * covectorProjectionSum ω (insert k s) v := by
  unfold covectorProjectionSum
  rw [Finset.sum_powerset_insert hk, Finset.sum_powerset_insert hk,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  exact CovectorPurePolynomial.Holomorphic.covectorProjectionTerm_pair ω v t k (Finset.notMem_of_mem_powerset_of_notMem ht hk)

theorem covectorProjectionSum_rotate (k : Fin n) (v : Fin n → E) :
    covectorProjectionSum ω Finset.univ (Function.update v k (Complex.I • v k)) =
      Complex.I * covectorProjectionSum ω Finset.univ v := by
  have h := covectorProjectionSum_insert_rotate ω (Finset.univ.erase k) k
    (Finset.notMem_erase k Finset.univ) v
  simpa only [Finset.insert_erase (Finset.mem_univ k)] using h

variable [IsScalarTower ℝ ℂ E]

theorem homogeneous_covector_map_update_I
    (hω : ∀ (z : ℂˣ) (v : Fin n → E), ω (fun i => (z : ℂ) • v i) = (z : ℂ) ^ n * ω v)
    (k : Fin n) (v : Fin n → E) :
    ω (Function.update v k (Complex.I • v k)) = Complex.I * ω v := by
  have hs (w : Fin n → E) : covectorProjectionSum ω Finset.univ w = (2 : ℂ) ^ n * ω w := by
    simpa only [covectorProjectionSum, Finset.powerset_univ, CovectorPurePolynomial.Holomorphic.covectorProjectionTerm] using
      CovectorPurePolynomial.Holomorphic.covector_complex_projection_identity ω w (fun z => hω z w)
  have h := covectorProjectionSum_rotate ω k v
  rw [hs, hs] at h
  apply mul_left_cancel₀ (pow_ne_zero n (by norm_num : (2 : ℂ) ≠ 0))
  exact h.trans (by ring)

end

/-! A real multilinear covector with highest complex character is genuinely complex multilinear. -/

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {n : ℕ}
  (ω : MultilinearMap ℝ (fun _ : Fin n => E) ℂ)
  (hω : ∀ (z : ℂˣ) (v : Fin n → E), ω (fun i => (z : ℂ) • v i) = (z : ℂ) ^ n * ω v)

include hω in
theorem homogeneous_covector_map_update_smul_self (k : Fin n) (v : Fin n → E) (z : ℂ) :
    ω (Function.update v k (z • v k)) = z * ω v := by
  have hv : z • v k = z.re • v k + z.im • (Complex.I • v k) := by
    calc
      _ = ((z.re : ℂ) + (z.im : ℂ) * Complex.I) • v k :=
        congrArg (fun c : ℂ => c • v k) (Complex.re_add_im z).symm
      _ = _ := by
        have hs (r : ℝ) (x : E) : (r : ℂ) • x = r • x := algebraMap_smul ℂ r x
        rw [add_smul, mul_smul, hs, hs]
  rw [hv, ω.map_update_add, ω.map_update_smul, ω.map_update_smul,
    Function.update_eq_self, homogeneous_covector_map_update_I ω hω]
  simp only [Complex.real_smul]
  rw [← mul_assoc, ← add_mul, Complex.re_add_im]

include hω in
theorem homogeneous_covector_map_update_smul (k : Fin n) (v : Fin n → E) (z : ℂ) (x : E) :
    ω (Function.update v k (z • x)) = z * ω (Function.update v k x) := by
  simpa only [Function.update_self, Function.update_idem] using
    homogeneous_covector_map_update_smul_self ω hω k (Function.update v k x) z

def homogeneousComplexMultilinearMap : MultilinearMap ℂ (fun _ : Fin n => E) ℂ :=
  MultilinearMap.mk' (R := ℂ) ω
    (fun v k x y => ω.map_update_add v k x y)
    (fun v k z x => homogeneous_covector_map_update_smul ω hω k v z x)

theorem homogeneousComplexMultilinearMap_apply (v : Fin n → E) :
    homogeneousComplexMultilinearMap ω hω v = ω v := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.CovectorComplexProjection.Holomorphic
