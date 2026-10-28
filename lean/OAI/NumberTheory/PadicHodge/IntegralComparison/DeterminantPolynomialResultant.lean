import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Charpoly.Basic

/-! # Determinant Polynomial Resultant -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DeterminantPolynomialResultant

noncomputable section

/-! The determinant of a polynomial in an endomorphism is the resultant
of its characteristic polynomial and that polynomial. A split-polynomial
version applies to any multiplicative homogeneous scalar-valued map. -/

open _root_.Polynomial
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K]

theorem monic_resultant_right_degree (W R : Polynomial K) (hW : W.Monic)
    (n : ℕ) (hn : R.natDegree ≤ n) :
    W.resultant R W.natDegree n = W.resultant R := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [resultant_add_right_deg _ _ _ _ _ le_rfl, coeff_natDegree, hW.leadingCoeff, one_pow, one_mul]

theorem resultant_eq_multiplicative_eval {A : Type*} [Ring A] [Algebra K A]
    (D : A →* K) (F : A) (W : Polynomial K) (hW : W.Monic)
    (hscalar : ∀ c : K, D (algebraMap K A c) = c ^ W.natDegree)
    (hshift : ∀ c : K, W.eval c = D (algebraMap K A c - F))
    (R : Polynomial K) (hR : R.Splits) :
    W.resultant R = D (Polynomial.aeval F R) := by
  induction hR using Submonoid.closure_induction with
  | mem P hP =>
    obtain (⟨c, rfl⟩ | ⟨a, rfl⟩) := hP
    · rw [natDegree_C, resultant_C_zero_right, aeval_C, hscalar]
    · rw [show X + C a = X - C (-a) by rw [map_neg, sub_neg_eq_add]]
      rw [natDegree_X_sub_C, resultant_X_sub_C_right _ _ _ le_rfl,
        map_sub, aeval_X, aeval_C]
      have he : F - algebraMap K A (-a) =
          algebraMap K A (-1) * (algebraMap K A (-a) - F) := by
        simp only [map_neg, map_one, neg_one_mul, neg_sub]
      rw [he, map_mul, hscalar, ← hshift]
  | one => simp only [natDegree_one, resultant_one_right, pow_zero, map_one]
  | mul P Q _ _ ihP ihQ =>
    rw [← monic_resultant_right_degree W (P * Q) hW (P.natDegree + Q.natDegree) natDegree_mul_le,
      resultant_mul_right W P Q W.natDegree le_rfl, ihP, ihQ, map_mul, map_mul]

theorem det_aeval_of_splits {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (R : Polynomial K) (hR : R.Splits) :
    (Polynomial.aeval T R).det = T.charpoly.resultant R := by
  symm
  apply resultant_eq_multiplicative_eval LinearMap.det T T.charpoly T.charpoly_monic
    (fun c => ?_) (fun c => T.eval_charpoly c) R hR
  rw [LinearMap.charpoly_natDegree]
  change LinearMap.det (c • (1 : Module.End K V)) = _
  rw [LinearMap.det_smul, map_one, mul_one]

theorem aeval_baseChange {V : Type*} [AddCommGroup V] [Module K V]
    (L : Type*) [Field L] [Algebra K L] (T : Module.End K V) (R : Polynomial K) :
    (Polynomial.aeval T R).baseChange L =
      Polynomial.aeval (T.baseChange L) (R.map (algebraMap K L)) := by
  have h := Polynomial.aeval_algHom_apply (Module.End.baseChangeHom K L V) T R
  change Polynomial.aeval (T.baseChange L) R = (Polynomial.aeval T R).baseChange L at h
  rw [Polynomial.aeval_map_algebraMap]
  exact h.symm

theorem det_aeval {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (R : Polynomial K) :
    (Polynomial.aeval T R).det = T.charpoly.resultant R := by
  let L := AlgebraicClosure K
  apply (algebraMap K L).injective
  rw [← LinearMap.det_baseChange, aeval_baseChange]
  have h := det_aeval_of_splits (T.baseChange L) (R.map (algebraMap K L)) (IsAlgClosed.splits _)
  rw [LinearMap.charpoly_baseChange] at h
  rw [h, natDegree_map_eq_of_injective (algebraMap K L).injective,
    natDegree_map_eq_of_injective (algebraMap K L).injective, resultant_map_map]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DeterminantPolynomialResultant
