import OAI.NumberTheory.PadicHodge.IntegralComparison.ResultantNorm
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.NhdsWithin
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.Rat

/-! # Resultant Norm Rigidity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ResultantNormRigidity

noncomputable section

/-! Integer polynomial tests suffice to recover a monic p-adic polynomial.
Rational denominators are cleared, then density is applied to finite vectors
of coefficients. -/

open _root_.Polynomial
open scoped Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.ResultantNorm.Rigidity

variable {K : Type*} [NontriviallyNormedField K]

theorem continuous_ofFn_coeff (n i : ℕ) :
    Continuous (fun a : Fin n → K => (ofFn n a).coeff i) := by
  classical
  by_cases h : i < n
  · simpa only [ofFn_coeff_eq_val_of_lt _ h] using (continuous_apply (⟨i, h⟩ : Fin n))
  · simpa only [ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt h)] using
      (continuous_const : Continuous (fun _ : Fin n → K => (0 : K)))

theorem continuous_resultant_ofFn (P : Polynomial K) (n : ℕ) :
    Continuous (fun a : Fin n → K => P.resultant (ofFn n a) P.natDegree n) := by
  classical
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  induction j using Fin.addCases with
  | left j =>
    simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
    change Continuous (fun a : Fin n → K =>
      if (i : ℕ) ∈ Set.Icc (j : ℕ) (j + n) then (ofFn n a).coeff (i - j) else 0)
    split_ifs
    · exact continuous_ofFn_coeff n _
    · exact continuous_const
  | right j =>
    simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
    change Continuous (fun _ : Fin n → K =>
      if (i : ℕ) ∈ Set.Icc (j : ℕ) (j + P.natDegree) then P.coeff (i - j) else 0)
    exact continuous_const

theorem map_ofFn {F : Type*} [Field F] (f : F →+* K) (n : ℕ) (a : Fin n → F) :
    (ofFn n a).map f = ofFn n (fun i => f (a i)) := by
  classical
  ext i
  by_cases hi : i < n
  · simp only [coeff_map, ofFn_coeff_eq_val_of_lt _ hi]
  · simp only [coeff_map, ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hi), map_zero]

theorem norm_resultant_eq_of_dense_subfield {F : Type*} [Field F]
    (f : F →+* K) (hf : DenseRange f) (P Q : Polynomial K) (hP : P.Monic) (hQ : Q.Monic)
    (h : ∀ R : Polynomial F, ‖P.resultant (R.map f)‖ = ‖Q.resultant (R.map f)‖) :
    ∀ R : Polynomial K, ‖P.resultant R‖ = ‖Q.resultant R‖ := by
  classical
  intro R
  let n := R.natDegree + 1
  have hn : 1 ≤ n := Nat.succ_le_succ (Nat.zero_le _)
  have he : (fun a : Fin n → K => ‖P.resultant (ofFn n a) P.natDegree n‖) =
      fun a : Fin n → K => ‖Q.resultant (ofFn n a) Q.natDegree n‖ := by
    apply Continuous.ext_on (DenseRange.piMap (fun _ : Fin n => hf))
      (continuous_resultant_ofFn P n).norm (continuous_resultant_ofFn Q n).norm
    rintro _ ⟨a, rfl⟩
    change ‖P.resultant (ofFn n (fun i => f (a i))) P.natDegree n‖ =
      ‖Q.resultant (ofFn n (fun i => f (a i))) Q.natDegree n‖
    rw [ResultantNorm.Rigidity.resultant_right_degree P _ hP _ (ofFn_natDegree_lt hn _).le,
      ResultantNorm.Rigidity.resultant_right_degree Q _ hQ _ (ofFn_natDegree_lt hn _).le, ← map_ofFn]
    exact h _
  have hh := congrFun he (toFn n R)
  rw [ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self _),
    ResultantNorm.Rigidity.resultant_right_degree P R hP n (Nat.le_succ _),
    ResultantNorm.Rigidity.resultant_right_degree Q R hQ n (Nat.le_succ _)] at hh
  exact hh

theorem rational_tests_of_integer_tests [CharZero K] (P Q : Polynomial K)
    (hdeg : P.natDegree = Q.natDegree)
    (h : ∀ R : Polynomial ℤ,
      ‖P.resultant (R.map (Int.castRingHom K))‖ = ‖Q.resultant (R.map (Int.castRingHom K))‖) :
    ∀ R : Polynomial ℚ,
      ‖P.resultant (R.map (algebraMap ℚ K))‖ = ‖Q.resultant (R.map (algebraMap ℚ K))‖ := by
  intro R
  obtain ⟨b, hb, he⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) R
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have he' : (IsLocalization.integerNormalization (nonZeroDivisors ℤ) R).map
      (algebraMap ℤ ℚ) = C (b : ℚ) * R := by
    simpa only [← Int.cast_smul_eq_zsmul ℚ, Polynomial.smul_eq_C_mul] using he
  have heK := congrArg (Polynomial.map (algebraMap ℚ K)) he'
  have hcomp : (algebraMap ℚ K).comp (algebraMap ℤ ℚ) = Int.castRingHom K := by ext; simp
  rw [Polynomial.map_map, hcomp, Polynomial.map_mul, Polynomial.map_C, map_intCast] at heK
  have hh := h (IsLocalization.integerNormalization (nonZeroDivisors ℤ) R)
  rw [heK] at hh
  have hbK : (b : K) ≠ 0 := Int.cast_ne_zero.mpr hb0
  rw [natDegree_C_mul hbK, resultant_C_mul_right, resultant_C_mul_right, norm_mul, norm_mul, hdeg] at hh
  rw [hdeg]
  exact mul_left_cancel₀ (norm_ne_zero_iff.mpr (pow_ne_zero _ hbK)) hh

theorem monic_eq_of_integer_resultant_norm (p : ℕ) [Fact p.Prime]
    (P Q : Polynomial ℚ_[p]) (hP : P.Monic) (hQ : Q.Monic)
    (hdeg : P.natDegree = Q.natDegree)
    (h : ∀ R : Polynomial ℤ,
      ‖P.resultant (R.map (Int.castRingHom ℚ_[p]))‖ =
        ‖Q.resultant (R.map (Int.castRingHom ℚ_[p]))‖) : P = Q := by
  apply ResultantNorm.Rigidity.monic_eq_of_norm_resultant_eq P Q hP hQ hdeg
  apply norm_resultant_eq_of_dense_subfield (algebraMap ℚ ℚ_[p])
    (Padic.denseRange_ratCast p) P Q hP hQ
  exact rational_tests_of_integer_tests P Q hdeg h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ResultantNormRigidity
