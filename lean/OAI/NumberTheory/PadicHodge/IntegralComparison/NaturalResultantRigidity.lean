import OAI.NumberTheory.PadicHodge.IntegralComparison.ResultantNormRigidity
import Mathlib.NumberTheory.Padics.RingHoms

/-! # Natural Resultant Rigidity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NaturalResultantRigidity

noncomputable section

/-! Natural-coefficient polynomial tests with constant coefficient prime to
a different prime determine a monic p-adic polynomial. Constants 1+p*n
already give the required coefficient density. -/

open _root_.Polynomial
open scoped Classical

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.ResultantNormRigidity OAI.NumberTheory.PadicHodge.IntegralComparison.ResultantNorm.Rigidity

variable (ℓ p : ℕ) [Fact ℓ.Prime] [Fact p.Prime] (hℓp : ℓ ≠ p)

include hℓp in
theorem denseRange_progression : DenseRange (fun n : ℕ => ((1 + p * n : ℕ) : ℤ_[ℓ])) := by
  have hp : IsUnit (p : ℤ_[ℓ]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes (Fact.out : ℓ.Prime) (Fact.out : p.Prime)).mpr hℓp
  obtain ⟨u, hu⟩ := hp
  let e : ℤ_[ℓ] ≃ₜ ℤ_[ℓ] :=
    (ContinuousAddEquiv.mulLeft u).toHomeomorph.trans (Homeomorph.addLeft 1)
  have h := e.surjective.denseRange.comp (PadicInt.denseRange_natCast (p := ℓ)) e.continuous
  convert h using 1
  funext n
  change ((1 + p * n : ℕ) : ℤ_[ℓ]) = 1 + (u : ℤ_[ℓ]) * (n : ℤ_[ℓ])
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, hu]

def coefficient {n : ℕ} (i : Fin n) (a : ℕ) : ℕ := if i.val = 0 then 1 + p * a else a

include hℓp in
theorem coefficient_dense {n : ℕ} (i : Fin n) :
    DenseRange (fun a : ℕ => (coefficient p i a : ℤ_[ℓ])) := by
  by_cases hi : i.val = 0
  · simpa only [coefficient, hi, ite_true] using denseRange_progression ℓ p hℓp
  · simpa only [coefficient, hi, ite_false] using (PadicInt.denseRange_natCast (p := ℓ))

theorem map_ofFn_semiring {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+* B) (n : ℕ) (a : Fin n → A) :
    (ofFn n a).map f = ofFn n (fun i => f (a i)) := by
  ext i
  by_cases hi : i < n
  · simp only [coeff_map, ofFn_coeff_eq_val_of_lt _ hi]
  · simp only [coeff_map, ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hi), map_zero]

include hℓp in
theorem integral_tests (P Q : Polynomial ℚ_[ℓ]) (hP : P.Monic) (hQ : Q.Monic)
    (h : ∀ T : Polynomial ℕ, ¬ p ∣ T.coeff 0 →
      ‖P.resultant (T.map (Nat.castRingHom ℚ_[ℓ]))‖ =
        ‖Q.resultant (T.map (Nat.castRingHom ℚ_[ℓ]))‖) :
    ∀ T : Polynomial ℤ_[ℓ],
      ‖P.resultant (T.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]))‖ =
        ‖Q.resultant (T.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]))‖ := by
  intro T
  let n := T.natDegree + 1
  have hn : 0 < n := Nat.zero_lt_succ _
  have hc : Continuous (fun a : Fin n → ℤ_[ℓ] =>
      (fun i => algebraMap ℤ_[ℓ] ℚ_[ℓ] (a i))) := by
    apply continuous_pi
    intro i
    exact continuous_subtype_val.comp (continuous_apply i)
  have he : (fun a : Fin n → ℤ_[ℓ] =>
      ‖P.resultant (ofFn n (fun i => algebraMap ℤ_[ℓ] ℚ_[ℓ] (a i))) P.natDegree n‖) =
      fun a : Fin n → ℤ_[ℓ] =>
      ‖Q.resultant (ofFn n (fun i => algebraMap ℤ_[ℓ] ℚ_[ℓ] (a i))) Q.natDegree n‖ := by
    apply Continuous.ext_on (DenseRange.piMap (fun i : Fin n => coefficient_dense ℓ p hℓp i))
      ((ResultantNormRigidity.continuous_resultant_ofFn P n).comp hc).norm
      ((ResultantNormRigidity.continuous_resultant_ofFn Q n).comp hc).norm
    rintro _ ⟨a, rfl⟩
    let U : Polynomial ℕ := ofFn n (fun i => coefficient p i (a i))
    have hU : ¬p ∣ U.coeff 0 := by
      rw [ofFn_coeff_eq_val_of_lt _ hn]
      change ¬p ∣ 1 + p * a ⟨0, hn⟩
      simpa only [← Nat.dvd_add_iff_left (dvd_mul_right p (a ⟨0, hn⟩))] using
        (Fact.out : p.Prime).not_dvd_one
    have hm : U.map (Nat.castRingHom ℚ_[ℓ]) =
        ofFn n (fun i => algebraMap ℤ_[ℓ] ℚ_[ℓ] (coefficient p i (a i) : ℤ_[ℓ])) := by
      ext j
      dsimp only [U]
      rw [coeff_map]
      by_cases hj : j < n
      · rw [ofFn_coeff_eq_val_of_lt _ hj, ofFn_coeff_eq_val_of_lt _ hj]
        exact (map_natCast (algebraMap ℤ_[ℓ] ℚ_[ℓ]) (coefficient p ⟨j, hj⟩ (a ⟨j, hj⟩))).symm
      · rw [ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hj),
          ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hj), map_zero]
    change ‖P.resultant (ofFn n _) P.natDegree n‖ = ‖Q.resultant (ofFn n _) Q.natDegree n‖
    rw [ResultantNorm.Rigidity.resultant_right_degree P _ hP n (ofFn_natDegree_lt hn _).le,
      ResultantNorm.Rigidity.resultant_right_degree Q _ hQ n (ofFn_natDegree_lt hn _).le]
    exact (congrArg (fun V : Polynomial ℚ_[ℓ] => ‖P.resultant V‖) hm).symm.trans
      ((h U hU).trans (congrArg (fun V : Polynomial ℚ_[ℓ] => ‖Q.resultant V‖) hm))
  have ht := congrFun he (toFn n T)
  rw [← map_ofFn_semiring, ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_self _)] at ht
  rw [ResultantNorm.Rigidity.resultant_right_degree P _ hP n
      (natDegree_map_le.trans (Nat.le_succ _)),
    ResultantNorm.Rigidity.resultant_right_degree Q _ hQ n
      (natDegree_map_le.trans (Nat.le_succ _))] at ht
  exact ht

include hℓp in
theorem monic_eq_of_natural_resultant_norm (P Q : Polynomial ℚ_[ℓ])
    (hP : P.Monic) (hQ : Q.Monic) (hdeg : P.natDegree = Q.natDegree)
    (h : ∀ T : Polynomial ℕ, ¬p ∣ T.coeff 0 →
      ‖P.resultant (T.map (Nat.castRingHom ℚ_[ℓ]))‖ =
        ‖Q.resultant (T.map (Nat.castRingHom ℚ_[ℓ]))‖) : P = Q := by
  apply ResultantNormRigidity.monic_eq_of_integer_resultant_norm ℓ P Q hP hQ hdeg
  intro T
  have hT := integral_tests ℓ p hℓp P Q hP hQ h (T.map (Int.castRingHom ℤ_[ℓ]))
  have hm : (T.map (Int.castRingHom ℤ_[ℓ])).map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) =
      T.map (Int.castRingHom ℚ_[ℓ]) := by
    rw [Polynomial.map_map]
    congr 1
  exact (congrArg (fun V : Polynomial ℚ_[ℓ] => ‖P.resultant V‖) hm).symm.trans
    (hT.trans (congrArg (fun V : Polynomial ℚ_[ℓ] => ‖Q.resultant V‖) hm))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NaturalResultantRigidity
