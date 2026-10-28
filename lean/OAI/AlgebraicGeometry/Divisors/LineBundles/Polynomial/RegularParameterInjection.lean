import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Regular Parameter Injection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.RegularParameterInjection.BundleCycles

noncomputable section

/-! A polynomial parameter is algebraically independent when it is
regular and the coefficient ring embeds into its zero fiber. -/

variable {R S : Type} [CommRing R] [CommRing S]
    (φ : R →+* S) (t : S) (J : Ideal S) (htJ : t ∈ J)

include htJ in
theorem polynomialEval_mod_parameter :
    (Ideal.Quotient.mk J).comp (Polynomial.eval₂RingHom φ t) =
      ((Ideal.Quotient.mk J).comp φ).comp Polynomial.constantCoeff := by
  apply Polynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    change Ideal.Quotient.mk J (φ r) = Ideal.Quotient.mk J (φ ((Polynomial.C r).coeff 0))
    rw [Polynomial.coeff_C_zero]
  · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    change Ideal.Quotient.mk J t = Ideal.Quotient.mk J (φ ((Polynomial.X : Polynomial R).coeff 0))
    rw [Polynomial.coeff_X_zero, map_zero, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr htJ

include htJ in
theorem polynomialEval_injective_of_regular_parameter (ht : t ∈ nonZeroDivisors S)
    (hφ : Function.Injective ((Ideal.Quotient.mk J).comp φ)) :
    Function.Injective (Polynomial.eval₂RingHom φ t) := by
  have hzero (a : Polynomial R) (ha : Polynomial.eval₂RingHom φ t a = 0) : a.coeff 0 = 0 := by
    apply hφ
    have he := DFunLike.congr_fun (polynomialEval_mod_parameter φ t J htJ) a
    change Ideal.Quotient.mk J (Polynomial.eval₂RingHom φ t a) =
      Ideal.Quotient.mk J (φ (a.coeff 0)) at he
    rw [ha, map_zero] at he
    exact he.symm.trans (map_zero ((Ideal.Quotient.mk J).comp φ)).symm
  apply (injective_iff_map_eq_zero (Polynomial.eval₂RingHom φ t)).mpr
  intro a
  induction a using Polynomial.recOnHorner with
  | M0 => intro _; rfl
  | MC a r ha hr _ =>
    intro h
    have h0 := hzero _ h
    rw [Polynomial.coeff_add, Polynomial.coeff_C_zero, ha, zero_add] at h0
    exact False.elim (hr h0)
  | MX a _ ih =>
    intro h
    rw [map_mul] at h
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] at h
    have ha := ih ((mem_nonZeroDivisors_iff.mp ht).2 _ h)
    rw [ha, zero_mul]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.RegularParameterInjection.BundleCycles
