import OAI.NumberTheory.Quaternion.Arithmetic.FiniteAdelicLattice

/-! # Finite Adelic Polynomial Values -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.FiniteAdelicPolynomialValues

noncomputable section

/-! A fixed denominator makes polynomial values integral on integral
adelic vectors. Invariant polynomials therefore have uniformly bounded
denominators on the rational lattices attached to adelic matrices. -/

open scoped Classical _root_.NumberField _root_.Matrix

variable {F : Type} [Field F] [NumberField F]

theorem exists_integral_adelic_polynomial_multiple {σ : Type*} (p : MvPolynomial σ F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ x : σ → ScalarApproximation.ScalarFiniteAdeles F,
      (∀ i, x i ∈ ScalarApproximation.integralScalarAdeles F) →
      algebraMap (𝓞 F) (ScalarApproximation.ScalarFiniteAdeles F) d *
        MvPolynomial.eval₂Hom (algebraMap F (ScalarApproximation.ScalarFiniteAdeles F)) x p ∈ ScalarApproximation.integralScalarAdeles F := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    obtain ⟨d, hd, hc⟩ := ScalarApproximation.exists_integralScalar_multiple F (algebraMap F (ScalarApproximation.ScalarFiniteAdeles F) c)
    refine ⟨d, hd, fun x _ => ?_⟩
    simpa only [MvPolynomial.eval₂Hom_C] using hc
  | add p q hp hq =>
    obtain ⟨d, hd, hdp⟩ := hp
    obtain ⟨e, he, heq⟩ := hq
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    intro x hx
    let ev := MvPolynomial.eval₂Hom (algebraMap F (ScalarApproximation.ScalarFiniteAdeles F)) x
    have h := (ScalarApproximation.integralScalarAdeles F).add_mem
      (FiniteAdelicLattice.integralScalarAdeles_scalar_mul e (hdp x hx))
      (FiniteAdelicLattice.integralScalarAdeles_scalar_mul d (heq x hx))
    change algebraMap (𝓞 F) (ScalarApproximation.ScalarFiniteAdeles F) (d * e) * ev (p + q) ∈ ScalarApproximation.integralScalarAdeles F
    rw [map_mul, map_add]
    convert h using 1
    change algebraMap (𝓞 F) (ScalarApproximation.ScalarFiniteAdeles F) d * algebraMap (𝓞 F) (ScalarApproximation.ScalarFiniteAdeles F) e *
      (ev p + ev q) = algebraMap (𝓞 F) (ScalarApproximation.ScalarFiniteAdeles F) e *
        (algebraMap (𝓞 F) (ScalarApproximation.ScalarFiniteAdeles F) d * ev p) +
      algebraMap (𝓞 F) (ScalarApproximation.ScalarFiniteAdeles F) d * (algebraMap (𝓞 F) (ScalarApproximation.ScalarFiniteAdeles F) e * ev q)
    ring
  | mul_X p i hp =>
    obtain ⟨d, hd, hdp⟩ := hp
    refine ⟨d, hd, ?_⟩
    intro x hx
    rw [map_mul, MvPolynomial.eval₂Hom_X', ← mul_assoc]
    exact (ScalarApproximation.integralScalarAdeles F).mul_mem (hdp x hx) (hx i)

theorem invariant_adelic_polynomial_rational_values {n : ℕ} (p : MvPolynomial (Fin n) F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧
      ∀ A : Matrix (Fin n) (Fin n) (ScalarApproximation.ScalarFiniteAdeles F),
        (∀ x : Fin n → F,
          MvPolynomial.eval₂Hom (algebraMap F (ScalarApproximation.ScalarFiniteAdeles F))
            (A *ᵥ FiniteAdelicLattice.rationalFiniteAdelicVectorMap n x) p =
          algebraMap F (ScalarApproximation.ScalarFiniteAdeles F) (MvPolynomial.eval x p)) →
        ∀ x ∈ FiniteAdelicLattice.finiteAdelicMatrixLattice A,
          (d : F) * MvPolynomial.eval x p ∈ (algebraMap (𝓞 F) F).range := by
  obtain ⟨d, hd, hp⟩ := exists_integral_adelic_polynomial_multiple p
  refine ⟨d, hd, ?_⟩
  intro A hA x hx
  apply (FiniteAdelicLattice.scalarFiniteAdele_integral_iff _).mp
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← hA x]
  exact hp (A *ᵥ FiniteAdelicLattice.rationalFiniteAdelicVectorMap n x) hx

end

end OAI.NumberTheory.Quaternion.Arithmetic.FiniteAdelicPolynomialValues
