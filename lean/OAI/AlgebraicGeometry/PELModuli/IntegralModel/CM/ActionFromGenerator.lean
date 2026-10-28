import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM.ActionGeneratorFaithfulness
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-! # Action From Generator -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM

noncomputable section

section

/-! A root of the integral primitive generator's minimal polynomial satisfies
all its integral polynomial relations. In particular the fixed reconstruction
polynomials satisfy the unit, product, and generator identities needed to
recover an integral action after division by the fixed conductor. -/

open _root_.Polynomial

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  (D : GeneratorReconstruction.CMIntegralGeneratorData E) {R : Type*} [Ring R] (u : R)
  (hu : aeval u (minpoly ℤ (D.generator : E)) = 0)

include hu

theorem GeneratorReconstruction.CMIntegralGeneratorData.polynomial_relation_transfer
    {p q : ℤ[X]} (h : aeval (D.generator : E) p = aeval (D.generator : E) q) :
    aeval u p = aeval u q := by
  have hz : aeval (D.generator : E) (p - q) = 0 := by rw [map_sub, h, sub_self]
  have hd := minpoly.isIntegrallyClosed_dvd D.generator.isIntegral_coe hz
  have he := aeval_eq_zero_of_dvd_aeval_eq_zero hd hu
  rwa [map_sub, sub_eq_zero] at he

theorem GeneratorReconstruction.CMIntegralGeneratorData.reconstruction_unit_at_root :
    aeval u (D.polynomial 1) = (D.conductor : R) := by
  have h := D.polynomial_relation_transfer u hu
    (p := D.polynomial 1) (q := C (D.conductor : ℤ)) (by
      rw [D.reconstruction, aeval_C]
      simp)
  simpa only [aeval_C, Int.cast_natCast, map_natCast] using h

theorem GeneratorReconstruction.CMIntegralGeneratorData.reconstruction_mul_at_root
    (a b : NumberField.RingOfIntegers E) :
    (D.conductor : R) * aeval u (D.polynomial (a * b)) =
      aeval u (D.polynomial a) * aeval u (D.polynomial b) := by
  have h := D.polynomial_relation_transfer u hu
    (p := C (D.conductor : ℤ) * D.polynomial (a * b))
    (q := D.polynomial a * D.polynomial b) (by
      simp only [map_mul, map_natCast, D.reconstruction]
      ring)
  simpa only [map_mul, aeval_C, map_natCast, Int.cast_natCast] using h

theorem GeneratorReconstruction.CMIntegralGeneratorData.reconstruction_generator_at_root :
    aeval u (D.polynomial D.generator) = (D.conductor : R) * u := by
  have h := D.polynomial_relation_transfer u hu
    (p := D.polynomial D.generator) (q := C (D.conductor : ℤ) * X) (by
      simp only [D.reconstruction, map_mul, aeval_X, map_natCast])
  simpa only [map_mul, aeval_C, aeval_X, map_natCast, Int.cast_natCast] using h

end

/-! Reconstruct the entire integral CM action from one primitive generator.
Only its minimal-polynomial equation and division of finitely many fixed
polynomials by the conductor are required. Ring identities are proved. -/

open _root_.Polynomial _root_.Module

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  (D : GeneratorReconstruction.CMIntegralGeneratorData E) {R : Type*} [Ring R] (u : R)
  (hu : aeval u (minpoly ℤ (D.generator : E)) = 0)
  (hc : Function.Injective (fun r : R => (D.conductor : R) * r))

def GeneratorReconstruction.CMIntegralGeneratorData.ringActionOfPolynomialDivision
    (v : NumberField.RingOfIntegers E →ₗ[ℤ] R)
    (hv : ∀ a, (D.conductor : R) * v a = aeval u (D.polynomial a)) :
    NumberField.RingOfIntegers E →+* R where
  toFun := v
  map_zero' := map_zero v
  map_add' := map_add v
  map_one' := by
    apply hc
    change (D.conductor : R) * v 1 = (D.conductor : R) * 1
    rw [hv, D.reconstruction_unit_at_root u hu, mul_one]
  map_mul' a b := by
    apply hc
    apply hc
    change (D.conductor : R) * ((D.conductor : R) * v (a * b)) =
      (D.conductor : R) * ((D.conductor : R) * (v a * v b))
    rw [hv, D.reconstruction_mul_at_root u hu, ← hv a, ← hv b]
    calc
      (D.conductor : R) * v a * ((D.conductor : R) * v b) =
          (D.conductor : R) * (v a * ((D.conductor : R) * v b)) := mul_assoc _ _ _
      _ = (D.conductor : R) * ((v a * (D.conductor : R)) * v b) :=
        congrArg (fun z => (D.conductor : R) * z) (mul_assoc _ _ _).symm
      _ = (D.conductor : R) * (((D.conductor : R) * v a) * v b) := by
        rw [← Nat.cast_comm D.conductor (v a)]
      _ = (D.conductor : R) * ((D.conductor : R) * (v a * v b)) := by rw [mul_assoc]

theorem GeneratorReconstruction.CMIntegralGeneratorData.ringActionOfPolynomialDivision_generator
    (v : NumberField.RingOfIntegers E →ₗ[ℤ] R)
    (hv : ∀ a, (D.conductor : R) * v a = aeval u (D.polynomial a)) :
    D.ringActionOfPolynomialDivision u hu hc v hv D.generator = u := by
  apply hc
  exact (hv D.generator).trans (D.reconstruction_generator_at_root u hu)

theorem GeneratorReconstruction.CMIntegralGeneratorData.basis_division_extends
    {ι : Type*} (b : Basis ι ℤ (NumberField.RingOfIntegers E)) (v : ι → R)
    (hv : ∀ i, (D.conductor : R) * v i = aeval u (D.polynomial (b i))) :
    ∀ a, (D.conductor : R) * Finite.Actions.basisExtension b v a = aeval u (D.polynomial a) := by
  let L := Finite.Actions.basisExtension b v
  have he : (D.conductor : ℤ) • L = (aeval u : ℤ[X] →ₐ[ℤ] R).toLinearMap.comp D.polynomial := by
    apply b.ext
    intro i
    simpa only [L, LinearMap.smul_apply, Finite.Actions.basisExtension_basis, zsmul_eq_mul,
      Int.cast_natCast, LinearMap.comp_apply, AlgHom.toLinearMap_apply] using hv i
  intro a
  have h := LinearMap.congr_fun he a
  simpa only [LinearMap.smul_apply, zsmul_eq_mul, Int.cast_natCast,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply] using h

include hu hc in
theorem GeneratorReconstruction.CMIntegralGeneratorData.existsUnique_ring_action_of_basis_division
    {ι : Type*} (b : Basis ι ℤ (NumberField.RingOfIntegers E)) (v : ι → R)
    (hv : ∀ i, (D.conductor : R) * v i = aeval u (D.polynomial (b i))) :
    ∃! ρ : NumberField.RingOfIntegers E →+* R, ρ D.generator = u := by
  let h := D.basis_division_extends u b v hv
  let ρ := D.ringActionOfPolynomialDivision u hu hc (Finite.Actions.basisExtension b v) h
  have hρ : ρ D.generator = u := D.ringActionOfPolynomialDivision_generator u hu hc _ h
  refine ⟨ρ, hρ, fun σ hσ => ?_⟩
  exact D.ring_action_eq_of_generator σ ρ hc (hσ.trans hρ.symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM
