import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Lagrangians
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.RingTheory.Trace.Basic

/-! # Quadratic Model -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.QuadraticModel.CM

noncomputable section

section

/-!
ThetaCycle: present the actual CM field over its maximal real subfield in the
quadratic-algebra coordinates used by the native unitary splitting.
The chosen imaginary scalar is retained as the quadratic generator.
-/

open scoped Classical

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]

def cmRealElement (x : K) (hx : NumberField.IsCMField.complexConj K x = x) :
    NumberField.maximalRealSubfield K :=
  ⟨x, (NumberField.IsCMField.complexConj_eq_self_iff K x).mp hx⟩

def cmQuadraticParameter (δ : K) (hδ : NumberField.IsCMField.complexConj K δ = -δ) :
    NumberField.maximalRealSubfield K :=
  cmRealElement K (δ ^ 2) (by rw [map_pow, hδ]; ring)

theorem cm_quadratic_parameter_ne_zero (δ : K)
    (hδ : NumberField.IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0) :
    cmQuadraticParameter K δ hδ ≠ 0 := by
  intro h
  have hz := congrArg (fun x : NumberField.maximalRealSubfield K => (x : K)) h
  exact pow_ne_zero 2 hδ0 hz

def cmRealCoordinate (x : K) : NumberField.maximalRealSubfield K :=
  cmRealElement K ((x + NumberField.IsCMField.complexConj K x) / 2) (by
    rw [map_div₀, map_add, map_ofNat, NumberField.IsCMField.complexConj_apply_apply]
    ring)

def cmImaginaryCoordinate (δ : K)
    (hδ : NumberField.IsCMField.complexConj K δ = -δ) (x : K) :
    NumberField.maximalRealSubfield K :=
  cmRealElement K ((x - NumberField.IsCMField.complexConj K x) / (2 * δ)) (by
    rw [map_div₀, map_sub, map_mul, map_ofNat,
      NumberField.IsCMField.complexConj_apply_apply, hδ]
    rw [mul_neg, div_neg, ← neg_div, neg_sub])

def cmQuadraticMap (δ : K) (hδ : NumberField.IsCMField.complexConj K δ = -δ) :
    QuadraticAlgebra (NumberField.maximalRealSubfield K) (cmQuadraticParameter K δ hδ) 0 →ₐ[
      NumberField.maximalRealSubfield K] K :=
  QuadraticAlgebra.lift (R := NumberField.maximalRealSubfield K)
    (a := cmQuadraticParameter K δ hδ) (b := 0) (A := K) ⟨δ, by
    rw [zero_smul, add_zero]
    simp only [Algebra.smul_def, mul_one]
    exact (pow_two δ).symm⟩

theorem cm_quadratic_map_apply (δ : K) (hδ : NumberField.IsCMField.complexConj K δ = -δ)
    (x : QuadraticAlgebra (NumberField.maximalRealSubfield K) (cmQuadraticParameter K δ hδ) 0) :
    cmQuadraticMap K δ hδ x = (x.re : K) + (x.im : K) * δ := by
  change x.re • (1 : K) + x.im • δ = _
  simp only [Algebra.smul_def, mul_one]
  rfl

theorem cm_quadratic_map_star (δ : K) (hδ : NumberField.IsCMField.complexConj K δ = -δ)
    (x : QuadraticAlgebra (NumberField.maximalRealSubfield K) (cmQuadraticParameter K δ hδ) 0) :
    cmQuadraticMap K δ hδ (star x) =
      NumberField.IsCMField.complexConj K (cmQuadraticMap K δ hδ x) := by
  simp only [cm_quadratic_map_apply, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
    zero_mul, add_zero, map_add, map_mul, NumberField.IsCMField.complexConj_apply_eq_self,
    hδ, Subfield.coe_neg]
  ring

theorem cm_quadratic_map_bijective (δ : K)
    (hδ : NumberField.IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0) :
    Function.Bijective (cmQuadraticMap K δ hδ) := by
  constructor
  · intro x y h
    have hc := congrArg (NumberField.IsCMField.complexConj K) h
    simp only [cm_quadratic_map_apply] at h hc
    simp only [map_add, map_mul, NumberField.IsCMField.complexConj_apply_eq_self, hδ] at hc
    have hi : ((x.im : K) - (y.im : K)) * δ = 0 := by
      linear_combination (1 / 2 : K) * h - (1 / 2 : K) * hc
    have hi' : (x.im : K) = (y.im : K) :=
      sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_right hδ0)
    have hr : (x.re : K) = (y.re : K) := by
      rw [hi'] at h
      exact add_right_cancel h
    exact QuadraticAlgebra.ext (Subtype.ext hr) (Subtype.ext hi')
  · intro x
    refine ⟨⟨cmRealCoordinate K x, cmImaginaryCoordinate K δ hδ x⟩, ?_⟩
    rw [cm_quadratic_map_apply]
    change (x + NumberField.IsCMField.complexConj K x) / 2 +
      (x - NumberField.IsCMField.complexConj K x) / (2 * δ) * δ = x
    field_simp
    ring

/-- An actual algebra isomorphism, preserving the chosen imaginary generator. -/
def cmQuadraticEquiv (δ : K) (hδ : NumberField.IsCMField.complexConj K δ = -δ)
    (hδ0 : δ ≠ 0) :
    QuadraticAlgebra (NumberField.maximalRealSubfield K) (cmQuadraticParameter K δ hδ) 0 ≃ₐ[
      NumberField.maximalRealSubfield K] K :=
  AlgEquiv.ofBijective (cmQuadraticMap K δ hδ) (cm_quadratic_map_bijective K δ hδ hδ0)

theorem cm_quadratic_parameter_not_isSquare (δ : K)
    (hδ : NumberField.IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0) :
    ¬ IsSquare (cmQuadraticParameter K δ hδ) := by
  rintro ⟨r, hr⟩
  have hs : δ ^ 2 = (r : K) ^ 2 := by
    have h := congrArg (fun x : NumberField.maximalRealSubfield K => (x : K)) hr
    change δ ^ 2 = (r : K) * (r : K) at h
    simpa only [pow_two] using h
  have hc : NumberField.IsCMField.complexConj K δ = δ := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
    · rw [h]
      exact NumberField.IsCMField.complexConj_apply_eq_self K r
    · rw [h, map_neg, NumberField.IsCMField.complexConj_apply_eq_self]
  exact hδ0 (CharZero.neg_eq_self_iff.mp (hδ.symm.trans hc))

theorem cm_quadratic_equiv_generator (δ : K)
    (hδ : NumberField.IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0) :
    cmQuadraticEquiv K δ hδ hδ0 QuadraticAlgebra.omega = δ := by
  change cmQuadraticMap K δ hδ QuadraticAlgebra.omega = δ
  simp [cm_quadratic_map_apply]

theorem cm_quadratic_equiv_conjugation (δ : K)
    (hδ : NumberField.IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0) (x : K) :
    (cmQuadraticEquiv K δ hδ hδ0).symm (NumberField.IsCMField.complexConj K x) =
      star ((cmQuadraticEquiv K δ hδ hδ0).symm x) := by
  apply (cmQuadraticEquiv K δ hδ hδ0).injective
  rw [AlgEquiv.apply_symm_apply]
  change NumberField.IsCMField.complexConj K x = cmQuadraticMap K δ hδ _
  rw [cm_quadratic_map_star]
  congr 1
  exact ((cmQuadraticEquiv K δ hδ hδ0).apply_symm_apply x).symm

end

/-! ThetaCycle: identify the quadratic-model trace with the actual field trace. -/

open scoped Classical

theorem quadratic_algebra_trace {R : Type*} [CommRing R] (d : R)
    (x : QuadraticAlgebra R d 0) :
    Algebra.trace R (QuadraticAlgebra R d 0) x = QuadraticAlgebra.trace x := by
  have h0 : QuadraticAlgebra.basis d 0 (0 : Fin 2) = 1 := by
    ext <;> simp [QuadraticAlgebra.basis, Module.Basis.coe_ofEquivFun,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have h1 : QuadraticAlgebra.basis d 0 (1 : Fin 2) = QuadraticAlgebra.omega := by
    ext <;> simp [QuadraticAlgebra.basis, Module.Basis.coe_ofEquivFun, QuadraticAlgebra.omega]
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis d 0)]
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Algebra.leftMulMatrix_eq_repr_mul,
    h0, h1, mul_one, QuadraticAlgebra.basis_repr_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_omega,
    QuadraticAlgebra.im_omega, mul_zero, zero_mul, add_zero,
    QuadraticAlgebra.trace_def]
  ring

/-- The skew-Hermitian convention in AdelicSplitting includes a half-trace. The factor
`-2` compensates for it and for switching the conjugate-linear argument. -/
theorem quadratic_skew_trace_normalization {F : Type*} [Field F] [CharZero F]
    (d : F) (δ x : QuadraticAlgebra F d 0) (hδ : star δ = -δ) :
    QuadraticAlgebra.trace ((-2 * δ) * star x) / 2 = QuadraticAlgebra.trace (δ * x) := by
  rw [← QuadraticAlgebra.trace_star ((-2 * δ) * star x)]
  have h : star ((-2 * δ) * star x) = δ * x + δ * x := by
    simp only [star_mul, star_neg, star_ofNat, hδ, star_star]
    ring
  rw [h, map_add]
  field_simp
  ring

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]

theorem cm_quadratic_relative_trace (δ : K)
    (hδ : NumberField.IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)
    (x : QuadraticAlgebra (NumberField.maximalRealSubfield K) (cmQuadraticParameter K δ hδ) 0) :
    Algebra.trace (NumberField.maximalRealSubfield K) K (cmQuadraticEquiv K δ hδ hδ0 x) =
      QuadraticAlgebra.trace x := by
  rw [Algebra.trace_eq_of_algEquiv (cmQuadraticEquiv K δ hδ hδ0), quadratic_algebra_trace]

/-- Restriction of scalars preserves the original rational trace, with its
normalization determined by the degree-two multiplication matrix. -/
theorem cm_quadratic_rational_trace (δ : K)
    (hδ : NumberField.IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)
    (x : QuadraticAlgebra (NumberField.maximalRealSubfield K) (cmQuadraticParameter K δ hδ) 0) :
    Algebra.trace ℚ (NumberField.maximalRealSubfield K) (QuadraticAlgebra.trace x) =
      Algebra.trace ℚ K (cmQuadraticEquiv K δ hδ hδ0 x) := by
  rw [← cm_quadratic_relative_trace K δ hδ hδ0 x, Algebra.trace_trace]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.QuadraticModel.CM
