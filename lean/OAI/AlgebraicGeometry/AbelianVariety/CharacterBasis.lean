import OAI.AlgebraicGeometry.AbelianVariety.PureAverage
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Character Basis -/

namespace OAI.AlgebraicGeometry.AbelianVariety.CharacterBasis.Constructions.ExteriorCohomology

noncomputable section

open scoped BigOperators

/-- Differentiating a Hodge character along a unit curve reads its signed degree. -/
theorem bidegree_curve_hasDerivAt (p q : ℕ) :
    HasDerivAt (fun t : ℝ => ((1 : ℂ) + (t : ℂ) * Complex.I) ^ p *
      ((1 : ℂ) - (t : ℂ) * Complex.I) ^ q)
      (((p : ℂ) - (q : ℂ)) * Complex.I) 0 := by
  have hr : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have hplus : HasDerivAt (fun t : ℝ => (1 : ℂ) + (t : ℂ) * Complex.I) Complex.I 0 := by
    simpa using (hr.mul_const Complex.I).const_add 1
  have hminus : HasDerivAt (fun t : ℝ => (1 : ℂ) - (t : ℂ) * Complex.I) (-Complex.I) 0 := by
    simpa using (hr.mul_const Complex.I).const_sub 1
  apply HasDerivAt.congr_deriv ((hplus.pow p).mul (hminus.pow q))
  norm_num
  ring

/-- Equal Hodge characters have equal signed degrees. -/
theorem bidegreeCharacter_eq_imp_signed_eq (p q r s : ℕ)
    (h : ∀ z : ℂˣ, OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z = OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter r s z) :
    (p : ℤ) - q = (r : ℤ) - s := by
  have hz (t : ℝ) : (1 : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    simp at hre
  have he : (fun t : ℝ => ((1 : ℂ) + (t : ℂ) * Complex.I) ^ p *
      ((1 : ℂ) - (t : ℂ) * Complex.I) ^ q) =
      (fun t : ℝ => ((1 : ℂ) + (t : ℂ) * Complex.I) ^ r *
      ((1 : ℂ) - (t : ℂ) * Complex.I) ^ s) := by
    funext t
    have ht := h (Units.mk0 ((1 : ℂ) + (t : ℂ) * Complex.I) (hz t))
    simpa [OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, Complex.star_def, sub_eq_add_neg, mul_neg] using ht
  have hd := bidegree_curve_hasDerivAt p q
  rw [he] at hd
  have hder := hd.unique (bidegree_curve_hasDerivAt r s)
  have hc := mul_right_cancel₀ Complex.I_ne_zero hder
  exact_mod_cast hc

variable {V ι Z : Type*} [AddCommGroup V] [Module ℂ V] [Fintype ι]
  (b : Module.Basis ι ℂ V) (T : Z → V →ₗ[ℂ] V) (χ : ι → Z → ℂ)
  (hb : ∀ z i, T z (b i) = χ i z • b i)

include hb

theorem eigen_basis_coordinate (z : Z) (x : V) (i : ι) :
    b.repr (T z x) i = χ i z * b.repr x i := by
  classical
  have he := congrArg (fun y => b.repr (T z y) i) (b.sum_repr x)
  simp only [map_sum, map_smul, hb, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, Module.Basis.repr_self,
    Finsupp.single_apply, smul_eq_mul] at he
  simpa [mul_comm] using he.symm

/-- A simultaneous character condition is precisely the span of matching basis characters. -/
theorem eigen_basis_span_iff (chi0 : Z → ℂ) (x : V) :
    (∀ z, T z x = chi0 z • x) ↔ x ∈ Submodule.span ℂ (b '' {i | χ i = chi0}) := by
  classical
  constructor
  · intro hx
    apply b.mem_span_image.mpr
    intro i hi
    have hci : b.repr x i ≠ 0 := Finsupp.mem_support_iff.mp hi
    funext z
    have he := congrArg (fun y => b.repr y i) (hx z)
    rw [eigen_basis_coordinate b T χ hb, map_smul] at he
    change χ i z * b.repr x i = chi0 z * b.repr x i at he
    exact mul_right_cancel₀ hci he
  · intro hx z
    let S : Submodule ℂ V := LinearMap.ker (T z - chi0 z • LinearMap.id)
    have hs : Submodule.span ℂ (b '' {i | χ i = chi0}) ≤ S := by
      apply Submodule.span_le.mpr
      rintro y ⟨i, hi, rfl⟩
      change T z (b i) - chi0 z • b i = 0
      rw [hb, hi, sub_self]
    exact sub_eq_zero.mp (hs hx)

end

end OAI.AlgebraicGeometry.AbelianVariety.CharacterBasis.Constructions.ExteriorCohomology
