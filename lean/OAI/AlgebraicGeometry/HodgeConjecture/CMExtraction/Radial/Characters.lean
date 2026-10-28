import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Hecke
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Algebra

/-! # Characters -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Characters

noncomputable section

section

/-! Dilation eigenfunctionals are constructed on the actual radial basis.
Their uniqueness will identify the Hecke character of a radial quotient. -/

open scoped Classical
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable (q : ℕ) [Fact q.Prime]

def dilationFunctional (e : ℂ) : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] ℂ :=
  (Hecke.radialBasis q).constr ℂ (fun n : ℤ => (e / Cyclicity.normalization q) ^ n)

theorem dilationFunctional_ball (e : ℂ) (n : ℤ) :
    dilationFunctional q e (Cyclicity.ball q n) = (e / Cyclicity.normalization q) ^ n := by
  rw [← Hecke.radialBasis_apply]
  exact Module.Basis.constr_basis _ _ _ _

theorem dilationFunctional_unit_ball (e : ℂ) : dilationFunctional q e (Cyclicity.ball q 0) = 1 := by
  rw [dilationFunctional_ball, zpow_zero]

theorem dilationFunctional_ne_zero (e : ℂ) : dilationFunctional q e ≠ 0 := by
  intro h
  have hz := LinearMap.congr_fun h (Cyclicity.ball q 0)
  rw [dilationFunctional_unit_ball] at hz
  exact one_ne_zero hz

theorem dilationFunctional_dilation (e : ℂ) (he : e ≠ 0) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    dilationFunctional q e (Cyclicity.dilationEquiv q b) = e * dilationFunctional q e b := by
  have h : (dilationFunctional q e).comp (Cyclicity.dilationEquiv q).toLinearMap =
      e • dilationFunctional q e := by
    apply (Hecke.radialBasis q).ext
    intro n
    change dilationFunctional q e (Cyclicity.dilationEquiv q (Hecke.radialBasis q n)) =
      e * dilationFunctional q e (Hecke.radialBasis q n)
    rw [Hecke.radialBasis_apply, Cyclicity.dilationEquiv_ball, map_smul, dilationFunctional_ball,
      dilationFunctional_ball, smul_eq_mul,
      zpow_add_one₀ (div_ne_zero he (Cyclicity.normalization_ne_zero q))]
    field_simp [Cyclicity.normalization_ne_zero q]
  exact LinearMap.congr_fun h b

theorem dilation_eigenfunctional_ext (e : ℂ) (he : e ≠ 0)
    (f g : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q →ₗ[ℂ] ℂ)
    (hf : ∀ b, f (Cyclicity.dilationEquiv q b) = e * f b)
    (hg : ∀ b, g (Cyclicity.dilationEquiv q b) = e * g b)
    (h0 : f (Cyclicity.ball q 0) = g (Cyclicity.ball q 0)) : f = g := by
  have hs (n : ℤ) (h : f (Cyclicity.ball q n) = g (Cyclicity.ball q n)) :
      f (Cyclicity.ball q (n + 1)) = g (Cyclicity.ball q (n + 1)) := by
    have h' : f (Cyclicity.dilationEquiv q (Cyclicity.ball q n)) = g (Cyclicity.dilationEquiv q (Cyclicity.ball q n)) := by rw [hf, hg, h]
    rw [Cyclicity.dilationEquiv_ball, map_smul, map_smul] at h'
    exact mul_left_cancel₀ (Cyclicity.normalization_ne_zero q) h'
  have hp (n : ℤ) (h : f (Cyclicity.ball q n) = g (Cyclicity.ball q n)) :
      f (Cyclicity.ball q (n - 1)) = g (Cyclicity.ball q (n - 1)) := by
    have h' : f (Cyclicity.dilationEquiv q (Cyclicity.ball q (n - 1))) = g (Cyclicity.dilationEquiv q (Cyclicity.ball q (n - 1))) := by
      rw [Cyclicity.dilationEquiv_ball, sub_add_cancel, map_smul, map_smul, h]
    rw [hf, hg] at h'
    exact mul_left_cancel₀ he h'
  apply (Hecke.radialBasis q).ext
  intro n
  rw [Hecke.radialBasis_apply]
  induction n using Int.induction_on with
  | zero => exact h0
  | succ n ih => exact hs n ih
  | pred n ih => exact hp (-(n : ℤ)) ih

end

/-! The actual radial action supplies a spherical character for each
nonzero dilation parameter. Its eigenfunctional is explicitly constructed. -/

open scoped Classical TensorProduct
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

variable (q : ℕ) [Fact q.Prime]
  (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (e : ℂ)

def radialEigenvalue (T : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) : ℂ :=
  dilationFunctional q e (Algebra.sphericalRadialComplexAlgebra q hElementaryDivisors T (Cyclicity.ball q 0))

theorem dilationFunctional_hecke (he : e ≠ 0)
    (T : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) (b : RepresentationTheory.Hecke.RadialDilation.Cm.radialInput q) :
    dilationFunctional q e (Algebra.sphericalRadialComplexAlgebra q hElementaryDivisors T b) =
      radialEigenvalue q hElementaryDivisors e T * dilationFunctional q e b := by
  have h : (dilationFunctional q e).comp (Algebra.sphericalRadialComplexAlgebra q hElementaryDivisors T) =
      radialEigenvalue q hElementaryDivisors e T • dilationFunctional q e := by
    apply dilation_eigenfunctional_ext q e he
    · intro b
      change dilationFunctional q e
        (Algebra.sphericalRadialComplexAlgebra q hElementaryDivisors T (Cyclicity.dilationEquiv q b)) = _
      rw [Algebra.sphericalRadialComplexAlgebra_dilation, dilationFunctional_dilation q e he]
      rfl
    · intro b
      change radialEigenvalue q hElementaryDivisors e T * dilationFunctional q e (Cyclicity.dilationEquiv q b) = _
      rw [dilationFunctional_dilation q e he]
      change _ = e * (radialEigenvalue q hElementaryDivisors e T * dilationFunctional q e b)
      ring
    · change radialEigenvalue q hElementaryDivisors e T =
        radialEigenvalue q hElementaryDivisors e T * dilationFunctional q e (Cyclicity.ball q 0)
      rw [dilationFunctional_unit_ball, mul_one]
  exact LinearMap.congr_fun h b

def radialCharacter (he : e ≠ 0) : (ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) →ₐ[ℂ] ℂ where
  toFun := radialEigenvalue q hElementaryDivisors e
  map_zero' := by simp [radialEigenvalue]
  map_one' := by simp [radialEigenvalue, dilationFunctional_unit_ball]
  map_add' T U := by simp [radialEigenvalue]
  map_mul' T U := by
    change dilationFunctional q e
      (Algebra.sphericalRadialComplexAlgebra q hElementaryDivisors (T * U) (Cyclicity.ball q 0)) = _
    rw [map_mul, Module.End.mul_apply, dilationFunctional_hecke q hElementaryDivisors e he]
    rfl
  commutes' c := by
    change dilationFunctional q e
      (Algebra.sphericalRadialComplexAlgebra q hElementaryDivisors ((algebraMap ℂ _) c) (Cyclicity.ball q 0)) = _
    rw [AlgHom.commutes]
    change dilationFunctional q e (c • Cyclicity.ball q 0) = c
    rw [map_smul, dilationFunctional_unit_ball, smul_eq_mul, mul_one]

theorem radialCharacter_quotient (he : e ≠ 0) :
    dilationFunctional q e ≠ 0 ∧
      (∀ b, dilationFunctional q e (Cyclicity.dilationEquiv q b) = e * dilationFunctional q e b) ∧
      (∀ T b, dilationFunctional q e (Algebra.sphericalRadialComplexAlgebra q hElementaryDivisors T b) =
        radialCharacter q hElementaryDivisors e he T * dilationFunctional q e b) :=
  ⟨dilationFunctional_ne_zero q e, dilationFunctional_dilation q e he,
    dilationFunctional_hecke q hElementaryDivisors e he⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Characters
