import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SiegelOscillatorGraph

/-! # Jacobi Block Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.JacobiBlockAction.CM

noncomputable section

/-! ThetaCycle: the actual position/momentum action induces the classical
inverse-transpose Jacobi change and its quadratic correction. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
    (g : ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks I R) (Z : Matrix I I R)

theorem jacobi_fractional_left_identity (hZ : Z.IsSymm) (hJ : IsUnit (g.denominator Z).det) :
    (g.denominator Z)ᵀ * g.fractional Z = (g.numerator Z)ᵀ := by
  have h := congrArg Matrix.transpose (g.fractional_mul_denominator Z hJ)
  simpa only [Matrix.transpose_mul, (g.fractional_symmetric Z hZ hJ).eq] using h

theorem jacobi_linear_factor (hZ : Z.IsSymm) (hJ : IsUnit (g.denominator Z).det) :
    g.A - g.fractional Z * g.C = (g.denominator Z)⁻¹ᵀ := by
  have hid : (g.denominator Z)ᵀ * (g.A - g.fractional Z * g.C) = 1 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, jacobi_fractional_left_identity g Z hZ hJ]
    calc
      (g.denominator Z)ᵀ * g.A - (g.numerator Z)ᵀ * g.C =
          Z * (g.Cᵀ * g.A - g.Aᵀ * g.C) + (g.Dᵀ * g.A - g.Bᵀ * g.C) := by
        simp only [ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.denominator, ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.numerator,
          Matrix.transpose_add, Matrix.transpose_mul, hZ.eq]
        noncomm_ring
      _ = 1 := by rw [g.ac, sub_self, mul_zero, zero_add, g.da_bc]
  simpa only [Matrix.transpose_nonsing_inv] using (Matrix.inv_eq_right_inv hid).symm

theorem jacobi_constant_factor (hJ : IsUnit (g.denominator Z).det) :
    g.B - g.fractional Z * g.D = -(g.A - g.fractional Z * g.C) * Z := by
  have hb : g.B = g.fractional Z * g.denominator Z - g.A * Z := by
    apply (eq_sub_iff_add_eq).mpr
    rw [g.fractional_mul_denominator Z hJ, ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.numerator, add_comm]
  rw [hb]
  unfold ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.denominator
  noncomm_ring

theorem jacobi_phase_action (hZ : Z.IsSymm) (hJ : IsUnit (g.denominator Z).det) (q p : I → R) :
    (g.B *ᵥ q + g.A *ᵥ p) - g.fractional Z *ᵥ (g.D *ᵥ q + g.C *ᵥ p) =
      (g.denominator Z)⁻¹ᵀ *ᵥ (p - Z *ᵥ q) := by
  calc
    _ = (g.B - g.fractional Z * g.D) *ᵥ q +
        (g.A - g.fractional Z * g.C) *ᵥ p := by
      simp only [Matrix.sub_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec]
      abel
    _ = (g.A - g.fractional Z * g.C) *ᵥ (p - Z *ᵥ q) := by
      rw [jacobi_constant_factor g Z hJ, Matrix.neg_mul, Matrix.neg_mulVec,
        Matrix.mulVec_sub, Matrix.mulVec_mulVec]
      abel
    _ = _ := by rw [jacobi_linear_factor g Z hZ hJ]

theorem jacobi_position_action (q p : I → R) :
    g.D *ᵥ q + g.C *ᵥ p = g.C *ᵥ (p - Z *ᵥ q) + g.denominator Z *ᵥ q := by
  simp only [ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.denominator, Matrix.mulVec_sub, Matrix.add_mulVec,
    Matrix.mulVec_mulVec]
  abel

theorem jacobi_pairing_correction (hJ : IsUnit (g.denominator Z).det) (q p : I → R) :
    q ⬝ᵥ (p - Z *ᵥ q) -
        (g.D *ᵥ q + g.C *ᵥ p) ⬝ᵥ ((g.denominator Z)⁻¹ᵀ *ᵥ (p - Z *ᵥ q)) =
      -((p - Z *ᵥ q) ⬝ᵥ (((g.denominator Z)⁻¹ * g.C) *ᵥ (p - Z *ᵥ q))) := by
  rw [jacobi_position_action, add_dotProduct]
  have hj : (g.denominator Z *ᵥ q) ⬝ᵥ ((g.denominator Z)⁻¹ᵀ *ᵥ (p - Z *ᵥ q)) =
      q ⬝ᵥ (p - Z *ᵥ q) := by
    rw [Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hJ, Matrix.one_mulVec, dotProduct_comm]
  have hc : (g.C *ᵥ (p - Z *ᵥ q)) ⬝ᵥ ((g.denominator Z)⁻¹ᵀ *ᵥ (p - Z *ᵥ q)) =
      (p - Z *ᵥ q) ⬝ᵥ (((g.denominator Z)⁻¹ * g.C) *ᵥ (p - Z *ᵥ q)) := by
    rw [Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec]
  rw [hj, hc]
  abel

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.JacobiBlockAction.CM
