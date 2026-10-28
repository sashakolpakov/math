import OAI.AlgebraicGeometry.Resolution.Blowups.NilpotentTaylor
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.Regularity
import Mathlib.RingTheory.Derivation.MapCoeffs

/-! # Truncated Taylor -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.TruncatedTaylor.Construction

noncomputable section

/-! Taylor substitution in the universal truncated polynomial algebra. -/

open _root_.Polynomial

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]

/-- Extend a relative derivation coefficientwise, keeping the new variable fixed. -/
def polynomialCoefficientDerivation (D : Derivation k R R) :
    Derivation k R[X] R[X] :=
  PolynomialModule.equivPolynomialSelf.compDer D.mapCoeffs

@[simp] theorem polynomialCoefficientDerivation_X (D : Derivation k R R) :
    polynomialCoefficientDerivation D (X : R[X]) = 0 := by
  simp [polynomialCoefficientDerivation]

@[simp] theorem polynomialCoefficientDerivation_C (D : Derivation k R R) (x : R) :
    polynomialCoefficientDerivation D (C x) = C (D x) := by
  simp [polynomialCoefficientDerivation]

/-- The universal ring with a nilpotent Taylor parameter of exponent `n`. -/
abbrev TruncatedTaylorAlgebra (R : Type*) [CommRing R] (n : ℕ) :=
  R[X] ⧸ Ideal.span {(X : R[X]) ^ n}

def truncatedTaylorParameter (n : ℕ) : TruncatedTaylorAlgebra R n :=
  Ideal.Quotient.mk _ X

def truncatedTaylorConstants (n : ℕ) : R →ₐ[k] TruncatedTaylorAlgebra R n :=
  IsScalarTower.toAlgHom k R (TruncatedTaylorAlgebra R n)

theorem truncatedTaylorParameter_pow (n : ℕ) :
    (truncatedTaylorParameter (R := R) n) ^ n = 0 := by
  unfold truncatedTaylorParameter
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

theorem polynomialCoefficientDerivation_preserves_truncation
    (D : Derivation k R R) (n : ℕ) (p : R[X])
    (hp : p ∈ Ideal.span {(X : R[X]) ^ n}) :
    polynomialCoefficientDerivation D p ∈ Ideal.span {(X : R[X]) ^ n} := by
  have hpow : polynomialCoefficientDerivation D ((X : R[X]) ^ n) = 0 := by
    rw [(polynomialCoefficientDerivation D).leibniz_pow,
      polynomialCoefficientDerivation_X]
    simp only [smul_zero]
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hp
  rw [(polynomialCoefficientDerivation D).leibniz, hpow]
  change X ^ n * polynomialCoefficientDerivation D q + q * 0 ∈ _
  rw [mul_zero, add_zero]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ((X : R[X]) ^ n))

def truncatedCoefficientDerivation (D : Derivation k R R) (n : ℕ) :
    Derivation k (TruncatedTaylorAlgebra R n) (TruncatedTaylorAlgebra R n) :=
  Coordinate.Regularity.Construction.quotientDerivation (polynomialCoefficientDerivation D) _
    (polynomialCoefficientDerivation_preserves_truncation D n)

theorem truncatedCoefficientDerivation_parameter (D : Derivation k R R) (n : ℕ) :
    truncatedCoefficientDerivation D n (truncatedTaylorParameter n) = 0 := by
  change Ideal.Quotient.mk _ (polynomialCoefficientDerivation D X) = 0
  rw [polynomialCoefficientDerivation_X, map_zero]

theorem truncatedCoefficientDerivation_constants (D : Derivation k R R) (n : ℕ)
    (x : R) :
    truncatedCoefficientDerivation D n (truncatedTaylorConstants (k := k) n x) =
      truncatedTaylorConstants (k := k) n (D x) := by
  change Ideal.Quotient.mk _ (polynomialCoefficientDerivation D (C x)) = _
  rw [polynomialCoefficientDerivation_C]
  rfl

theorem truncatedCoefficientDerivation_pow_constants (D : Derivation k R R)
    (n j : ℕ) (x : R) :
    ((truncatedCoefficientDerivation D n).toLinearMap ^ j)
      (truncatedTaylorConstants (k := k) n x) =
        truncatedTaylorConstants (k := k) n ((D.toLinearMap ^ j) x) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ' D.toLinearMap j,
      Module.End.mul_apply]
    exact truncatedCoefficientDerivation_constants D n _

variable [Algebra ℚ R]

/-- Universal finite Taylor substitution, constructed as a genuine algebra map. -/
def truncatedTaylor (D : Derivation k R R) (n : ℕ) :
    R →ₐ[k] TruncatedTaylorAlgebra R n :=
  (NilpotentTaylor.Construction.invariantNilpotentTaylor (truncatedCoefficientDerivation D n)
    (truncatedTaylorParameter n) (truncatedCoefficientDerivation_parameter D n)
    n (truncatedTaylorParameter_pow n)).toAlgHom.comp (truncatedTaylorConstants n)

theorem truncatedTaylor_apply (D : Derivation k R R) (n : ℕ) (x : R) :
    truncatedTaylor D n x =
      ∑ j ∈ Finset.range n, (j.factorial : ℚ)⁻¹ •
        ((truncatedTaylorParameter n) ^ j *
          truncatedTaylorConstants (k := k) n ((D.toLinearMap ^ j) x)) := by
  unfold truncatedTaylor
  rw [AlgHom.comp_apply]
  change NilpotentTaylor.Construction.invariantNilpotentTaylor _ _ _ _ _ _ = _
  rw [NilpotentTaylor.Construction.invariantNilpotentTaylor_apply]
  simp only [truncatedCoefficientDerivation_pow_constants]

theorem truncatedTaylor_apply_short (D : Derivation k R R) (n m : ℕ) (x : R)
    (hx : (D.toLinearMap ^ m) x = 0) :
    truncatedTaylor D n x =
      ∑ j ∈ Finset.range m, (j.factorial : ℚ)⁻¹ •
        ((truncatedTaylorParameter n) ^ j *
          truncatedTaylorConstants (k := k) n ((D.toLinearMap ^ j) x)) := by
  unfold truncatedTaylor
  rw [AlgHom.comp_apply]
  change NilpotentTaylor.Construction.invariantNilpotentTaylor _ _ _ _ _ _ = _
  rw [NilpotentTaylor.Construction.invariantNilpotentTaylor_apply_short (m := m)]
  · simp only [truncatedCoefficientDerivation_pow_constants]
  · rw [truncatedCoefficientDerivation_pow_constants, hx, map_zero]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.TruncatedTaylor.Construction
