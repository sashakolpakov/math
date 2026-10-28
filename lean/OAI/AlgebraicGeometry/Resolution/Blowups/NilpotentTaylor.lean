import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Algebra.Equiv

/-! # Nilpotent Taylor -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.NilpotentTaylor.Construction

noncomputable section

/-! Finite Taylor automorphisms from nilpotent relative derivations. -/

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] [Algebra ℚ R]

theorem nilpotentDerivation_exp_fixed (D : Derivation k R R)
    (hD : IsNilpotent D.toLinearMap) (x : R) (hx : D x = 0) :
    IsNilpotent.exp D.toLinearMap x = x := by
  have h : (D.toLinearMap ^ 1) • x = 0 := by simpa using hx
  simpa using IsNilpotent.exp_smul_eq_sum h hD

/-- A nilpotent derivation has an actual algebra automorphism as its exponential. -/
def nilpotentDerivationExp (D : Derivation k R R) (hD : IsNilpotent D.toLinearMap) :
    R ≃ₐ[k] R where
  toFun x := IsNilpotent.exp D.toLinearMap x
  invFun x := IsNilpotent.exp (-D.toLinearMap) x
  left_inv x := by
    simp only [← LinearMap.comp_apply, ← Module.End.mul_eq_comp,
      hD.exp_neg_mul_exp_self, Module.End.one_apply]
  right_inv x := by
    simp only [← LinearMap.comp_apply, ← Module.End.mul_eq_comp,
      hD.exp_mul_exp_neg_self, Module.End.one_apply]
  map_add' := (IsNilpotent.exp D.toLinearMap).map_add
  map_mul' := Module.End.exp_mul_of_derivation k R D.toLinearMap
    (fun x y => by
      change D (x * y) = x * D y + D x * y
      simpa only [smul_eq_mul, mul_comm y (D x)] using D.leibniz x y) hD
  commutes' a := nilpotentDerivation_exp_fixed D hD _ (D.map_algebraMap a)

omit [Algebra ℚ R] in
/-- Multiplying a derivation by an element it fixes gives the expected powers. -/
theorem invariant_smul_derivation_pow (D : Derivation k R R) (t : R)
    (ht : D t = 0) (n : ℕ) (x : R) :
    ((t • D).toLinearMap ^ n) x = t ^ n * (D.toLinearMap ^ n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    change t * D (t ^ n * (D.toLinearMap ^ n) x) = _
    rw [D.leibniz, D.leibniz_pow, ht]
    simp only [smul_zero, mul_zero, add_zero, smul_eq_mul]
    rw [pow_succ', mul_assoc]
    rw [pow_succ' D.toLinearMap n, Module.End.mul_apply]
    rfl

omit [Algebra ℚ R] in
theorem invariant_smul_derivation_nilpotent (D : Derivation k R R) (t : R)
    (ht : D t = 0) (n : ℕ) (hn : t ^ n = 0) :
    (t • D).toLinearMap ^ n = 0 := by
  ext x
  rw [invariant_smul_derivation_pow D t ht n x, hn, zero_mul]
  rfl

/-- Finite Taylor substitution when the displacement is nilpotent and constant
for the derivation. -/
def invariantNilpotentTaylor (D : Derivation k R R) (t : R)
    (ht : D t = 0) (n : ℕ) (hn : t ^ n = 0) : R ≃ₐ[k] R :=
  nilpotentDerivationExp (t • D)
    ⟨n, invariant_smul_derivation_nilpotent D t ht n hn⟩

theorem invariantNilpotentTaylor_apply (D : Derivation k R R) (t : R)
    (ht : D t = 0) (n : ℕ) (hn : t ^ n = 0) (x : R) :
    invariantNilpotentTaylor D t ht n hn x =
      ∑ j ∈ Finset.range n, (j.factorial : ℚ)⁻¹ •
        (t ^ j * (D.toLinearMap ^ j) x) := by
  change IsNilpotent.exp (t • D).toLinearMap x = _
  rw [IsNilpotent.exp_eq_sum (invariant_smul_derivation_nilpotent D t ht n hn)]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply,
    invariant_smul_derivation_pow D t ht]

/-- For a section killed by an earlier derivative, the Taylor sum stops there. -/
theorem invariantNilpotentTaylor_apply_short (D : Derivation k R R) (t : R)
    (ht : D t = 0) (n : ℕ) (hn : t ^ n = 0) (m : ℕ) (x : R)
    (hx : (D.toLinearMap ^ m) x = 0) :
    invariantNilpotentTaylor D t ht n hn x =
      ∑ j ∈ Finset.range m, (j.factorial : ℚ)⁻¹ •
        (t ^ j * (D.toLinearMap ^ j) x) := by
  have h : ((t • D).toLinearMap ^ m) • x = 0 := by
    change ((t • D).toLinearMap ^ m) x = 0
    rw [invariant_smul_derivation_pow D t ht m x, hx, mul_zero]
  have he := IsNilpotent.exp_smul_eq_sum h
    (show IsNilpotent (t • D).toLinearMap from
      ⟨n, invariant_smul_derivation_nilpotent D t ht n hn⟩)
  change IsNilpotent.exp (t • D).toLinearMap x = _
  simpa only [Module.End.smul_def, invariant_smul_derivation_pow D t ht] using he

end

end OAI.AlgebraicGeometry.Resolution.Blowups.NilpotentTaylor.Construction
