import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Group.Hom.End

/-! # Endomorphism Orbit Difference -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.EndomorphismOrbitDifference

/-! Forward differences of an additive endomorphism orbit are powers of its difference from identity. -/

theorem endomorphism_orbit_fwdDiff {G : Type*} [AddCommGroup G] (T : AddMonoid.End G)
    (φ : G →+ ℤ) (x : G) (r n : ℕ) :
    (fwdDiff 1)^[r] (fun k : ℕ => φ ((T ^ k) x)) n = φ ((T ^ n) (((T - 1) ^ r) x)) := by
  induction r generalizing n with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    change (fwdDiff 1)^[r] (fun k : ℕ => φ ((T ^ k) x)) (n + 1) -
      (fwdDiff 1)^[r] (fun k : ℕ => φ ((T ^ k) x)) n = _
    rw [ih, ih, pow_succ T n, pow_succ' (T - 1) r]
    change φ ((T ^ n) (T (((T - 1) ^ r) x))) - φ ((T ^ n) (((T - 1) ^ r) x)) =
      φ ((T ^ n) (T (((T - 1) ^ r) x) - ((T - 1) ^ r) x))
    rw [map_sub, map_sub]

theorem endomorphism_orbit_fwdDiff_eq_zero {G : Type*} [AddCommGroup G] (T : AddMonoid.End G)
    (φ : G →+ ℤ) (x : G) (r : ℕ) (hr : (T - 1) ^ r = 0) :
    (fwdDiff 1)^[r] (fun k : ℕ => φ ((T ^ k) x)) = 0 := by
  funext n
  rw [endomorphism_orbit_fwdDiff, hr]
  simp

end OAI.AlgebraicGeometry.SheafCohomology.Projective.EndomorphismOrbitDifference
