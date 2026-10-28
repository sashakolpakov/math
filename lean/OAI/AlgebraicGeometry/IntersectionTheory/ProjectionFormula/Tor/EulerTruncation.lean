import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Euler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BoundedResolution

/-! # Euler Truncation -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.EulerTruncation

noncomputable section

/-! Increasing the native Tor Euler truncation above a proved
projective-dimension bound does not change its value. -/

open _root_.CategoryTheory

universe u

theorem stable (R : Type u) [CommRing R] (M N : ModuleCat.{u} R)
    (d e : ℕ) [HasProjectiveDimensionLE N d] (hde : d ≤ e) :
    Euler.euler R M N e = Euler.euler R M N d := by
  unfold Euler.euler
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro i _ hi
  have hd : d < i := by
    simp only [Finset.mem_range, not_lt] at hi
    omega
  rw [ExactLength.rationalLength, BoundedResolution.tor_length_zero R M N d i hd,
    ENat.toNat_zero, Nat.cast_zero, mul_zero]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.EulerTruncation
