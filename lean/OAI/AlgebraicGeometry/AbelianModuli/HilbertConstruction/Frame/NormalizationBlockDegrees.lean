import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.ChartDenominators
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.DeterminantAlgebra
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.ExponentCompletion

/-! # Normalization Block Degrees -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.NormalizationBlockDegrees

noncomputable section

/-! Exact block degrees of the frame discriminant and cleared point
coordinates identify the invariant fraction inverse to a normalized denominator. -/
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {r m : ℕ}

theorem frameReplacementWeight_sum (σ : Fin r → Fin m) (e i : Fin m) :
    (∑ k, DeterminantBlockDegrees.labeledDeterminantWeight (Function.update σ k e) i) + DeterminantBlockDegrees.labeledDeterminantWeight σ i =
      r * (DeterminantBlockDegrees.labeledDeterminantWeight σ i + if e = i then 1 else 0) := by
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin r))) rfl
    (fun k _ => CoordinateExponents.labeledDeterminantWeight_update_add σ k e i)
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] at h
  change (∑ k, DeterminantBlockDegrees.labeledDeterminantWeight (Function.update σ k e) i) + DeterminantBlockDegrees.labeledDeterminantWeight σ i =
    r * DeterminantBlockDegrees.labeledDeterminantWeight σ i + r * (if e = i then 1 else 0) at h
  simpa only [Nat.mul_add] using h

theorem frameDiscriminantExponent_degree (σ : Fin r → Fin m) (e i : Fin m) :
    Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight (ChartDenominators.frameDiscriminantExponent σ e) i =
      r * (DeterminantBlockDegrees.labeledDeterminantWeight σ i + if e = i then 1 else 0) := by
  have hsingle (j : Fin r → Fin m) : Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight (Pi.single j 1) i =
      DeterminantBlockDegrees.labeledDeterminantWeight j i := by simp [Balanced.ExponentFiniteGeneration.monomialMultiDegree, Pi.single_apply]
  simp only [ChartDenominators.frameDiscriminantExponent, Balanced.ExponentFiniteGeneration.monomialMultiDegree_add, MonomialFiniteSums.monomialMultiDegree_sum, hsingle]
  exact (Nat.add_comm _ _).trans (frameReplacementWeight_sum σ e i)

theorem frameCoordinateExponent_degree_explicit (hr : 0 < r)
    (σ : Fin r → Fin m) (e z : Fin m) (k : Fin r) (i : Fin m) :
    Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight (CoordinateExponents.frameCoordinateExponent σ e z k) i =
      (r - 1) * (DeterminantBlockDegrees.labeledDeterminantWeight σ i + if e = i then 1 else 0) +
        if z = i then 1 else 0 := by
  rw [CoordinateExponents.frameCoordinateExponent_degree]
  have hsum := frameReplacementWeight_sum σ e i
  have he := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin r)))
    (fun j => DeterminantBlockDegrees.labeledDeterminantWeight (Function.update σ j e) i) (Finset.mem_univ k)
  have hz := CoordinateExponents.labeledDeterminantWeight_update_add σ k z i
  have hv := CoordinateExponents.labeledDeterminantWeight_update_add σ k e i
  have hsplit : r * (DeterminantBlockDegrees.labeledDeterminantWeight σ i + if e = i then 1 else 0) =
      (r - 1) * (DeterminantBlockDegrees.labeledDeterminantWeight σ i + if e = i then 1 else 0) +
        (DeterminantBlockDegrees.labeledDeterminantWeight σ i + if e = i then 1 else 0) := by
    have heq := congrArg
      (fun t : ℕ => t * (DeterminantBlockDegrees.labeledDeterminantWeight σ i + if e = i then 1 else 0))
      (Nat.sub_add_cancel (Nat.succ_le_of_lt hr))
    simpa only [Nat.add_mul, Nat.one_mul] using heq.symm
  omega

def allFrameCoordinateExponent (σ : Fin r → Fin m) (e : Fin m) (c : Fin m → Fin r) :
    (Fin r → Fin m) → ℕ := ∑ z, CoordinateExponents.frameCoordinateExponent σ e z (c z)

theorem allFrameCoordinateExponent_degree (hr : 0 < r) (σ : Fin r → Fin m)
    (e i : Fin m) (c : Fin m → Fin r) :
    Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight (allFrameCoordinateExponent σ e c) i =
      m * ((r - 1) * (DeterminantBlockDegrees.labeledDeterminantWeight σ i + if e = i then 1 else 0)) + 1 := by
  simp only [allFrameCoordinateExponent, MonomialFiniteSums.monomialMultiDegree_sum,
    frameCoordinateExponent_degree_explicit hr, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp

theorem normalizedDenominatorInverse_equal_degrees (hr : 0 < r)
    (σ : Fin r → Fin m) (e : Fin m) (c : Fin m → Fin r)
    (a : (Fin r → Fin m) → ℕ) (ha : a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight) (i₀ : Fin m) :
    ∀ i, Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight
        ((Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i₀) • allFrameCoordinateExponent σ e c) i =
      Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight
        (((r - 1) * ∑ τ, a τ) • ChartDenominators.frameDiscriminantExponent σ e + a) i := by
  intro i
  have hmass := Balanced.DeterminantAlgebra.balancedDeterminantMonomial_degree_mass a ha i₀
  have hbal := (Balanced.ExponentFiniteGeneration.mem_balancedExponentMonoid_iff _ _).mp ha i i₀
  rw [Balanced.ExponentCompletion.monomialMultiDegree_nsmul, Balanced.ExponentFiniteGeneration.monomialMultiDegree_add, Balanced.ExponentCompletion.monomialMultiDegree_nsmul,
    allFrameCoordinateExponent_degree hr, frameDiscriminantExponent_degree, hbal]
  calc
    _ = (m * Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i₀) *
        ((r - 1) * (DeterminantBlockDegrees.labeledDeterminantWeight σ i + if e = i then 1 else 0)) +
          Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a i₀ := by ring
    _ = _ := by rw [← hmass]; ring

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.NormalizationBlockDegrees
