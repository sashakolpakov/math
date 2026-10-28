import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DeterminantFrameNormalizationValues

/-! # Frame Coordinate Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.FrameCoordinateValues

noncomputable section

/-! The affine ratios of the determinant normalizer send a projective
frame to the coordinate axes and the all-one point over arbitrary rings. -/
open scoped BigOperators Classical
universe u v w
variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
variable {κ : Type w} [Fintype κ]

theorem normalizedDeterminantFrame_additional
    (e : Module.Basis κ R V) (b : κ → V) (v : V)
    (hframe : IsUnit (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant e b v))
    (c : κ) (x : κ → R)
    (hx : ∀ k, x k * DeterminantFrameLinearMap.determinantFrameLinearMap e b v v c = DeterminantFrameLinearMap.determinantFrameLinearMap e b v v k) :
    x = fun _ => 1 := by
  obtain ⟨u, hu⟩ := (DeterminantFrameNormalizationValues.determinantFrameLinearMap_normalizes e b v hframe).1
  funext k
  apply u.isUnit.mul_right_cancel
  have h := hx k
  rw [hu] at h
  exact h.trans (one_mul _).symm

theorem normalizedDeterminantFrame_basis
    (e : Module.Basis κ R V) (b : κ → V) (v : V)
    (hframe : IsUnit (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant e b v))
    (j c : κ) (x : κ → R)
    (hx : ∀ k, x k * DeterminantFrameLinearMap.determinantFrameLinearMap e b v (b j) c = DeterminantFrameLinearMap.determinantFrameLinearMap e b v (b j) k) :
    x = fun k => if j = k then 1 else 0 := by
  obtain ⟨u, hu⟩ := (DeterminantFrameNormalizationValues.determinantFrameLinearMap_normalizes e b v hframe).2 j
  by_cases hjc : j = c
  · subst c
    funext k
    apply u.isUnit.mul_right_cancel
    have h := hx k
    rw [hu, hu, ite_eq_left rfl] at h
    by_cases hjk : j = k
    · simpa only [hjk, ite_true, one_mul] using h
    · simpa only [hjk, ite_false, zero_mul] using h
  · have hj := hx j
    rw [hu, hu, ite_eq_right hjc, ite_eq_left rfl, mul_zero] at hj
    have hzero : IsUnit (0 : R) := hj.symm ▸ u.isUnit
    have h01 : (0 : R) = 1 := isUnit_zero_iff.mp hzero
    have hall (a : R) : a = 0 := by
      calc
        a = a * 1 := (mul_one a).symm
        _ = a * 0 := congrArg (a * ·) h01.symm
        _ = 0 := mul_zero a
    funext k
    exact (hall _).trans (hall _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.FrameCoordinateValues
