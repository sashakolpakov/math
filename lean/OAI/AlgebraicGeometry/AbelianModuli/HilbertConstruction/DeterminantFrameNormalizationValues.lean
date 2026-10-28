import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DeterminantFrameLinearMap

/-! # Determinant Frame Normalization Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DeterminantFrameNormalizationValues

noncomputable section

/-! The determinant normalizer sends the additional frame vector to a
unit multiple of the all-one vector, and each selected basis vector to
a unit multiple of its coordinate axis. -/
open scoped BigOperators Classical
universe u v w
variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
variable {κ : Type w} [Fintype κ]

theorem determinantFrameLinearMap_normalizes
    (e : Module.Basis κ R V) (b : κ → V) (v : V)
    (h : IsUnit (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant e b v)) :
    (∃ u : Rˣ, DeterminantFrameLinearMap.determinantFrameLinearMap e b v v = fun _ => (u : R)) ∧
      ∀ i : κ, ∃ u : Rˣ, ∀ k : κ,
        DeterminantFrameLinearMap.determinantFrameLinearMap e b v (b i) k = if i = k then (u : R) else 0 := by
  obtain ⟨c, hc, hu⟩ := (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant_isUnit_iff e b v).mp h
  have hbc : b = c := funext (fun i => (hc i).symm)
  subst b
  let a := (e.det c) ^ Fintype.card κ * ∏ i, c.repr v i
  have ha : IsUnit a := ((e.isUnit_det c).pow _).mul
    (ProjectiveFrame.HomogeneousCoordinates.projectiveFrameHomogeneousCoordinates_unit_factor c v hu)
  have he (w : V) : DeterminantFrameLinearMap.determinantFrameLinearMap e c v w =
      a • ProjectiveFrame.Normalization.projectiveFrameNormalization c v hu w := by
    rw [DeterminantFrameLinearMap.determinantFrameLinearMap_apply, ProjectiveFrame.DeterminantCoordinates.projectiveFrameDeterminantCoordinates_eq,
      ProjectiveFrame.HomogeneousCoordinates.projectiveFrameHomogeneousCoordinates_eq c v hu, smul_smul]
  constructor
  · refine ⟨ha.unit, ?_⟩
    rw [he, ProjectiveFrame.Normalization.projectiveFrameNormalization_additional]
    funext k
    change a * 1 = (ha.unit : R)
    rw [mul_one, ha.unit_spec]
  · intro i
    refine ⟨ha.unit * (hu i).unit⁻¹, fun k => ?_⟩
    rw [he]
    change a * ProjectiveFrame.Normalization.projectiveFrameNormalization c v hu (c i) k = _
    rw [ProjectiveFrame.Normalization.projectiveFrameNormalization_basis]
    by_cases hik : i = k
    · subst k
      simp only [ite_true, Units.val_mul, ha.unit_spec]
    · simp only [hik, ite_false, mul_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DeterminantFrameNormalizationValues
