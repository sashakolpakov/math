import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.NormalizationTransport

/-! # Homogeneous Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.HomogeneousCoordinates

noncomputable section

/-! Clearing a common denominator expresses frame normalization by
homogeneous polynomial coordinates. On the frame locus the cleared
factor is a unit, so the actual projective point is unchanged. -/
open scoped BigOperators Classical
universe u v w
variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
variable {κ : Type w} [Fintype κ] (b : Module.Basis κ R V)

def projectiveFrameHomogeneousCoordinates (v w : V) (i : κ) : R :=
  b.repr w i * ∏ j ∈ Finset.univ.erase i, b.repr v j

theorem projectiveFrameHomogeneousCoordinates_eq
    (v : V) (hu : ∀ k, IsUnit (b.repr v k)) (w : V) :
    projectiveFrameHomogeneousCoordinates b v w =
      (∏ k, b.repr v k) • Normalization.projectiveFrameNormalization b v hu w := by
  funext i
  change b.repr w i * ∏ j ∈ Finset.univ.erase i, b.repr v j =
    (∏ k, b.repr v k) * Normalization.projectiveFrameNormalization b v hu w i
  have hp : (∏ j ∈ Finset.univ.erase i, b.repr v j) * b.repr v i = ∏ j, b.repr v j :=
    Finset.prod_erase_mul _ _ (Finset.mem_univ i)
  rw [← hp, mul_assoc, NormalizationTransport.projectiveFrameNormalization_coordinate_mul, mul_comm]

theorem projectiveFrameHomogeneousCoordinates_unit_factor
    (v : V) (hu : ∀ k, IsUnit (b.repr v k)) : IsUnit (∏ k, b.repr v k) :=
  by
    classical
    have h : ∀ s : Finset κ, IsUnit (∏ k ∈ s, b.repr v k) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa only [Finset.prod_empty] using (isUnit_one : IsUnit (1 : R))
      | @insert a s ha ih =>
        rw [Finset.prod_insert ha]
        exact (hu a).mul ih
    exact h Finset.univ

theorem projectiveFrameHomogeneousCoordinates_linear (v : V) :
    ∃ f : V →ₗ[R] (κ → R), ∀ w, f w = projectiveFrameHomogeneousCoordinates b v w := by
  refine ⟨LinearMap.pi fun i =>
    (∏ j ∈ Finset.univ.erase i, b.repr v j) • b.coord i, ?_⟩
  intro w
  funext i
  exact mul_comm _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.HomogeneousCoordinates
