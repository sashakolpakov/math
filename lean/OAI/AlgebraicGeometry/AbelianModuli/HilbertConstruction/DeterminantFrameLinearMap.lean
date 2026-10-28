import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.Discriminant

/-! # Determinant Frame Linear Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DeterminantFrameLinearMap

noncomputable section

/-! The polynomial determinant coordinates form an actual invertible
linear map on the frame-discriminant open. Its invertibility is proved
over arbitrary commutative rings. -/
open scoped BigOperators Classical
universe u v w
variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
variable {κ : Type w} [Fintype κ]

def determinantFrameLinearMap (e : Module.Basis κ R V) (b : κ → V) (v : V) :
    V →ₗ[R] (κ → R) :=
  LinearMap.pi fun i =>
    (∏ j ∈ Finset.univ.erase i, e.det (Function.update b j v)) •
      e.det.toMultilinearMap.toLinearMap b i

theorem determinantFrameLinearMap_apply (e : Module.Basis κ R V) (b : κ → V) (v w : V) :
    determinantFrameLinearMap e b v w = ProjectiveFrame.DeterminantCoordinates.projectiveFrameDeterminantCoordinates e b v w := by
  funext i
  exact mul_comm _ _

theorem determinantFrameLinearMap_bijective (e : Module.Basis κ R V) (b : κ → V) (v : V)
    (h : IsUnit (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant e b v)) :
    Function.Bijective (determinantFrameLinearMap e b v) := by
  obtain ⟨c, hc, hu⟩ := (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant_isUnit_iff e b v).mp h
  have hbc : b = c := funext (fun i => (hc i).symm)
  subst b
  let a := (e.det c) ^ Fintype.card κ * ∏ i, c.repr v i
  have ha : IsUnit a := ((e.isUnit_det c).pow _).mul
    (ProjectiveFrame.HomogeneousCoordinates.projectiveFrameHomogeneousCoordinates_unit_factor c v hu)
  let f : V ≃ₗ[R] (κ → R) :=
    (ProjectiveFrame.Normalization.projectiveFrameNormalization c v hu).trans (LinearEquiv.smulOfUnit ha.unit)
  have hf : (determinantFrameLinearMap e c v : V → (κ → R)) = f := by
    funext w
    rw [determinantFrameLinearMap_apply, ProjectiveFrame.DeterminantCoordinates.projectiveFrameDeterminantCoordinates_eq,
      ProjectiveFrame.HomogeneousCoordinates.projectiveFrameHomogeneousCoordinates_eq c v hu]
    change (e.det c) ^ Fintype.card κ • ((∏ i, c.repr v i) •
      ProjectiveFrame.Normalization.projectiveFrameNormalization c v hu w) =
        (ha.unit : R) • ProjectiveFrame.Normalization.projectiveFrameNormalization c v hu w
    rw [smul_smul, ha.unit_spec]
  rw [hf]
  exact f.bijective

def determinantFrameLinearEquiv (e : Module.Basis κ R V) (b : κ → V) (v : V)
    (h : IsUnit (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant e b v)) : V ≃ₗ[R] (κ → R) :=
  LinearEquiv.ofBijective (determinantFrameLinearMap e b v)
    (determinantFrameLinearMap_bijective e b v h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DeterminantFrameLinearMap
