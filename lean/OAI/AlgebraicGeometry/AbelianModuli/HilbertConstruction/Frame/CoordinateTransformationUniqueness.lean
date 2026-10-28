import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.ScalarRigidity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.Discriminant

/-! # Coordinate Transformation Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.CoordinateTransformationUniqueness

noncomputable section

/-! Coordinate transformations agreeing on the lines of a
projective frame differ by one unit scalar, over arbitrary rings. -/
universe u v w
variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
variable {κ : Type w}

theorem projectiveFrame_linearEquiv_unique_up_to_unit
    (b : Module.Basis κ R V) (v : V) (hu : ∀ k, IsUnit (b.repr v k))
    (T U : V ≃ₗ[R] V) (s : κ → Rˣ) (c : Rˣ)
    (hb : ∀ k, T (b k) = (s k : R) • U (b k))
    (hv : T v = (c : R) • U v) : T.toLinearMap = (c : R) • U.toLinearMap := by
  have hf : U.symm.toLinearMap.comp T.toLinearMap = (c : R) • LinearMap.id :=
    ProjectiveFrame.ScalarRigidity.projectiveFrame_linearMap_scalar b (U.symm.toLinearMap.comp T.toLinearMap)
      (fun k => (s k : R)) (fun k => by
        change U.symm (T (b k)) = _
        rw [hb, U.symm.map_smul, U.symm_apply_apply]) v hu c (by
          change U.symm (T v) = _
          rw [hv, U.symm.map_smul, U.symm_apply_apply])
  apply LinearMap.ext
  intro z
  apply U.symm.injective
  change U.symm (T z) = U.symm ((c : R) • U z)
  rw [U.symm.map_smul, U.symm_apply_apply]
  exact LinearMap.congr_fun hf z

theorem configurationFrame_linearEquiv_unique_up_to_unit [Fintype κ]
    {ι : Type*} (b₀ : Module.Basis κ R V) (v : ι → V) (σ : κ → ι) (e : ι)
    (hframe : IsUnit (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant b₀ (fun k => v (σ k)) (v e)))
    (T U : V ≃ₗ[R] V) (s : ι → Rˣ)
    (h : ∀ k, T (v k) = (s k : R) • U (v k)) :
    T.toLinearMap = (s e : R) • U.toLinearMap := by
  obtain ⟨b, hb, hu⟩ := (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant_isUnit_iff b₀ _ _).mp hframe
  exact projectiveFrame_linearEquiv_unique_up_to_unit b (v e) hu T U (fun k => s (σ k)) (s e)
    (fun k => by rw [hb]; exact h (σ k)) (h e)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.CoordinateTransformationUniqueness
