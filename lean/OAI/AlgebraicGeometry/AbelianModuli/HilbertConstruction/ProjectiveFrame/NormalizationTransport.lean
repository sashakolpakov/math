import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.Normalization
import Mathlib.LinearAlgebra.Basis.SMul

/-! # Normalization Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.NormalizationTransport

noncomputable section

/-! Frame normalization respects linear coordinate changes. Rescaling
the chosen basis lines cancels, and rescaling the additional frame point
changes the normalization only by a common unit scalar. -/
open scoped Classical
universe u v w z
variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]
variable {W : Type w} [AddCommGroup W] [Module R W]
variable {κ : Type z} [Fintype κ]

theorem projectiveFrameNormalization_coordinate_mul
    (b : Module.Basis κ R V) (v : V) (hu : ∀ k, IsUnit (b.repr v k)) (w : V) (k : κ) :
    b.repr v k * Normalization.projectiveFrameNormalization b v hu w k = b.repr w k := by
  change b.repr v k * ((↑((hu k).unit⁻¹) : R) * b.repr w k) = _
  conv_lhs => lhs; rw [← (hu k).unit_spec]
  rw [← mul_assoc, Units.mul_inv, one_mul]

theorem projectiveFrameNormalization_map
    (b : Module.Basis κ R V) (v : V) (hu : ∀ k, IsUnit (b.repr v k))
    (f : V ≃ₗ[R] W) (hf : ∀ k, IsUnit ((b.map f).repr (f v) k)) (w : V) :
    Normalization.projectiveFrameNormalization (b.map f) (f v) hf (f w) =
      Normalization.projectiveFrameNormalization b v hu w := by
  funext k
  apply (hu k).mul_left_cancel
  have hv : (b.map f).repr (f v) k = b.repr v k := by
    change b.repr (f.symm (f v)) k = _
    rw [f.symm_apply_apply]
  have hw : (b.map f).repr (f w) k = b.repr w k := by
    change b.repr (f.symm (f w)) k = _
    rw [f.symm_apply_apply]
  rw [projectiveFrameNormalization_coordinate_mul,
    ← hv, projectiveFrameNormalization_coordinate_mul, hw]

theorem projectiveFrameNormalization_unitsSMul
    (b : Module.Basis κ R V) (v : V) (hu : ∀ k, IsUnit (b.repr v k))
    (a : κ → Rˣ) (c : Rˣ)
    (hscaled : ∀ k, IsUnit ((b.unitsSMul a).repr ((c : R) • v) k)) (w : V) :
    Normalization.projectiveFrameNormalization (b.unitsSMul a) ((c : R) • v) hscaled w =
      (↑(c⁻¹) : R) • Normalization.projectiveFrameNormalization b v hu w := by
  funext k
  apply (hscaled k).mul_left_cancel
  rw [projectiveFrameNormalization_coordinate_mul]
  change (b.unitsSMul a).repr w k =
    (b.unitsSMul a).repr ((c : R) • v) k *
      ((↑(c⁻¹) : R) * Normalization.projectiveFrameNormalization b v hu w k)
  rw [Module.Basis.repr_unitsSMul, Module.Basis.repr_unitsSMul, map_smul]
  change (↑((a k)⁻¹) : R) * b.repr w k =
    ((↑((a k)⁻¹) : R) * ((c : R) * b.repr v k)) *
      ((↑(c⁻¹) : R) * Normalization.projectiveFrameNormalization b v hu w k)
  symm
  calc
    _ = (↑((a k)⁻¹) : R) * ((c : R) * (↑(c⁻¹) : R)) *
        (b.repr v k * Normalization.projectiveFrameNormalization b v hu w k) := by ring
    _ = _ := by rw [Units.mul_inv, mul_one, projectiveFrameNormalization_coordinate_mul]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.NormalizationTransport
