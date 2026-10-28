import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.ScalarRigidity
import Mathlib.LinearAlgebra.Pi

/-! # Normalization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.Normalization

noncomputable section

/-! An actual projective frame has an explicit invertible linear
normalization over any commutative base ring: its additional vector maps
to the all-one vector and its basis lines map to the coordinate lines. -/
open scoped Classical
universe u v w
variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
variable {κ : Type w} [Fintype κ] (b : Module.Basis κ R V)
variable (v : V) (hu : ∀ k, IsUnit (b.repr v k))

def projectiveFrameNormalization : V ≃ₗ[R] (κ → R) :=
  b.equivFun.trans (LinearEquiv.piCongrRight fun k =>
    (LinearEquiv.smulOfUnit ((hu k).unit⁻¹) : R ≃ₗ[R] R))

theorem projectiveFrameNormalization_additional :
    projectiveFrameNormalization b v hu v = fun _ => (1 : R) := by
  funext k
  change (↑((hu k).unit⁻¹) : R) * b.repr v k = 1
  exact (congrArg (fun a : R => (↑((hu k).unit⁻¹) : R) * a)
    (hu k).unit_spec.symm).trans (Units.inv_mul (hu k).unit)

theorem projectiveFrameNormalization_basis (i k : κ) :
    projectiveFrameNormalization b v hu (b i) k =
      if i = k then (↑((hu k).unit⁻¹) : R) else 0 := by
  change (↑((hu k).unit⁻¹) : R) * b.repr (b i) k = _
  rw [b.repr_self_apply]
  split_ifs
  · exact mul_one _
  · exact mul_zero _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.Normalization
