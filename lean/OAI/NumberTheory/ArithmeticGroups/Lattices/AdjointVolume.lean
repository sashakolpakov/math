import OAI.NumberTheory.ArithmeticGroups.Lattices.KillingScalarExtension
import OAI.NumberTheory.ArithmeticGroups.Lattices.ExponentialNormal

/-! # Adjoint Volume -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointVolume.Construction

noncomputable section

/-! Automorphisms of a Killing Lie algebra have determinant of absolute
value one, because they preserve its nondegenerate Killing form. -/

open scoped Classical

theorem bilinear_isometry_determinant_sq
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate)
    (e : V ≃ₗ[k] V) (he : ∀ x y, B (e x) (e y) = B x y) :
    LinearMap.det e.toLinearMap ^ 2 = 1 := by
  let b := Module.finBasis k V
  have hc : B.comp e.toLinearMap e.toLinearMap = B := by
    ext x y
    exact he x y
  have hm := congrArg (fun Q : LinearMap.BilinForm k V => (LinearMap.BilinForm.toMatrix b Q).det) hc
  rw [LinearMap.BilinForm.toMatrix_comp b b, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    LinearMap.det_toMatrix] at hm
  have hdet : (LinearMap.BilinForm.toMatrix b B).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB
  apply mul_right_cancel₀ hdet
  calc
    LinearMap.det e.toLinearMap ^ 2 * (LinearMap.BilinForm.toMatrix b B).det =
      LinearMap.det e.toLinearMap * (LinearMap.BilinForm.toMatrix b B).det *
        LinearMap.det e.toLinearMap := by ring
    _ = 1 * (LinearMap.BilinForm.toMatrix b B).det := by simpa only [one_mul] using hm

theorem killing_LieEquiv_determinant_sq
    {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L] [Module.Finite k L]
    [LieAlgebra.IsKilling k L] (e : L ≃ₗ⁅k⁆ L) :
    LinearMap.det e.toLinearMap ^ 2 = 1 := by
  apply bilinear_isometry_determinant_sq (killingForm k L)
    (LieAlgebra.IsKilling.killingForm_nondegenerate k L) e.toLinearEquiv
  exact LieAlgebra.killingForm_of_equiv_apply e

theorem killing_LieEquiv_norm_determinant
    {k L : Type*} [NormedField k] [LieRing L] [LieAlgebra k L] [Module.Finite k L]
    [LieAlgebra.IsKilling k L] (e : L ≃ₗ⁅k⁆ L) :
    ‖LinearMap.det e.toLinearMap‖ = 1 := by
  have h := congrArg (fun x : k => ‖x‖) (killing_LieEquiv_determinant_sq e)
  rw [norm_pow, norm_one] at h
  have hnonneg := norm_nonneg (LinearMap.det e.toLinearMap)
  nlinarith

theorem infinitesimalAdjoint_norm_determinant
    {k : Type} [NormedField k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n)
    (hconn : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple) (g : G.RationalPoints) :
    ‖LinearMap.det (ExponentialNormal.Construction.infinitesimalAdjoint G g).toLinearMap‖ = 1 := by
  let : LieAlgebra.IsKilling k (Infinitesimal.Action.Construction.infinitesimalStabilizer G) := KillingScalarDescent.Construction.infinitesimal_isKilling G hconn hsemi
  exact killing_LieEquiv_norm_determinant _

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointVolume.Construction
