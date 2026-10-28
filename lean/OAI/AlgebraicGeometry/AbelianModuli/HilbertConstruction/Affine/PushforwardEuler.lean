import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardCohomologyFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyEulerCharacteristic

/-! # Pushforward Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardEuler

noncomputable section

/-! Affine direct image preserves genuine Euler characteristic with the structural coefficient action. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem coefficientEulerCharacteristic_affinePushforward
    {K : Type u} [Field K] {X Y : Scheme.{u}} [Y.IsSeparated]
    (f : X ⟶ Y) [IsAffineHom f] (p : Y ⟶ Spec (.of K))
    (M : X.Modules) [M.IsQuasicoherent] :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic (f ≫ p) M =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic p ((Scheme.Modules.pushforward f).obj M) := by
  apply finsum_congr
  intro q
  exact congrArg (fun n : ℕ => (-1 : ℤ) ^ q * (n : ℤ))
    (PushforwardCohomologyFiniteness.affinePushforwardCohomologyIso f p M q).toLinearEquiv.finrank_eq

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardEuler
