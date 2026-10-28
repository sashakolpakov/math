import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.LineBundleEuler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Classes
import Mathlib.Algebra.Group.Hom.End

/-! # Euler Shifts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EulerShifts

noncomputable section

/-! Genuine Euler characteristic is a function of actual line-bundle classes. Tensor product acts on these functions by commuting additive shifts, whose orbits are the actual tensor-power Euler sequences. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

def lineBundleClassEuler {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) : Line.Bundles.LineBundle.IsoClass X → ℤ :=
  Quotient.lift (fun L : Line.Bundles.LineBundle X => CohomologyEulerCharacteristic.coefficientEulerCharacteristic p L.sheaf)
    (fun _ _ ⟨e⟩ => Proper.LineBundleEuler.coefficientEulerCharacteristic_eq_of_sheafIso p e)

@[simp]
theorem lineBundleClassEuler_classOf {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X) :
    lineBundleClassEuler p (Line.Bundles.LineBundle.classOf L) = CohomologyEulerCharacteristic.coefficientEulerCharacteristic p L.sheaf := rfl

def lineBundleEulerShift (X : Scheme.{u}) :
    Line.Bundles.LineBundle.IsoClass X →* AddMonoid.End (Line.Bundles.LineBundle.IsoClass X → ℤ) where
  toFun a :=
    { toFun := fun f b => f (b * a)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_one' := by
    ext f b
    change f (b * 1) = f b
    rw [mul_one]
  map_mul' a b := by
    ext f c
    change f (c * (a * b)) = f ((c * a) * b)
    rw [mul_assoc]

theorem lineBundleEulerShift_commute (X : Scheme.{u}) (a b : Line.Bundles.LineBundle.IsoClass X) :
    Commute (lineBundleEulerShift X a) (lineBundleEulerShift X b) := by
  change lineBundleEulerShift X a * lineBundleEulerShift X b =
    lineBundleEulerShift X b * lineBundleEulerShift X a
  rw [← (lineBundleEulerShift X).map_mul, ← (lineBundleEulerShift X).map_mul, mul_comm a b]

theorem lineBundleEulerShift_power_eval_one {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X) (n : ℕ) :
    ((lineBundleEulerShift X (Line.Bundles.LineBundle.classOf L)) ^ n) (lineBundleClassEuler p) 1 =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (L.tensorPower n).sheaf := by
  rw [← (lineBundleEulerShift X).map_pow]
  change lineBundleClassEuler p (1 * Line.Bundles.LineBundle.classOf L ^ n) = _
  rw [one_mul, ← Line.Bundles.LineBundle.classOf_tensorPower]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EulerShifts
