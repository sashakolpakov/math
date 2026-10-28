import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.ClassUnits
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

/-! # Power Classes -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.PowerClasses

noncomputable section

/-! Balancing scalar multiplication between the two coordinates of an actual biextension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LineBundles OAI.AlgebraicGeometry.Picard.PoincareBundle.Origin OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

variable {S : Scheme.{u}} {D A : Over S}
  (P : Line.Bundles.LineBundle (D ⊗ A).left)

/-- The actual line class at a pair of arbitrary scheme-valued points. -/
def pointClass {T : Over S} (x : T ⟶ D) (a : T ⟶ A) : Line.Bundles.LineBundleClass T.left :=
  Line.Bundles.LineBundleClass.pullback (lift x a).left (Line.Bundles.LineBundleClass.mk P)

variable [GrpObj D] [GrpObj A]
  (Dh : FiberwiseMultiplication.Multiplication (fst D A) (snd D A) P)
  (Dv : FiberwiseMultiplication.Multiplication (snd D A) (fst D A) P)

include Dh in
omit [GrpObj A] in
/-- The genuine first product yields multiplication of pointwise line classes. -/
theorem first_mul {T : Over S} (x y : T ⟶ D) (a : T ⟶ A) :
    pointClass P (x * y) a = Tensor.LineBundles.tensorClass (pointClass P x a) (pointClass P y a) := by
  have hp : FiberwiseMultiplication.ProductRel (fst D A) (snd D A) (lift x a) (lift y a) (lift (x * y) a) := by
    simp [FiberwiseMultiplication.ProductRel]
  let e := @asIso _ _ _ _ (Bilinear.BilinearPullback.toHom (Dh.product _ _ _ hp)) (Dh.product_isIso _ _ _ hp)
  symm
  exact Quotient.sound ⟨e⟩

include Dv in
omit [GrpObj D] in
/-- The genuine second product yields multiplication of the same pointwise classes. -/
theorem second_mul {T : Over S} (x : T ⟶ D) (a b : T ⟶ A) :
    pointClass P x (a * b) = Tensor.LineBundles.tensorClass (pointClass P x a) (pointClass P x b) := by
  have hp : FiberwiseMultiplication.ProductRel (snd D A) (fst D A) (lift x a) (lift x b) (lift x (a * b)) := by
    simp [FiberwiseMultiplication.ProductRel]
  let e := @asIso _ _ _ _ (Bilinear.BilinearPullback.toHom (Dv.product _ _ _ hp)) (Dv.product_isIso _ _ _ hp)
  symm
  exact Quotient.sound ⟨e⟩

include Dh in
omit [GrpObj A] in
/-- The genuine first unit identifies the neutral point line with the structure line. -/
theorem first_one {T : Over S} (a : T ⟶ A) :
    pointClass P (1 : T ⟶ D) a = Origin.trivialLineClass T.left := by
  exact Quotient.sound ⟨(Dh.unitFrame (lift 1 a) (by simp)).symm⟩

include Dv in
omit [GrpObj D] in
/-- The genuine second unit gives the analogous neutral identification. -/
theorem second_one {T : Over S} (x : T ⟶ D) :
    pointClass P x (1 : T ⟶ A) = Origin.trivialLineClass T.left := by
  exact Quotient.sound ⟨(Dv.unitFrame (lift x 1) (by simp)).symm⟩

include Dh Dv

/-- Multiplication by the same integer can be moved between the two coordinates, on all test schemes. -/
theorem pow_balance {T : Over S} (x : T ⟶ D) (a : T ⟶ A) (n : ℕ) :
    pointClass P (x ^ n) a = pointClass P x (a ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, first_one P Dh, second_one P Dv]
  | succ n ih => rw [pow_succ, pow_succ, first_mul P Dh, second_mul P Dv, ih]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.PowerClasses
