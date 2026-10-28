import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.ClassComparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.PowerClasses
import OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemePullback

/-! # Line Classes -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.LineClasses

noncomputable section

/-! The constructed Poincare products give the actual group laws on pointwise line classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.ClassComparison OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemePullback.Construction
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.PowerClasses

variable {S : Scheme.{u}} {D A : Over S}
  (P : Line.Bundles.LineBundle (D ⊗ A).left)

/-- The intrinsic line-bundle class at an arbitrary pair of scheme-valued points. -/
def pairClass {T : Over S} (x : T ⟶ D) (a : T ⟶ A) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left :=
  Line.Comparison.Bundle.classEquiv T.left (Biextension.PowerClasses.pointClass P x a)

variable [GrpObj D] [GrpObj A]
  (Dh : FiberwiseMultiplication.Multiplication (fst D A) (snd D A) P)
  (Dv : FiberwiseMultiplication.Multiplication (snd D A) (fst D A) P)

include Dh in
omit [GrpObj A] in
theorem pairClass_mul_left {T : Over S} (x y : T ⟶ D) (a : T ⟶ A) :
    pairClass P (x * y) a = pairClass P x a * pairClass P y a :=
  (congrArg (Line.Comparison.Bundle.classEquiv T.left) (Biextension.PowerClasses.first_mul P Dh x y a)).trans (Tensor.ClassComparison.classEquiv_tensor _ _)

include Dv in
omit [GrpObj D] in
theorem pairClass_mul_right {T : Over S} (x : T ⟶ D) (a b : T ⟶ A) :
    pairClass P x (a * b) = pairClass P x a * pairClass P x b :=
  (congrArg (Line.Comparison.Bundle.classEquiv T.left) (Biextension.PowerClasses.second_mul P Dv x a b)).trans (Tensor.ClassComparison.classEquiv_tensor _ _)

include Dh in
omit [GrpObj A] in
theorem pairClass_one_left {T : Over S} (a : T ⟶ A) : pairClass P (1 : T ⟶ D) a = 1 :=
  (congrArg (Line.Comparison.Bundle.classEquiv T.left) (Biextension.PowerClasses.first_one P Dh a)).trans (Line.Comparison.Bundle.classEquiv_trivial T.left)

include Dv in
omit [GrpObj D] in
theorem pairClass_one_right {T : Over S} (x : T ⟶ D) : pairClass P x (1 : T ⟶ A) = 1 :=
  (congrArg (Line.Comparison.Bundle.classEquiv T.left) (Biextension.PowerClasses.second_one P Dv x)).trans (Line.Comparison.Bundle.classEquiv_trivial T.left)

include Dv in
omit [GrpObj D] in
theorem pairClass_inv_right {T : Over S} (x : T ⟶ D) (a : T ⟶ A) :
    pairClass P x a⁻¹ = (pairClass P x a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pairClass_mul_right P Dv, inv_mul_cancel, pairClass_one_right P Dv]

include Dh in
omit [GrpObj A] in
theorem pairClass_pow_left {T : Over S} (x : T ⟶ D) (a : T ⟶ A) (n : ℕ) :
    pairClass P (x ^ n) a = pairClass P x a ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pairClass_one_left P Dh]
  | succ n ih => rw [pow_succ, pairClass_mul_left P Dh, ih, pow_succ]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.LineClasses
