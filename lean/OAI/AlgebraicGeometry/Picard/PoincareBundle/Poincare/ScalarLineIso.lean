import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.ScalarClasses
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

/-! # Scalar Line Iso -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.ScalarLineIso

noncomputable section

/-! Moving an integer between Poincare coordinates gives an actual line-sheaf isomorphism on every parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

variable {S : Scheme.{u}} {D A : Over S} [GrpObj D] [GrpObj A]
  (P : Line.Bundles.LineBundle (D ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst D A) (snd D A) P)
  (Dv : FiberwiseMultiplication.Multiplication (snd D A) (fst D A) P)

include Dh Dv

/-- The scalar-balance equality already holds for actual line bundles before relative Picard sheafification. -/
theorem exists_iso {T : Over S} (x : T ⟶ D) (n : ℕ) :
    Nonempty ((Scheme.Modules.pullback (𝟙 T ⊗ₘ (𝟙 A) ^ n).left).obj (FirstBiextensionFactor.familyLine P x).sheaf ≅
      (FirstBiextensionFactor.familyLine P (x ^ n)).sheaf) :=
  Quotient.exact (ScalarClasses.scalar_familyClass P Dh Dv x n)

/-- An actual scalar-balancing isomorphism, with arbitrary possibly nonreduced parameter scheme. -/
def scalarIso {T : Over S} (x : T ⟶ D) (n : ℕ) :
    (Scheme.Modules.pullback (𝟙 T ⊗ₘ (𝟙 A) ^ n).left).obj (FirstBiextensionFactor.familyLine P x).sheaf ≅
      (FirstBiextensionFactor.familyLine P (x ^ n)).sheaf :=
  Classical.choice (exists_iso P Dh Dv x n)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.ScalarLineIso
