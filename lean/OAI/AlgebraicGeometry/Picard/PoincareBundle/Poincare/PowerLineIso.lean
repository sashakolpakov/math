import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.LineClasses
import OAI.AlgebraicGeometry.Picard.PoincareBundle.DiagonalLineAmpleness

/-! # Power Line Iso -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.PowerLineIso

noncomputable section

/-! An integer multiple in the Poincare parameter is the corresponding tensor power of the actual family line. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.LineClasses OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

variable {S : Scheme.{u}} {D A : Over S} [GrpObj D]
  (P : Line.Bundles.LineBundle (D ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst D A) (snd D A) P)

include Dh

/-- The first Poincare product proves the power formula on the entire parameter family. -/
theorem class_power {T : Over S} (φ : T ⟶ D) (n : ℕ) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((Line.Comparison.Bundle.toShared P).pullback ((φ ^ n) ⊗ₘ 𝟙 A).left) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((Line.Comparison.Bundle.toShared P).pullback (φ ⊗ₘ 𝟙 A).left) ^ n := by
  have h := LineClasses.pairClass_pow_left P Dh (fst T A ≫ φ) (snd T A) n
  have hn : (φ ^ n) ⊗ₘ 𝟙 A = lift ((fst T A ≫ φ) ^ n) (snd T A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.comp_pow]
  have h0 : φ ⊗ₘ 𝟙 A = lift (fst T A ≫ φ) (snd T A) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((φ ^ n) ⊗ₘ 𝟙 A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Line.Comparison.Bundle.toShared P)) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (φ ⊗ₘ 𝟙 A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Line.Comparison.Bundle.toShared P)) ^ n
  rw [congrArg Over.Hom.left hn, congrArg Over.Hom.left h0]
  exact h

/-- Equality of actual line classes supplies an actual isomorphism to the tensor power. -/
theorem exists_iso {T : Over S} (φ : T ⟶ D) (n : ℕ) :
    Nonempty (((Line.Comparison.Bundle.toShared P).pullback ((φ ^ n) ⊗ₘ 𝟙 A).left).sheaf ≅
      (((Line.Comparison.Bundle.toShared P).pullback (φ ⊗ₘ 𝟙 A).left).tensorPower n).sheaf) :=
  Quotient.exact ((class_power P Dh φ n).trans
    (PELModuli.IntegralModel.AmpleTensor.PolarizationAmpleness.tensorPower_class
      ((Line.Comparison.Bundle.toShared P).pullback (φ ⊗ₘ 𝟙 A).left) n).symm)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.PowerLineIso
