import OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledDualData

/-! # Family Normalization -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.FamilyNormalization.Family

noncomputable section

/-! The actual Poincare normalization gives a zero frame on every represented family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor

variable {S : Scheme.{u}} {A : Over S} [GrpObj A]
  (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) {T : Over S} (m : T ⟶ D.abelian)

/-- The actual family-zero square commutes with the Poincare parameter map. -/
theorem zero_square :
    lift (𝟙 T) (1 : T ⟶ A) ≫ (m ⊗ₘ 𝟙 A) =
      m ≫ lift (𝟙 D.abelian) (1 : D.abelian ⟶ A) := by
  simp

/-- Every actual Poincare family retains its specified zero-section trivialization. -/
def zeroFrame : (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A)).left).obj
    (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) m).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left :=
  (Scheme.Modules.pullbackComp (lift (𝟙 T) (1 : T ⟶ A)).left (m ⊗ₘ 𝟙 A).left).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (zero_square D m))).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackComp m.left (lift (𝟙 D.abelian) (1 : D.abelian ⟶ A)).left).symm.app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullback m.left).mapIso (Classical.choice D.normalizedAtAbelianZero) ≪≫
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso m.left

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.FamilyNormalization.Family
