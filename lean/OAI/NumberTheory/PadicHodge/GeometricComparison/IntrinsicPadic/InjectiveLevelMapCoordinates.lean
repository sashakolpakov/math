import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.DiagonalInjectiveLevelHomotopy
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveSectionLevelCoordinates

/-! # Injective Level Map Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveLevelMapCoordinates.IntrinsicPadicInjectiveLevelMapCoordinates

noncomputable section

/-! The injective level map used in the native comparison homotopy is
the actual original open-section restriction map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p])))
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (n m : ℕ) (hnm : n ≤ m)
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y)))

theorem map_eq : DiagonalInjectiveLevelHomotopy.IntrinsicPadicDiagonalInjectiveLevelHomotopy.injectiveMap p X Y f n m hnm I =
    InjectiveSectionLevelCoordinates.IntrinsicPadicInjectiveSectionLevelCoordinates.sectionsMap p X Y f n m hnm I := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveLevelMapCoordinates.IntrinsicPadicInjectiveLevelMapCoordinates
