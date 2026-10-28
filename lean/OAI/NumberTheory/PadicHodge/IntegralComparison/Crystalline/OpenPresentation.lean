import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCover

/-! # Open Presentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.OpenPresentation

noncomputable section

/-!
# IntegralComparison: small presentations over an affine open of X

If the closed map of a big crystalline object factors through an affine
open of X, its affine polynomial presentation gives an actual morphism
to a small crystalline object over X.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

variable (p : ℕ) [Fact p.Prime] (k C : Type u) [Field k] [CharP k p]
variable [CommRing C] [Algebra k C] (X : Over (Spec (CommRingCat.of k)))
variable (j : (Presentation.affineScheme k C).left ⟶ X.left) [IsOpenImmersion j]
variable (hj : j ≫ X.hom = (Presentation.affineScheme k C).hom)

include hj in
omit [IsOpenImmersion j] [CharP k p] in
lemma overWitt : j ≫ (Witt.Crystalline.wittStructureMap p k X) = (Witt.Crystalline.wittStructureMap p k (Presentation.affineScheme k C)) := by
  unfold Witt.Crystalline.wittStructureMap
  rw [← Category.assoc, hj]

variable (T : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : (WittVector p k))}) (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X))
    (closedFactor : Spec (CommRingCat.of (T.ring ⧸ T.ideal)) ⟶ (Presentation.affineScheme k C).left)
  (ht : closedFactor ≫ j = T.mapToX)

abbrev affineObject : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : (WittVector p k))}) (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Presentation.affineScheme k C)) where
  ring := T.ring
  base := T.base
  ideal := T.ideal
  dividedPowers := T.dividedPowers
  baseCompatible := T.baseCompatible
  primeNilpotent := T.primeNilpotent
  nilIdeal := T.nilIdeal
  mapToX := closedFactor
  overBase := by
    rw [← overWitt p k C X j hj, ← Category.assoc, ht]
    exact T.overBase

variable (n : ℕ)

abbrev presentation : Site.AffineThickening p (WittVector p k) (Ideal.span {(p : (WittVector p k))}) (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) where
  ring := (Presentation.presentationObject p k C n).ring
  base := (Presentation.presentationObject p k C n).base
  ideal := (Presentation.presentationObject p k C n).ideal
  dividedPowers := (Presentation.presentationObject p k C n).dividedPowers
  baseCompatible := (Presentation.presentationObject p k C n).baseCompatible
  primeNilpotent := (Presentation.presentationObject p k C n).primeNilpotent
  nilIdeal := (Presentation.presentationObject p k C n).nilIdeal
  openMap := (Presentation.presentationObject p k C n).openMap ≫ j
  overBase := by
    rw [Category.assoc, overWitt p k C X j hj]
    exact (Presentation.presentationObject p k C n).overBase

omit n in
def presentationMorphism : T ⟶ BigCrystallineSite.fromSmall.obj
    (presentation p k C X j hj (BigCrystallineCover.levelBound p k C
      (affineObject p k C X j hj T closedFactor ht))) where
  ringMap := (BigCrystallineCover.presentationMorphism p k C
    (affineObject p k C X j hj T closedFactor ht)).ringMap
  overBase := (BigCrystallineCover.presentationMorphism p k C
    (affineObject p k C X j hj T closedFactor ht)).overBase
  overX := by
    let α := BigCrystallineCover.presentationMorphism p k C
      (affineObject p k C X j hj T closedFactor ht)
    change BigCrystallineSite.Object.closed.map α ≫ ((Presentation.presentationObject p k C _).openMap ≫ j) = T.mapToX
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ j) α.overX).trans ht)

omit n in
include hj ht in
lemma incoming_nonempty : Nonempty (StructuredArrow T
    (BigCrystallineSite.fromSmall (p := p) (B := (WittVector p k)) (J := Ideal.span {(p : (WittVector p k))}) (δ := (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)) (f := (Witt.Crystalline.wittStructureMap p k X)))) :=
  ⟨StructuredArrow.mk (presentationMorphism p k C X j hj T closedFactor ht)⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.OpenPresentation
