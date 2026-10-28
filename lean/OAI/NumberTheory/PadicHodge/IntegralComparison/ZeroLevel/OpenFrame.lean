import OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.LevelFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.OpenPresentation

/-! # Open Frame -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.OpenFrame

noncomputable section

/-!
# IntegralComparison: smooth affine open charts give original zeroth-level frames over the whole scheme
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k C : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [Algebra k C] (X : Over (Spec (CommRingCat.of k)))
  (j : (Crystalline.Presentation.affineScheme k C).left ⟶ X.left) [IsOpenImmersion j]
  (hj : j ≫ X.hom = (Crystalline.Presentation.affineScheme k C).hom)

def frame : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) :=
  (BigCrystallineSite.postcompose j (Crystalline.OpenPresentation.overWitt p k C X j hj)).obj (LevelFrame.frame p k C)

def boundedFrame : BoundedCrystalline.Site.Objects (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) 0 :=
  ⟨frame p k C X j hj, (pow_one (p : C)).trans (LevelFrame.prime_zero p k C)⟩

variable (U : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X))
  (t : Spec (CommRingCat.of (U.ring ⧸ U.ideal)) ⟶ (Crystalline.Presentation.affineScheme k C).left)
  (ht : t ≫ j = U.mapToX)

include ht in
omit [IsOpenImmersion j] in
theorem exists_map [Algebra.Smooth k C] (h : (p : U.ring) = 0) : Nonempty (U ⟶ frame p k C X j hj) := by
  let A := Crystalline.OpenPresentation.affineObject p k C X j hj U t ht
  obtain ⟨a⟩ := LevelFrame.exists_map p k C A h
  refine ⟨{ ringMap := a.ringMap, overBase := a.overBase, overX := ?_ }⟩
  change Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap A (LevelFrame.frame p k C) a.ringMap)) ≫
    ((LevelFrame.frame p k C).mapToX ≫ j) = U.mapToX
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun m => m ≫ j) a.overX).trans ht)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.OpenFrame
