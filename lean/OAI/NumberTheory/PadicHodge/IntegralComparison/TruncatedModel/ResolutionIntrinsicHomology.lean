import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechIso

/-! # Resolution Intrinsic Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionIntrinsicHomology.Intrinsic

noncomputable section

/-! The original injective Cech comparison with its source expressed as
the literal native frame total before taking the inverse isomorphism. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k Y) n))

attribute [local irreducible] HomologicalComplex.homology

def iso (q : ℕ) :
    (FrameCech.Complexes.target p k n X Y f I).homology q ≅
    ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := WittVector p k))
      (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
        (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
        (Witt.Crystalline.wittStructureMap p k Y) n q) :=
  GlobalEdge.InjectiveCech.homologyIso p k n X Y f I q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionIntrinsicHomology.Intrinsic
