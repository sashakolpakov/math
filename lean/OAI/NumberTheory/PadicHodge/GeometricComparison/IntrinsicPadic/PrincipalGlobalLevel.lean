import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalCoefficientLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralGlobalLevel

/-! # Principal Global Level -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalGlobalLevel.IntrinsicPadicPrincipalGlobalLevel

noncomputable section

/-! The original principal quotient H-one tower compares naturally
with the original bounded crystalline Ext tower. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y)))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y

def iso (q : ℕ) : PrincipalCoefficientLevel.IntrinsicPadicPrincipalCoefficientLevel.source p X q ≅
    ModuleCat.of R (IntegralComparison.BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : WittVector p (ZMod p))})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w q 1) :=
  PrincipalCoefficientLevel.IntrinsicPadicPrincipalCoefficientLevel.iso p X q ≪≫
    IntegralGlobalLevel.IntrinsicPadicIntegralGlobalLevel.homologyIso p X Y f hp I q

theorem natural (n m : ℕ) (hnm : n ≤ m) : PrincipalCoefficientLevel.IntrinsicPadicPrincipalCoefficientLevel.sourceMap p X n m hnm ≫
    (iso p X Y f hp I n).hom = (iso p X Y f hp I m).hom ≫
      ModuleCat.ofHom (IntegralComparison.Bounded.CohomologyTransition.map w n m hnm 1) :=
  ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _
    (PrincipalCoefficientLevel.IntrinsicPadicPrincipalCoefficientLevel.natural p X n m hnm)
    (IntegralGlobalLevel.IntrinsicPadicIntegralGlobalLevel.natural p X Y f hp n m hnm I)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalGlobalLevel.IntrinsicPadicPrincipalGlobalLevel
