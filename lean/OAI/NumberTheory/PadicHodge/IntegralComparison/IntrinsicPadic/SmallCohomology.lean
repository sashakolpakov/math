import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.AllDegreeGlobalLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallCoefficientLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient

/-! # Small Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SmallCohomology.Intrinsic

noncomputable section

/-! The actual small ordinary coefficient-quotient Čech cohomology
computes original bounded crystalline Ext in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (I : InjectiveResolution (BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (Witt.Crystalline.wittStructureMap p (ZMod p) Y)))

local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y

def coefficientIso (n i : ℕ) : (F).obj ((GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.total p X n).homology i) ≅
    (GeometricComparison.IntrinsicPadic.SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.target p X n).homology i :=
  GeometricComparison.ExactHomology.ExactHomologyComparison.iso F (.up ℕ) (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.total p X n)
    (GeometricComparison.IntrinsicPadic.SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.target p X n) (GeometricComparison.IntrinsicPadic.SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.iso p X n) i

theorem coefficient_natural (n m : ℕ) (hnm : n ≤ m) (i : ℕ) :
    (F).map (HomologicalComplex.homologyMap (GeometricComparison.IntrinsicPadic.SmallQuotientLevel.IntrinsicPadicSmallQuotientLevel.map p X n m hnm) i) ≫
      (coefficientIso p X n i).hom = (coefficientIso p X m i).hom ≫
        HomologicalComplex.homologyMap (GeometricComparison.IntrinsicPadic.IntegralCoefficientLevel.IntrinsicPadicIntegralCoefficientLevel.largeMap p X n m hnm) i :=
  GeometricComparison.ExactHomology.ExactHomologyComparison.naturality F (.up ℕ)
    (GeometricComparison.IntrinsicPadic.SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.iso p X m) (GeometricComparison.IntrinsicPadic.SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.iso p X n)
    (GeometricComparison.IntrinsicPadic.SmallQuotientLevel.IntrinsicPadicSmallQuotientLevel.map p X n m hnm)
    (GeometricComparison.IntrinsicPadic.IntegralCoefficientLevel.IntrinsicPadicIntegralCoefficientLevel.largeMap p X n m hnm)
    (GeometricComparison.IntrinsicPadic.SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.natural p X n m hnm) i

def iso (n i : ℕ) : (F).obj ((GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.total p X n).homology i) ≅
    ModuleCat.of R (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : WittVector p (ZMod p))})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w n i) :=
  coefficientIso p X n i ≪≫ AllDegreeGlobalLevel.Intrinsic.iso p X Y f hp I n i

theorem natural (n m : ℕ) (hnm : n ≤ m) (i : ℕ) :
    (F).map (HomologicalComplex.homologyMap (GeometricComparison.IntrinsicPadic.SmallQuotientLevel.IntrinsicPadicSmallQuotientLevel.map p X n m hnm) i) ≫
      (iso p X Y f hp I n i).hom = (iso p X Y f hp I m i).hom ≫
        ModuleCat.ofHom (Bounded.CohomologyTransition.map w n m hnm i) :=
  GeometricComparison.ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ (coefficient_natural p X n m hnm i)
    (AllDegreeGlobalLevel.Intrinsic.natural p X Y f hp n m hnm I i)

def linearEquiv (n i : ℕ) :=
  (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicCoefficientDescent.equiv p ((GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.total p X n).homology i)).trans
    (((GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicCoefficientDescent.restrict p).mapIso (iso p X Y f hp I n i)).toLinearEquiv)

theorem coefficientIso_one (n : ℕ) : coefficientIso p X n 1 =
    GeometricComparison.IntrinsicPadic.SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.homologyIso p X n := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SmallCohomology.Intrinsic
