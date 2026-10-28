import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallineRestrictionExt
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallReductionCoordinates

/-! # Small Global Level -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallGlobalLevel.IntrinsicPadicSmallGlobalLevel

noncomputable section

/-! The original finite crystalline comparison in the actual small
quotient Cech coordinates, after descending its coefficient field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsProper Y.hom] [Smooth Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y)))
  (hprojective : IntegralComparison.Projectivity.Construction.ProjectiveOver (ZMod p) Y.hom)

local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p
local notation "D" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicCoefficientDescent.restrict p

def iso (n : ℕ) := SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.homologyIso p X n ≪≫
  IntegralGlobalLevel.IntrinsicPadicIntegralGlobalLevel.homologyIso p X Y f hp I n

omit [Smooth Y.hom] in
theorem principal_factor (n : ℕ) : (PrincipalGlobalLevel.IntrinsicPadicPrincipalGlobalLevel.iso p X Y f hp I n).hom =
    (F).map (FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline.sourceHomologyIso p X n).inv ≫ (iso p X Y f hp I n).hom :=
  Category.assoc ((F).map (FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline.sourceHomologyIso p X n).inv)
    (SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.homologyIso p X n).hom
    (IntegralGlobalLevel.IntrinsicPadicIntegralGlobalLevel.homologyIso p X Y f hp I n).hom

omit [Smooth Y.hom] in
theorem reduction (n : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1) :
    CrystallineRestrictionExt.IntrinsicPadicIntegralCrystallineReduction.finiteEquiv p X Y f hp I n
      (IntegralReductionCoordinates.IntrinsicPadicIntegralReductionCoordinates.reduction p X (n + 1) x) =
    (D).map (iso p X Y f hp I n).hom
      (Coefficient.IntrinsicPadicCoefficientDescent.equiv p ((Coefficient.IntrinsicPadicSmallQuotientTotal.total p X n).homology 1)
        (SmallReductionCoordinates.IntrinsicPadicSmallReductionCoordinates.map p X n x)) := by
  have h := congrArg (D).map (principal_factor p X Y f hp I n)
  erw [Functor.map_comp] at h
  have hx := ConcreteCategory.congr_hom h
    (Coefficient.IntrinsicPadicCoefficientDescent.equiv p _ (IntegralReductionCoordinates.IntrinsicPadicIntegralReductionCoordinates.reduction p X (n + 1) x))
  exact hx.trans (congrArg ((D).map (iso p X Y f hp I n).hom)
    (Coefficient.IntrinsicPadicCoefficientDescent.natural p (FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline.sourceHomologyIso p X n).inv
      (IntegralReductionCoordinates.IntrinsicPadicIntegralReductionCoordinates.reduction p X (n + 1) x)).symm)

theorem restriction (n : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1) :
    CrystallineRestrictionExt.IntrinsicPadicIntegralCrystallineReduction.restriction p Y n
      (IntegralCrystallineEquiv.IntrinsicPadicIntegralCrystallineEquiv.equiv p X Y f hp I hprojective x) =
    (D).map (iso p X Y f hp I n).hom
      (Coefficient.IntrinsicPadicCoefficientDescent.equiv p ((Coefficient.IntrinsicPadicSmallQuotientTotal.total p X n).homology 1)
        (SmallReductionCoordinates.IntrinsicPadicSmallReductionCoordinates.map p X n x)) :=
  (LinearMap.congr_fun (CrystallineRestrictionExt.IntrinsicPadicIntegralCrystallineReduction.square p X Y f hp I hprojective n) x).trans
    (reduction p X Y f hp I n x)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallGlobalLevel.IntrinsicPadicSmallGlobalLevel
