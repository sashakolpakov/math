import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallCoefficientLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FirstThreeSourceLevel

/-! # Principal Coefficient Level -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalCoefficientLevel.IntrinsicPadicPrincipalCoefficientLevel

noncomputable section

/-! The native integral source H-one is naturally the coefficient
transport of the original principal-quotient H-one tower. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (n m : ℕ) (hnm : n ≤ m)

local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X
local notation "C" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.complex ℤ_[p] X U

def source (q : ℕ) := (F).obj ((PrincipalCochainExact.PrincipalCochainQuotient.quotient ℤ_[p] C (p : ℤ_[p]) (q + 1)).homology 1)

def sourceMap : source p X m ⟶ source p X n :=
  (F).map (HomologicalComplex.homologyMap (FirstThreeSourceLevel.IntrinsicPadicFirstThreeSourceLevel.principalMap p X n m hnm) 1)

theorem inverse_source : HomologicalComplex.homologyMap (FirstThreeSourceLevel.IntrinsicPadicFirstThreeSourceLevel.principalMap p X n m hnm) 1 ≫
    (FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline.sourceHomologyIso p X n).inv =
    (FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline.sourceHomologyIso p X m).inv ≫
      HomologicalComplex.homologyMap (SmallQuotientLevel.IntrinsicPadicSmallQuotientLevel.map p X n m hnm) 1 :=
  IntegralComparison.InverseCoordinateHomology.inverse (FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline.sourceHomologyIso p X m)
    (FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline.sourceHomologyIso p X n)
    (HomologicalComplex.homologyMap (SmallQuotientLevel.IntrinsicPadicSmallQuotientLevel.map p X n m hnm) 1)
    (HomologicalComplex.homologyMap (FirstThreeSourceLevel.IntrinsicPadicFirstThreeSourceLevel.principalMap p X n m hnm) 1)
    (FirstThreeSourceLevel.IntrinsicPadicFirstThreeSourceLevel.natural p X n m hnm)

theorem mapped_inverse_source : sourceMap p X n m hnm ≫
    (F).map (FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline.sourceHomologyIso p X n).inv =
    (F).map (FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline.sourceHomologyIso p X m).inv ≫
      (F).map (HomologicalComplex.homologyMap (SmallQuotientLevel.IntrinsicPadicSmallQuotientLevel.map p X n m hnm) 1) :=
  ((F).map_comp (HomologicalComplex.homologyMap (FirstThreeSourceLevel.IntrinsicPadicFirstThreeSourceLevel.principalMap p X n m hnm) 1)
    (FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline.sourceHomologyIso p X n).inv).symm.trans
      ((congrArg (F).map (inverse_source p X n m hnm)).trans
        ((F).map_comp (FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline.sourceHomologyIso p X m).inv
          (HomologicalComplex.homologyMap (SmallQuotientLevel.IntrinsicPadicSmallQuotientLevel.map p X n m hnm) 1)))

def iso (q : ℕ) : source p X q ≅ (SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.target p X q).homology 1 :=
  (F).mapIso (FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline.sourceHomologyIso p X q).symm ≪≫
    SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.homologyIso p X q

theorem natural : sourceMap p X n m hnm ≫ (iso p X n).hom =
    (iso p X m).hom ≫ HomologicalComplex.homologyMap (IntegralCoefficientLevel.IntrinsicPadicIntegralCoefficientLevel.largeMap p X n m hnm) 1 :=
  ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ (mapped_inverse_source p X n m hnm)
    (SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel.homology p X n m hnm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalCoefficientLevel.IntrinsicPadicPrincipalCoefficientLevel
