import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCoefficientLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient

/-! # Small Coefficient Level -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel

noncomputable section

/-! The coefficient comparison from the small p-adic Cech complex to
the native integral source is natural on the original level maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (n m : ℕ) (hnm : n ≤ m)

local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X)

def target (q : ℕ) := CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.total E
  (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X q)

def iso (q : ℕ) : ((F).mapHomologicalComplex (.up ℕ)).obj (Coefficient.IntrinsicPadicSmallQuotientTotal.total p X q) ≅ target p X q :=
  Coefficient.IntrinsicPadicSmallQuotientTotal.coefficientTotalIso p X q ≪≫
    IntrinsicIntegral.CoefficientTotal.IntrinsicIntegralCoefficientTotal.coefficientIso p X q

theorem natural : ((F).mapHomologicalComplex (.up ℕ)).map (SmallQuotientLevel.IntrinsicPadicSmallQuotientLevel.map p X n m hnm) ≫
    (iso p X n).hom = (iso p X m).hom ≫ IntegralCoefficientLevel.IntrinsicPadicIntegralCoefficientLevel.largeMap p X n m hnm :=
  ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _
    (IntegralCoefficientLevel.IntrinsicPadicIntegralCoefficientLevel.padic p X n m hnm)
    (IntegralCoefficientLevel.IntrinsicPadicIntegralCoefficientLevel.witt p X n m hnm)

def homologyIso (q : ℕ) : (F).obj ((Coefficient.IntrinsicPadicSmallQuotientTotal.total p X q).homology 1) ≅
    (target p X q).homology 1 :=
  ExactHomology.ExactHomologyComparison.iso F (.up ℕ) (Coefficient.IntrinsicPadicSmallQuotientTotal.total p X q) (target p X q) (iso p X q) 1

theorem homology : (F).map (HomologicalComplex.homologyMap (SmallQuotientLevel.IntrinsicPadicSmallQuotientLevel.map p X n m hnm) 1) ≫
    (homologyIso p X n).hom = (homologyIso p X m).hom ≫
      HomologicalComplex.homologyMap (IntegralCoefficientLevel.IntrinsicPadicIntegralCoefficientLevel.largeMap p X n m hnm) 1 :=
  ExactHomology.ExactHomologyComparison.naturality F (.up ℕ) (iso p X m) (iso p X n)
    (SmallQuotientLevel.IntrinsicPadicSmallQuotientLevel.map p X n m hnm) (IntegralCoefficientLevel.IntrinsicPadicIntegralCoefficientLevel.largeMap p X n m hnm)
    (natural p X n m hnm) 1

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallCoefficientLevel.IntrinsicPadicSmallCoefficientLevel
