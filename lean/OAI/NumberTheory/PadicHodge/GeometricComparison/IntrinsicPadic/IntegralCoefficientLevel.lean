import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallQuotientLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralSourceAssemblyLevel

/-! # Integral Coefficient Level -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCoefficientLevel.IntrinsicPadicIntegralCoefficientLevel

noncomputable section

/-! The original finite-level total coefficient isomorphisms respect
both integral Witt and small p-adic quotient transitions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (n m : ℕ) (hnm : n ≤ m)

local notation "W" => WittVector p (ZMod p)
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.coefficients p
local notation "G" => ModuleCat.restrictScalars (RingEquiv.toRingHom (WittVector.equiv p))
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U

def largeMap : CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.total E (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X m) ⟶
    CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.total E (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X n) :=
  Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} R E (IntegralSourceAssemblyLevel.IntrinsicPadicIntegralSourceAssemblyLevel.map p X n m hnm)

theorem witt : ((F).mapHomologicalComplex (.up ℕ)).map (SmallQuotientLevel.IntrinsicPadicSmallQuotientLevel.wittMap p X n m hnm) ≫
    (IntrinsicIntegral.CoefficientTotal.IntrinsicIntegralCoefficientTotal.coefficientIso p X n).hom =
      (IntrinsicIntegral.CoefficientTotal.IntrinsicIntegralCoefficientTotal.coefficientIso p X m).hom ≫ largeMap p X n m hnm :=
  CechAssembly.CoefficientNaturality.CechAssemblyCoefficientNaturality.natural F E (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U)
    (ReducedDeRhamLevelMap.IntrinsicPadicReducedDeRhamLevelMap.sourceTransition p X n m hnm)

theorem inverse_witt : ((G).mapHomologicalComplex (.up ℕ)).map (SmallQuotientLevel.IntrinsicPadicSmallQuotientLevel.map p X n m hnm) ≫
    (Coefficient.IntrinsicPadicSmallQuotientTotal.wittTotalIso p X n).inv =
      (Coefficient.IntrinsicPadicSmallQuotientTotal.wittTotalIso p X m).inv ≫ SmallQuotientLevel.IntrinsicPadicSmallQuotientLevel.wittMap p X n m hnm :=
  IntegralComparison.InverseCoordinateHomology.inverse (Coefficient.IntrinsicPadicSmallQuotientTotal.wittTotalIso p X m)
    (Coefficient.IntrinsicPadicSmallQuotientTotal.wittTotalIso p X n)
    (SmallQuotientLevel.IntrinsicPadicSmallQuotientLevel.wittMap p X n m hnm)
    (((G).mapHomologicalComplex (.up ℕ)).map (SmallQuotientLevel.IntrinsicPadicSmallQuotientLevel.map p X n m hnm))
    (SmallQuotientLevel.IntrinsicPadicSmallQuotientLevel.natural p X n m hnm).symm

theorem padic : ((Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p).mapHomologicalComplex (.up ℕ)).map
    (SmallQuotientLevel.IntrinsicPadicSmallQuotientLevel.map p X n m hnm) ≫ (Coefficient.IntrinsicPadicSmallQuotientTotal.coefficientTotalIso p X n).hom =
      (Coefficient.IntrinsicPadicSmallQuotientTotal.coefficientTotalIso p X m).hom ≫
        ((F).mapHomologicalComplex (.up ℕ)).map (SmallQuotientLevel.IntrinsicPadicSmallQuotientLevel.wittMap p X n m hnm) := by
  let T := (F).mapHomologicalComplex (.up ℕ)
  exact (T.map_comp
    (((G).mapHomologicalComplex (.up ℕ)).map (SmallQuotientLevel.IntrinsicPadicSmallQuotientLevel.map p X n m hnm))
    (Coefficient.IntrinsicPadicSmallQuotientTotal.wittTotalIso p X n).inv).symm.trans
      ((congrArg T.map (inverse_witt p X n m hnm)).trans
        (T.map_comp (Coefficient.IntrinsicPadicSmallQuotientTotal.wittTotalIso p X m).inv
          (SmallQuotientLevel.IntrinsicPadicSmallQuotientLevel.wittMap p X n m hnm)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCoefficientLevel.IntrinsicPadicIntegralCoefficientLevel
