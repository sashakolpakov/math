import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedBaseLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.CoefficientNaturality

/-! # Small Quotient Level -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallQuotientLevel.IntrinsicPadicSmallQuotientLevel

noncomputable section

/-! Actual p-adic quotient diagrams and their original Witt-coordinate
isomorphisms form compatible finite-level Cech total maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (n m : ℕ) (hnm : n ≤ m)

local notation "W" => WittVector p (ZMod p)
local notation "G" => ModuleCat.restrictScalars (RingEquiv.toRingHom (WittVector.equiv p))
local notation "IZ" => fun q : ℕ => (Ideal.span {(p : ℤ_[p])}) ^ (q + 1)
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U

def diagramMap : Coefficient.IntrinsicPadicSmallQuotientTotal.diagram p X m ⟶ Coefficient.IntrinsicPadicSmallQuotientTotal.diagram p X n :=
  Functor.whiskerLeft ((Affine.OpenProducts.AffineOpenProducts.inclusion X.left).op ⋙ OrdinarySection.OrdinarySectionComplexAssembly.diagram ℤ_[p] X)
    ((IntegralComparison.Module.IdealQuotientTransition.transformation ℤ_[p] (IZ m) (IZ n)
      (Ideal.pow_le_pow_right (Nat.add_le_add_right hnm 1))).mapHomologicalComplex (.up ℕ))

omit [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] in
theorem diagram_natural : (Coefficient.IntrinsicPadicSmallQuotientTotal.wittIso p X m).hom ≫
    Functor.whiskerRight (diagramMap p X n m hnm) ((G).mapHomologicalComplex (.up ℕ)) =
    ReducedDeRhamLevelMap.IntrinsicPadicReducedDeRhamLevelMap.sourceTransition p X n m hnm ≫
      (Coefficient.IntrinsicPadicSmallQuotientTotal.wittIso p X n).hom :=
  ReducedBaseLevel.IntrinsicPadicReducedBaseLevel.natural p X n m hnm

def wittMap : IntrinsicIntegral.CoefficientTotal.IntrinsicIntegralCoefficientTotal.total p X m ⟶ IntrinsicIntegral.CoefficientTotal.IntrinsicIntegralCoefficientTotal.total p X n :=
  (CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor E).map (ReducedDeRhamLevelMap.IntrinsicPadicReducedDeRhamLevelMap.sourceTransition p X n m hnm)

def map : Coefficient.IntrinsicPadicSmallQuotientTotal.total p X m ⟶ Coefficient.IntrinsicPadicSmallQuotientTotal.total p X n :=
  (CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor E).map (diagramMap p X n m hnm)

theorem mapped_diagram : (CechAssembly.Iso.CechAssemblyIso.totalIso E (Coefficient.IntrinsicPadicSmallQuotientTotal.wittIso p X m)).hom ≫
    (CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor E).map (Functor.whiskerRight (diagramMap p X n m hnm) ((G).mapHomologicalComplex (.up ℕ))) =
      wittMap p X n m hnm ≫ (CechAssembly.Iso.CechAssemblyIso.totalIso E (Coefficient.IntrinsicPadicSmallQuotientTotal.wittIso p X n)).hom := by
  let T := CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor (A := ModuleCat.{0} W) E
  exact (T.map_comp _ _).symm.trans
    ((congrArg T.map (diagram_natural p X n m hnm)).trans (T.map_comp _ _))

theorem inverse_coefficient :
    (CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso G E (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U)
      (Coefficient.IntrinsicPadicSmallQuotientTotal.diagram p X m)).inv ≫
        ((G).mapHomologicalComplex (.up ℕ)).map (IntrinsicPadicSmallQuotientLevel.map p X n m hnm) =
    (CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor E).map (Functor.whiskerRight (diagramMap p X n m hnm) ((G).mapHomologicalComplex (.up ℕ))) ≫
      (CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso G E (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U)
        (Coefficient.IntrinsicPadicSmallQuotientTotal.diagram p X n)).inv :=
  (IntegralComparison.InverseCoordinateHomology.inverse
    (CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso G E (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) (Coefficient.IntrinsicPadicSmallQuotientTotal.diagram p X m))
    (CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso G E (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) (Coefficient.IntrinsicPadicSmallQuotientTotal.diagram p X n))
    (((G).mapHomologicalComplex (.up ℕ)).map (IntrinsicPadicSmallQuotientLevel.map p X n m hnm))
    ((CechAssembly.TotalFunctor.CechAssemblyTotalFunctor.functor E).map (Functor.whiskerRight (diagramMap p X n m hnm) ((G).mapHomologicalComplex (.up ℕ))))
    (CechAssembly.CoefficientNaturality.CechAssemblyCoefficientNaturality.natural G E (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U) (diagramMap p X n m hnm))).symm

theorem natural : (Coefficient.IntrinsicPadicSmallQuotientTotal.wittTotalIso p X m).hom ≫
    ((G).mapHomologicalComplex (.up ℕ)).map (IntrinsicPadicSmallQuotientLevel.map p X n m hnm) =
      wittMap p X n m hnm ≫ (Coefficient.IntrinsicPadicSmallQuotientTotal.wittTotalIso p X n).hom :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun q => (CechAssembly.Iso.CechAssemblyIso.totalIso E (Coefficient.IntrinsicPadicSmallQuotientTotal.wittIso p X m)).hom ≫ q)
      (inverse_coefficient p X n m hnm)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun q => q ≫ (CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso G E (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices U)
            (Coefficient.IntrinsicPadicSmallQuotientTotal.diagram p X n)).inv) (mapped_diagram p X n m hnm)).trans
              (Category.assoc _ _ _))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallQuotientLevel.IntrinsicPadicSmallQuotientLevel
