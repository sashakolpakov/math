import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.ReducedBaseProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryQuotientDiagramProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.RestrictScalarsPresheafCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution

/-! # Reduced Base Total Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.ReducedBaseTotalProduct.Intrinsic

noncomputable section

/-! The actual Witt-to-p-adic coefficient isomorphism preserves the
finite ordinary Čech cohomology product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "IW" => (Ideal.span {(p : W)}) ^ (n+1)
local notation "IZ" => (Ideal.span {(p : ℤ_[p])}) ^ (n+1)
local notation "AW" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X
local notation "AZ" => CategoryTheory.Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left) ⋙
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras ℤ_[p] X
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryQuotientDiagramProduct.Ordinary.complex W IW AW
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryQuotientDiagramProduct.Ordinary.complex ℤ_[p] IZ AZ
local notation "μ" => OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryQuotientDiagramProduct.Ordinary.pairing W IW AW
local notation "ν" => OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryQuotientDiagramProduct.Ordinary.pairing ℤ_[p] IZ AZ
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X)
local instance coefficients : Algebra W ℤ_[p] := GeometricComparison.WittAlgebra.PadicWittAlgebra.coefficientAlgebra p

def map := Cech.ComplexDiagramNaturality.Coordinates.complexMap
  (GeometricComparison.IntrinsicPadic.IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.iso p X n).hom

abbrev pairing := RestrictScalarsPresheafCup.pairing W ℤ_[p] Q ν

omit [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] in
theorem map_pairing (i j : ℕ) (U : X.left.affineOpensᵒᵖ)
    (x : ((P).X i).obj U) (y : ((P).X j).obj U) :
    ((map p X n).f (i+j)).app U (μ i j U x y) =
      pairing p X n i j U (((map p X n).f i).app U x) (((map p X n).f j).app U y) :=
  ReducedBaseProduct.Intrinsic.map_wedge p X n U i j x y

abbrev totalMap := Presheaf.CechProductNaturality.totalMap N (map p X n)

abbrev cohomologyMap_cup := Presheaf.CohomologyProduct.Cech.totalMap_cohomologyCup N P μ
  (OrdinaryQuotientDiagramProduct.Ordinary.natural W IW AW)
  (OrdinaryQuotientDiagramProduct.Ordinary.differential W IW AW)
  (GeometricComparison.CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.mappedComplex (ModuleCat.restrictScalars (algebraMap W ℤ_[p])) Q)
  (pairing p X n)
  (RestrictScalarsPresheafCup.natural W ℤ_[p] Q ν
    (OrdinaryQuotientDiagramProduct.Ordinary.natural ℤ_[p] IZ AZ))
  (RestrictScalarsPresheafCup.differential W ℤ_[p] Q ν
    (OrdinaryQuotientDiagramProduct.Ordinary.differential ℤ_[p] IZ AZ))
  (map p X n) (map_pairing p X n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.ReducedBaseTotalProduct.Intrinsic
