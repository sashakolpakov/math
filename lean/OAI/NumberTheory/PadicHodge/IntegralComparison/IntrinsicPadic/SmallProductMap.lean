import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.WittTotalProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.ReducedTotalProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.FrameProduct

/-! # Small Product Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SmallProductMap.Intrinsic

noncomputable section

/-! The native finite comparison from the original small ordinary
quotient Čech groups to original bounded crystalline Ext preserves cup. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p)))) (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "IW" => (Ideal.span {(p : W)}) ^ (n+1)
local notation "IZ" => (Ideal.span {(p : ℤ_[p])}) ^ (n+1)
local notation "AW" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X
local notation "AZ" => CategoryTheory.Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left) ⋙
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras ℤ_[p] X
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryQuotientDiagramProduct.Ordinary.complex ℤ_[p] IZ AZ
local notation "ν" => OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryQuotientDiagramProduct.Ordinary.pairing ℤ_[p] IZ AZ
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "M" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.total p X n
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "H" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.frames p X Y f hp n
local instance coefficients : Algebra W ℤ_[p] := GeometricComparison.WittAlgebra.PadicWittAlgebra.coefficientAlgebra p
local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

abbrev sourceCup := OrdinaryQuotientDiagramProduct.Ordinary.cohomologyCup ℤ_[p] IZ AZ U
abbrev wittCup := OrdinaryQuotientDiagramProduct.Ordinary.cohomologyCup W IW AW U

abbrev restrictedCup := Cochain.CohomologyCup.cohomologyCup
  (((ModuleCat.restrictScalars (algebraMap W ℤ_[p])).mapHomologicalComplex (.up ℕ)).obj M)
  (WittTotalProduct.Intrinsic.targetCup p X n)
  (WittTotalProduct.Intrinsic.target_differential p X n)

abbrev restriction (i : ℕ) := RestrictScalarsCochainCup.map W ℤ_[p] M i

abbrev restriction_cup := RestrictScalarsCochainCup.map_cup W ℤ_[p] M
  (Presheaf.TotalCup.CechProduct.totalCup N Q ν) (Presheaf.TotalLeibniz.CechProduct.differential_totalCup N Q ν
    (OrdinaryQuotientDiagramProduct.Ordinary.natural ℤ_[p] IZ AZ)
    (OrdinaryQuotientDiagramProduct.Ordinary.differential ℤ_[p] IZ AZ))

def wittMap (i : ℕ) :=
  (HomologicalComplex.homologyMap (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.wittTotalIso p X n).inv i).hom.toAddMonoidHom.comp (restriction p X n i)

abbrev wittMap_cup (i j : ℕ) (x : (M).homology i) (y : (M).homology j) := by
  have result := (congrArg (HomologicalComplex.homologyMap
      (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.wittTotalIso p X n).inv (i+j))
      (restriction_cup p X n i j x y)).trans
      (WittTotalProduct.Intrinsic.inverse_cohomologyMap_cup p X n i j _ _)
  exact result

def frameMap (i : ℕ) :=
  (HomologicalComplex.homologyMap (ReducedTotalProduct.Intrinsic.totalMap p X Y f hp n) i).hom.toAddMonoidHom.comp (wittMap p X n i)

omit [IsSeparated Y.hom] in
abbrev frameMap_cup (i j : ℕ) (x : (M).homology i) (y : (M).homology j) :=
  (congrArg (HomologicalComplex.homologyMap
    (ReducedTotalProduct.Intrinsic.totalMap p X Y f hp n) (i+j))
    (wittMap_cup p X n i j x y)).trans
    (ReducedTotalProduct.Intrinsic.cohomologyMap_cup p X Y f hp n i j _ _)

def map (i : ℕ) := (FrameProduct.IntrinsicRaw.map p X Y f hp n i).comp
  (frameMap p X Y f hp n i)

abbrev map_cup (i j : ℕ) (x : (M).homology i) (y : (M).homology j) :=
  (congrArg (FrameProduct.IntrinsicRaw.map p X Y f hp n (i+j))
    (frameMap_cup p X Y f hp n i j x y)).trans
    (FrameProduct.IntrinsicRaw.map_cup p X Y f hp n i j _ _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SmallProductMap.Intrinsic
