import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SmallProductMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineQuotientInverseProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.OrdinaryReductionProduct

/-! # Reduction Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.ReductionProduct.Intrinsic

noncomputable section

/-! Literal coefficient reduction of the original full ordinary Čech
complex followed by its genuine finite crystalline product comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p)))) (n : ℕ)

local instance separated : IsSeparated (Witt.Crystalline.wittStructureMap p (ZMod p) Y) := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "I" => (Ideal.span {(p : ℤ_[p])}) ^ (n+1)
local notation "M" => HomologicalComplex₂.total
  (GeometricComparison.IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.bicomplex ℤ_[p] X
    (fun i => Subtype.val (U i)) I) (ComplexShape.up ℕ)
local notation "K" => HomologicalComplex₂.total
  (OrdinaryCechUnit.IntrinsicOrdinary.bicomplex p X) (ComplexShape.up ℕ)

def comparison (i : ℕ) := (SmallProductMap.Intrinsic.map p X Y f hp n i).comp
  (HomologicalComplex.homologyMap (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.fullOpenIso p X n).inv i).hom.toAddMonoidHom

attribute [local irreducible] Cochain.CohomologyCup.cohomologyCup

abbrev comparison_cup (i j : ℕ) (x : (M).homology i) (y : (M).homology j) := by
  have result := (congrArg (SmallProductMap.Intrinsic.map p X Y f hp n (i+j))
    (AffineQuotientInverseProduct.Ordinary.cohomologyMap_cup ℤ_[p] X U I i j x y)).trans
    (SmallProductMap.Intrinsic.map_cup p X Y f hp n i j _ _)
  exact result

def reductionComparison (i : ℕ) := (comparison p X Y f hp n i).comp
  (OrdinaryReduction.IntrinsicOrdinary.reduction p X n i).toAddMonoidHom

abbrev reductionComparison_cup (i j : ℕ) (x : (K).homology i) (y : (K).homology j) := by
  have result := (congrArg (comparison p X Y f hp n (i+j))
    (OrdinaryReductionProduct.IntrinsicOrdinary.reduction_cup p X n i j x y)).trans
    (comparison_cup p X Y f hp n i j _ _)
  exact result

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.ReductionProduct.Intrinsic
