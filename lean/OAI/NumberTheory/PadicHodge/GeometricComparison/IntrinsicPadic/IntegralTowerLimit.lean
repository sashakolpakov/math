import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalTower
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechLimit
import OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientLimitCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCechCoordinates

/-! # Integral Tower Limit -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralTowerLimit.IntrinsicPadicIntegralTowerLimit

noncomputable section

/-! Completed integral de Rham H-one is the inverse limit of the
original bounded crystalline Ext tower, with original reduction coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y)))

local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.complex ℤ_[p] X U
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.CochainQuotientLimit.PrincipalCochainQuotient.shiftedDiagram ℤ_[p] K (p : ℤ_[p]) 1
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalTower.IntrinsicPadicPrincipalTower.targetDiagram p Y

local instance padic_complete : IsAdicComplete (Ideal.span {(p : ℤ_[p])}) ℤ_[p] := by
  rw [← PadicInt.maximalIdeal_eq_span_p]
  infer_instance

def sourceIso : (K).homology 1 ≅ limit P :=
  IntegralFirst.ThreeCechLimit.IntegralFirstThreeCechLimit.iso ℤ_[p] X U
    (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.affine ℤ_[p] X) (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.cover ℤ_[p] X)
    (p : ℤ_[p]) (IsRegular.of_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) 1 le_rfl

def iso : (F).obj ((K).homology 1) ≅ limit Q :=
  CoefficientLimit.IntrinsicPadicCoefficientLimitComparison.sourceIso p P Q
    (PrincipalTower.IntrinsicPadicPrincipalTower.diagramIso p X Y f hp I) (sourceIso p X)

theorem iso_π (n : ℕ) : (iso p X Y f hp I).hom ≫ limit.π Q (op n) =
    (F).map (ModuleCat.ofHom (CochainQuotientCohomology.PrincipalCochainQuotient.reduction ℤ_[p] K (p : ℤ_[p]) (n + 1) 1)) ≫
      (PrincipalGlobalLevel.IntrinsicPadicPrincipalGlobalLevel.iso p X Y f hp I n).hom :=
  (CoefficientLimit.IntrinsicPadicCoefficientLimitComparison.sourceIso_hom_π p P Q
    (PrincipalTower.IntrinsicPadicPrincipalTower.diagramIso p X Y f hp I)
    (sourceIso p X) (op n)).trans
      (congrArg (fun a => (F).map a ≫ (PrincipalGlobalLevel.IntrinsicPadicPrincipalGlobalLevel.iso p X Y f hp I n).hom)
        (IntegralFirst.ThreeCechLimit.IntegralFirstThreeCechLimitCoordinates.hom_π ℤ_[p] X U
          (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.affine ℤ_[p] X) (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.cover ℤ_[p] X)
          (p : ℤ_[p]) (IsRegular.of_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) 1 le_rfl n))

def nativeEquiv : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1 ≃ₗ[ℤ_[p]]
    (Coefficient.IntrinsicPadicCoefficientDescent.restrict p).obj (limit Q) :=
  (IntegralCechCoordinates.IntrinsicPadicIntegralCechCoordinates.equiv p X).trans
    ((Coefficient.IntrinsicPadicCoefficientDescent.equiv p ((K).homology 1)).trans
      (((Coefficient.IntrinsicPadicCoefficientDescent.restrict p).mapIso (iso p X Y f hp I)).toLinearEquiv))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralTowerLimit.IntrinsicPadicIntegralTowerLimit
