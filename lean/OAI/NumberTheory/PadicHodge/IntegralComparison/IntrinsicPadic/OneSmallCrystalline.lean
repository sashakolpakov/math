import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.OneCrystalline
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.CrystallineCup

/-! # One Small Crystalline -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.OneSmallCrystalline.IntrinsicH

noncomputable section

/-! The accepted integral degree-one comparison lands in the original
small crystalline groups through their genuine big/small equivalence. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p])))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsProper Y.hom] [Smooth Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (I : InjectiveResolution (BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (Witt.Crystalline.wittStructureMap p (ZMod p) Y)))
  (hprojective : Projectivity.Construction.ProjectiveOver (ZMod p) Y.hom)

local notation "K" => HomologicalComplex₂.total
  (OrdinaryCechUnit.IntrinsicOrdinary.bicomplex p X) (ComplexShape.up ℕ)

def equiv : (K).homology 1 ≃+ Witt.Crystalline.integralCohomology p (ZMod p) Y 1 :=
  (OneCrystalline.IntrinsicH.equiv p X Y f hp I hprojective).toAddEquiv.trans
    (Global.Crystalline.Comparison.integralEquiv p (ZMod p) Y 1).toAddEquiv

theorem equiv_apply (x : (K).homology 1) :
    equiv p X Y f hp I hprojective x =
      Global.Crystalline.Comparison.integralEquiv p (ZMod p) Y 1
        (OneCrystalline.IntrinsicH.equiv p X Y f hp I hprojective x) := rfl

theorem square (n : ℕ) (x : (K).homology 1) :
    Balanced.CrystallineCup.Integral.restriction p (ZMod p) Y n 1
        (equiv p X Y f hp I hprojective x) =
      SmallCohomology.Intrinsic.linearEquiv p X Y f hp I n 1
        (HomologicalComplex.homologyMap (GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.fullOpenIso p X n).inv 1
          (OrdinaryReduction.IntrinsicOrdinary.reduction p X n 1 x)) := by
  change BoundedCrystalline.CrystallineCohomology.restriction
      (Witt.Crystalline.wittStructureMap p (ZMod p) Y) n 1
      ((Global.Crystalline.Comparison.integralEquiv p (ZMod p) Y 1).symm
        (equiv p X Y f hp I hprojective x)) = _
  rw [equiv_apply]
  erw [LinearEquiv.symm_apply_apply]
  exact OneCrystalline.IntrinsicH.square p X Y f hp I hprojective n x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.OneSmallCrystalline.IntrinsicH
