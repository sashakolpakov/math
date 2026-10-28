import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallFinite
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallLevelFiniteCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallGlobalLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CoefficientReduction

/-! # Finite Reduction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FiniteReduction.IntrinsicPadicGeometricFiniteReduction

noncomputable section

/-! The original finite crystalline comparison preserves the actual
geometric pullback of reduced native de Rham classes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of (ZMod p)))} [IsProper Y₁.hom] [Smooth Y₁.hom] [IsProper Y₂.hom] [Smooth Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂) (n : ℕ)
  (I₁ : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁)))
  (I₂ : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂)))

local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p
local notation "D" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicCoefficientDescent.restrict p
local notation "Iq₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution
  (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁) n I₁
local notation "Iq₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution
  (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂) n I₂

def commonComparison := SmallFinite.IntrinsicPadicGeometricSmallFiniteComparison.commonComparison p u f₁ hp₁ n Iq₁

def sourceIso := SmallGlobalLevel.IntrinsicPadicSmallGlobalLevel.iso p X₁ Y₁ f₁ hp₁ I₁ n
def targetIso := SmallGlobalLevel.IntrinsicPadicSmallGlobalLevel.iso p X₂ Y₂ f₂ hp₂ I₂ n

def pullback := ModuleCat.ofHom (IntegralComparison.BoundedCrystalline.CrystallinePullback.pullback (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) v.left
  (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n 1)

omit [Smooth Y₁.hom] [Smooth Y₂.hom] in
theorem source_coordinates : (sourceIso p f₁ hp₁ n I₁).hom =
    (SmallFinite.IntrinsicPadicGeometricSmallFiniteComparison.sourceIso p f₁ hp₁ n Iq₁).hom :=
  SmallLevelFiniteCoordinates.IntrinsicPadicSmallLevelFiniteCoordinates.homology p X₁ Y₁ f₁ hp₁ I₁ n

omit [Smooth Y₁.hom] [Smooth Y₂.hom] in
theorem target_coordinates : (targetIso p f₂ hp₂ n I₂).hom =
    (SmallFinite.IntrinsicPadicGeometricSmallFiniteComparison.targetIso p f₂ hp₂ n Iq₂).hom :=
  SmallLevelFiniteCoordinates.IntrinsicPadicSmallLevelFiniteCoordinates.homology p X₂ Y₂ f₂ hp₂ I₂ n

omit [Smooth Y₁.hom] [Smooth Y₂.hom] in
theorem source : (sourceIso p f₁ hp₁ n I₁).hom =
    (F).map (QuotientOneCoordinates.IntrinsicPadicGeometricQuotientHOneCoordinates.sourceMap p u n) ≫
      commonComparison p u f₁ hp₁ n I₁ :=
  (source_coordinates p f₁ hp₁ n I₁).trans
    (SmallFinite.IntrinsicPadicGeometricSmallFiniteComparison.source p u f₁ hp₁ n Iq₁)

include hsquare in
omit [Smooth Y₁.hom] [Smooth Y₂.hom] in
theorem target : (targetIso p f₂ hp₂ n I₂).hom ≫ pullback p v n =
    (F).map (QuotientOneCoordinates.IntrinsicPadicGeometricQuotientHOneCoordinates.targetMap p u n) ≫
      (F).map (QuotientOneCoordinates.IntrinsicPadicGeometricQuotientHOneCoordinates.geometricMap p u n) ≫
        commonComparison p u f₁ hp₁ n I₁ :=
  (congrArg (fun a => a ≫ pullback p v n) (target_coordinates p f₂ hp₂ n I₂)).trans
    (SmallFinite.IntrinsicPadicGeometricSmallFiniteComparison.target p u v f₁ f₂ hp₁ hp₂ hsquare n Iq₁ Iq₂)

include hsquare in
omit [Smooth Y₁.hom] [Smooth Y₂.hom] in
theorem naturality (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X₂ 1) :
    (D).map (pullback p v n)
      ((D).map (targetIso p f₂ hp₂ n I₂).hom (CoefficientReduction.IntrinsicPadicGeometricCoefficientReduction.reduction p n X₂ x)) =
    (D).map (sourceIso p f₁ hp₁ n I₁).hom
      (CoefficientReduction.IntrinsicPadicGeometricCoefficientReduction.reduction p n X₁ (DeRham.Int.pullback u 1 x)) := by
  have ht := congrArg (D).map (target p u v f₁ f₂ hp₁ hp₂ hsquare n I₁ I₂)
  erw [Functor.map_comp, Functor.map_comp, Functor.map_comp] at ht
  have hs := congrArg (D).map (source p u f₁ hp₁ n I₁)
  erw [Functor.map_comp] at hs
  exact (ConcreteCategory.congr_hom ht (CoefficientReduction.IntrinsicPadicGeometricCoefficientReduction.reduction p n X₂ x)).trans
    ((congrArg ((D).map (commonComparison p u f₁ hp₁ n I₁))
      (CoefficientReduction.IntrinsicPadicGeometricCoefficientReduction.naturality p u n x)).trans
        (ConcreteCategory.congr_hom hs
          (CoefficientReduction.IntrinsicPadicGeometricCoefficientReduction.reduction p n X₁ (DeRham.Int.pullback u 1 x))).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FiniteReduction.IntrinsicPadicGeometricFiniteReduction
