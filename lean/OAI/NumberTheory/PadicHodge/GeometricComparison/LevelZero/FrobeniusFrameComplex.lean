import OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameComplexFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrameFrobeniusForms

/-! # Frobenius Frame Complex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrobeniusFrameComplex.LevelZeroFrobeniusFrameComplex

noncomputable section

/-! Actual level-zero frame Frobenius is a natural endomorphism of
the original divided-power frame-complex functor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime] (Y : Over (Spec (CommRingCat.of (ZMod p))))

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "G" => OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.postcompose p Y
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameComplexFunctor.CrystallineFrameComplexFunctor.bounded (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w 0

def postcomposeIso : (G).op ⋙ S ≅ S :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro U V a
    simp only [Iso.refl_hom]
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    rfl)

def pulled : S ⟶ (G).op ⋙ S :=
  (Functor.leftUnitor S).inv ≫
    Functor.whiskerRight (NatTrans.op (CrystallineFrobenius.LevelZeroCrystallineFrobenius.transformation p Y)) S

def transformation : S ⟶ S := pulled p Y ≫ (postcomposeIso p Y).hom

theorem positive (U : IntegralComparison.BoundedCrystalline.Site.Objects (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) 0) (n : ℕ) (hn : 0 < n) :
    ((transformation p Y).app (op U)).f n = 0 := by
  change (𝟙 _ ≫ ((S).map (X := op U) (Y := op ((G).obj U))
    (CrystallineFrobenius.LevelZeroCrystallineFrobenius.map p Y U).op) ≫ 𝟙 _).f n = 0
  rw [Category.id_comp, Category.comp_id]
  exact FrameFrobeniusForms.LevelZeroFrameFrobeniusForms.positive p Y U n hn

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrobeniusFrameComplex.LevelZeroFrobeniusFrameComplex
