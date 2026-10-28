import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.RelativeResolution

/-! # Relative Sheaf Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex

noncomputable section

/-!
# IntegralComparison: relative frame complexes in the native bounded crystalline sheaf category
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of B)) (n : ℕ)

def coefficientPresheaves :
    ((BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ ⥤ ModuleCat.{u} B) ⥤
      ((BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ ⥤ ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) :=
  (Functor.whiskeringRight _ _ _).obj (Crystalline.RelativeResolution.coefficientFunctor (B := B))

instance coefficientPresheaves_additive :
    (coefficientPresheaves (p := p) (J := J) (δ := δ) f n).Additive where
  map_add := by intros; rfl

instance coefficientPresheaves_preservesFiniteLimits :
    PreservesFiniteLimits (coefficientPresheaves (p := p) (J := J) (δ := δ) f n) where
  preservesFiniteLimits T _ _ := by
    dsimp [coefficientPresheaves]
    infer_instance

instance coefficientPresheaves_preservesFiniteColimits :
    PreservesFiniteColimits (coefficientPresheaves (p := p) (J := J) (δ := δ) f n) where
  preservesFiniteColimits T _ _ := by
    dsimp [coefficientPresheaves]
    infer_instance

instance coefficientPresheaves_preservesHomology :
    (coefficientPresheaves (p := p) (J := J) (δ := δ) f n).PreservesHomology := by
  infer_instance

def sheafification :
    ((BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ ⥤ ModuleCat.{u} B) ⥤
      BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n :=
  coefficientPresheaves f n ⋙ presheafToSheaf (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))

instance sheafification_additive : (sheafification (p := p) (J := J) (δ := δ) f n).Additive := by
  dsimp only [sheafification]
  infer_instance

instance sheafification_preservesFiniteLimits :
    PreservesFiniteLimits (sheafification (p := p) (J := J) (δ := δ) f n) where
  preservesFiniteLimits T _ _ := by
    dsimp only [sheafification]
    infer_instance

instance sheafification_preservesFiniteColimits :
    PreservesFiniteColimits (sheafification (p := p) (J := J) (δ := δ) f n) where
  preservesFiniteColimits T _ _ := by
    dsimp only [sheafification]
    infer_instance

instance sheafification_preservesHomology :
    (sheafification (p := p) (J := J) (δ := δ) f n).PreservesHomology := by
  infer_instance

local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := J) (δ := δ) f n
local notation "A" => Functor.op (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n) ⋙ OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf f
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f n

def structureIso : (S).obj A ≅ O :=
  ((BoundedCrystalline.Site.inclusion f n).pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) (BoundedCrystalline.Site.topology f n) BigCrystallineSite.Object.topology).app
      (BigCrystallineCohomology.largePresheaf f)

variable [Fact p.Prime] [IsSeparated f] (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

def complex : CochainComplex (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n) ℕ :=
  ((S).mapHomologicalComplex (ComplexShape.up ℕ)).obj (BoundedFrame.Diagram.complex F)

def sourceIso :
    ((S).mapHomologicalComplex (ComplexShape.up ℕ)).obj ((CochainComplex.single₀ _).obj A) ≅
      (CochainComplex.single₀ _).obj O :=
  (HomologicalComplex.singleMapHomologicalComplex S (ComplexShape.up ℕ) 0).app A ≪≫
    (CochainComplex.single₀ _).mapIso (structureIso f n)

def augmentation : (CochainComplex.single₀ _).obj O ⟶ complex f n F :=
  (sourceIso f n).inv ≫ ((S).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (BoundedFrame.Diagram.augmentation F)

theorem augmentation_quasiIso [QuasiIso (BoundedFrame.Diagram.augmentation F)] :
    QuasiIso (augmentation f n F) := by
  exact inferInstanceAs (QuasiIso ((sourceIso f n).inv ≫
    ((S).mapHomologicalComplex (ComplexShape.up ℕ)).map (BoundedFrame.Diagram.augmentation F)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex
