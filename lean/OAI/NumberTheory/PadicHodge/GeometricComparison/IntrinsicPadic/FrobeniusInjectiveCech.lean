import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveCechLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplexNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusInjectiveSectionCoordinates

/-! # Frobenius Injective Cech -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusInjectiveCech.IntrinsicPadicFrobeniusInjectiveCech

noncomputable section

/-! The original native integral-cover injective Cech comparison respects
actual level-zero crystalline Frobenius. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

private theorem map_square {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) {W X Y Z : A} (a : W ⟶ X) (b : X ⟶ Z) (c : W ⟶ Y) (d : Y ⟶ Z)
    (h : a ≫ b = c ≫ d) : F.map a ≫ F.map b = F.map c ≫ F.map d :=
  (F.map_comp a b).symm.trans ((congrArg F.map h).trans (F.map_comp c d))

private theorem three_squares {A : Type*} [Category* A] {W X Y Z W' X' Y' Z' : A}
    (p : W ⟶ W') (q : X ⟶ X') (r : Y ⟶ Y') (s : Z ⟶ Z')
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z)
    (a' : W' ⟶ X') (b' : X' ⟶ Y') (c' : Y' ⟶ Z')
    (h₁ : p ≫ a' = a ≫ q) (h₂ : q ≫ b' = b ≫ r) (h₃ : r ≫ c' = c ≫ s) :
    p ≫ (a' ≫ b' ≫ c') = (a ≫ b ≫ c) ≫ s := by
  have h := ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂
  have h' := ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h h₃
  simpa only [Category.assoc] using h'

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p))))
  (f : Y.left ⟶ X.left)
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y)))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f
local notation "I0" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution wittMap 0 I
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "special" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X Y f
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U

local instance tuple_preserves (q : ℕ) (t : Fin (q + 1) → Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X) :
    PreservesLimit (Discrete.functor (U ∘ t)) special := by
  dsimp only [SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens]
  infer_instance

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData

local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.cechFunctor p X
local notation "G" => Functor.mapHomologicalComplex
  (IntegralComparison.NonemptyCechNerve.complexFunctor (A := InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.Values p)
    (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.specialCover p X Y f)) (ComplexShape.up ℕ)

abbrev sectionsMap := FrobeniusInjectiveSectionCoordinates.IntrinsicPadicFrobeniusInjectiveSectionCoordinates.sectionsMap p X Y f I0

def nativeMap : InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.native p X Y f I 0 ⟶ InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.native p X Y f I 0 :=
  (F).map (sectionsMap p X Y f I)

def pulledMap : InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.pulled p X Y f I 0 ⟶ InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.pulled p X Y f I 0 :=
  (F).map (((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.Values p) special).mapHomologicalComplex (.up ℕ)).map
    (LevelZero.BoundedOpenFrobenius.LevelZeroBoundedOpenFrobenius.map p Y I0))

def opensMap : InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.opens p X Y f I 0 ⟶ InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.opens p X Y f I 0 :=
  (G).map (LevelZero.BoundedOpenFrobenius.LevelZeroBoundedOpenFrobenius.map p Y I0)

def targetMap : InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.target p X Y f I 0 ⟶ InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.target p X Y f I 0 :=
  FlasqueCechTotal.FlasqueCechGlobalNaturality.bicomplexMap.{1, 0, 2} R Y.left.carrier
    (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.specialCover p X Y f) (LevelZero.BoundedOpenFrobenius.LevelZeroBoundedOpenFrobenius.flasqueMap p Y I0)

theorem source_square : nativeMap p X Y f I ≫ (InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.sourceIso p X Y f I 0).hom =
    (InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.sourceIso p X Y f I 0).hom ≫ pulledMap p X Y f I :=
  map_square F _ _ _ _ (FrobeniusInjectiveSectionCoordinates.IntrinsicPadicFrobeniusInjectiveSectionCoordinates.source p X Y f I0)

theorem middle_square : pulledMap p X Y f I ≫ (InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.middleIso p X Y f I 0).hom =
    (InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.middleIso p X Y f I 0).hom ≫ opensMap p X Y f I := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact NonemptyCech.ProductBaseChangeNaturality.NonemptyCechProductBaseChangeNaturality.naturality (A := InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.Values p) special U
    ((LevelZero.BoundedOpenFrobenius.LevelZeroBoundedOpenFrobenius.map p Y I0).f i)

omit [X.left.IsSeparated] in
theorem target_square : opensMap p X Y f I ≫ (InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.targetIso p X Y f I 0).hom =
    (InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.targetIso p X Y f I 0).hom ≫ targetMap p X Y f I := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact map_square (IntegralComparison.NonemptyCechNerve.complexFunctor (A := InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.Values p)
    (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.specialCover p X Y f)) _ _ _ _
      (congrArg (fun q => q.f i) (FrobeniusInjectiveSectionCoordinates.IntrinsicPadicFrobeniusInjectiveSectionCoordinates.target p Y I0))

abbrev comparisonIso := InjectiveCechLevel.IntrinsicPadicInjectiveCechLevel.comparisonIso p X Y f I 0

theorem named_natural : nativeMap p X Y f I ≫
    (InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.sourceIso p X Y f I 0 ≪≫ InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.middleIso p X Y f I 0 ≪≫ InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.targetIso p X Y f I 0).hom =
    (InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.sourceIso p X Y f I 0 ≪≫ InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.middleIso p X Y f I 0 ≪≫ InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.targetIso p X Y f I 0).hom ≫
      targetMap p X Y f I :=
  three_squares _ _ _ _ _ _ _ _ _ _ (source_square p X Y f I)
    (middle_square p X Y f I) (target_square p X Y f I)

theorem bicomplex_natural : nativeMap p X Y f I ≫
    (comparisonIso p X Y f I).hom =
    (comparisonIso p X Y f I).hom ≫ targetMap p X Y f I :=
  named_natural p X Y f I

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusInjectiveCech.IntrinsicPadicFrobeniusInjectiveCech
