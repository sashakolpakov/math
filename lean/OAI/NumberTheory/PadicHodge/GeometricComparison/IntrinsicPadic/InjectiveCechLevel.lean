import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveCechGlobal
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveSectionLevelCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplexNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralPresheafLevelData
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionLevelMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.FlasqueCechLevel

/-! # Injective Cech Level -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData

/-! Named actual bicomplex objects, comparison isomorphisms and level maps
for the original native injective Cech/global comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (n m : ℕ) (hnm : n ≤ m)
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y)))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f
local notation "In" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution wittMap n I
local notation "Im" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution wittMap m I
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "special" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X Y f
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U

local instance tuple_preserves (q : ℕ) (t : Fin (q + 1) → Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X) :
    PreservesLimit (Discrete.functor (U ∘ t)) special := by
  dsimp only [SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens]
  infer_instance

abbrev Values := ModuleCat.{2} R

local notation "Iq" => fun q : ℕ => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution wittMap q I

def cechFunctor : CochainComplex (X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R) ℕ ⥤
    HomologicalComplex₂ (ModuleCat.{2} R) (.up ℕ) (.up ℕ) :=
  Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{1, 2} R E

local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.cechFunctor p X
local notation "G" => Functor.mapHomologicalComplex (OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.complexFunctor (A := OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.Values p)
  (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.specialCover p X Y f)) (ComplexShape.up ℕ)
local notation "pull" => Functor.mapHomologicalComplex (OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.Values p) special) (ComplexShape.up ℕ)

def native (q : ℕ) : HomologicalComplex₂ (ModuleCat.{2} R) (.up ℕ) (.up ℕ) :=
  (F).obj (IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.target p X Y f I q)

def pulled (q : ℕ) : HomologicalComplex₂ (ModuleCat.{2} R) (.up ℕ) (.up ℕ) :=
  (F).obj ((pull).obj (IntegralComparison.BoundedOpen.SectionComplex.complex wittMap q (Iq q)))

def opens (q : ℕ) : HomologicalComplex₂ (ModuleCat.{2} R) (.up ℕ) (.up ℕ) :=
  (G).obj (IntegralComparison.BoundedOpen.SectionComplex.complex wittMap q (Iq q))

def target (q : ℕ) : HomologicalComplex₂ (ModuleCat.{2} R) (.up ℕ) (.up ℕ) :=
  FlasqueCechGlobal.FlasqueCechGlobalComparison.bicomplex.{1, 0, 2} R Y.left.carrier
    (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.specialCover p X Y f) (IntegralComparison.BoundedOpen.FlasqueComplex.complex wittMap q (Iq q))

def sourceIso (q : ℕ) : native p X Y f I q ≅ pulled p X Y f I q :=
  (F).mapIso (SectionComplexRestriction.IntrinsicPadicSectionComplexRestriction.comparisonIso p X Y f q (Iq q))

def middleIso (q : ℕ) : pulled p X Y f I q ≅ opens p X Y f I q :=
  NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.iso (A := Values p) special U
    (IntegralComparison.BoundedOpen.SectionComplex.complex wittMap q (Iq q))

def targetIso (q : ℕ) : opens p X Y f I q ≅ target p X Y f I q :=
  (G).mapIso (IntegralComparison.BoundedOpen.FlasqueComplex.underlyingComplexIso wittMap q (Iq q)).symm

def nativeMap : native p X Y f I m ⟶ native p X Y f I n :=
  (F).map (IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.targetMap p X Y f I n m hnm)

def pulledMap : pulled p X Y f I m ⟶ pulled p X Y f I n :=
  (F).map ((pull).map (Bounded.OpenSectionLevel.BoundedOpenSectionLevel.complexMap wittMap n m hnm I))

def opensMap : opens p X Y f I m ⟶ opens p X Y f I n :=
  (G).map (Bounded.OpenSectionLevel.BoundedOpenSectionLevel.complexMap wittMap n m hnm I)

def targetMap : target p X Y f I m ⟶ target p X Y f I n :=
  FlasqueCechTotal.FlasqueCechGlobalNaturality.bicomplexMap.{1, 0, 2} R Y.left.carrier
    (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.specialCover p X Y f) (Bounded.FlasqueCechLevel.BoundedFlasqueCechLevel.complexMap wittMap n m hnm I)

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveCechLevel.IntrinsicPadicInjectiveCechLevel

/-! The original native integral-cover injective Cech comparison respects
the original bounded crystalline level transition. -/

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
  (n m : ℕ) (hnm : n ≤ m)
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y)))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f
local notation "In" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution wittMap n I
local notation "Im" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution wittMap m I
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
  (IntegralComparison.NonemptyCechNerve.complexFunctor (A := IntrinsicPadicInjectiveCechLevelData.Values p)
    (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.specialCover p X Y f)) (ComplexShape.up ℕ)

abbrev sectionsMap := InjectiveSectionLevelCoordinates.IntrinsicPadicInjectiveSectionLevelCoordinates.sectionsMap p X Y f n m hnm I

theorem source_square : IntrinsicPadicInjectiveCechLevelData.nativeMap p X Y f n m hnm I ≫ (IntrinsicPadicInjectiveCechLevelData.sourceIso p X Y f I n).hom =
    (IntrinsicPadicInjectiveCechLevelData.sourceIso p X Y f I m).hom ≫ IntrinsicPadicInjectiveCechLevelData.pulledMap p X Y f n m hnm I :=
  map_square F _ _ _ _ (InjectiveSectionLevelCoordinates.IntrinsicPadicInjectiveSectionLevelCoordinates.source p X Y f n m hnm I)

theorem middle_square : IntrinsicPadicInjectiveCechLevelData.pulledMap p X Y f n m hnm I ≫ (IntrinsicPadicInjectiveCechLevelData.middleIso p X Y f I n).hom =
    (IntrinsicPadicInjectiveCechLevelData.middleIso p X Y f I m).hom ≫ IntrinsicPadicInjectiveCechLevelData.opensMap p X Y f n m hnm I := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact NonemptyCech.ProductBaseChangeNaturality.NonemptyCechProductBaseChangeNaturality.naturality (A := IntrinsicPadicInjectiveCechLevelData.Values p) special U
    ((Bounded.OpenSectionLevel.BoundedOpenSectionLevel.complexMap wittMap n m hnm I).f i)

omit [X.left.IsSeparated] in
theorem target_square : IntrinsicPadicInjectiveCechLevelData.opensMap p X Y f n m hnm I ≫ (IntrinsicPadicInjectiveCechLevelData.targetIso p X Y f I n).hom =
    (IntrinsicPadicInjectiveCechLevelData.targetIso p X Y f I m).hom ≫ IntrinsicPadicInjectiveCechLevelData.targetMap p X Y f n m hnm I := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact map_square (IntegralComparison.NonemptyCechNerve.complexFunctor (A := IntrinsicPadicInjectiveCechLevelData.Values p)
    (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.specialCover p X Y f)) _ _ _ _
      (congrArg (fun q => q.f i) (InjectiveSectionLevelCoordinates.IntrinsicPadicInjectiveSectionLevelCoordinates.target p Y n m hnm I))

def comparisonIso (q : ℕ) : IntrinsicPadicInjectiveCechLevelData.native p X Y f I q ≅ IntrinsicPadicInjectiveCechLevelData.target p X Y f I q :=
  IntrinsicPadicInjectiveCechLevelData.sourceIso p X Y f I q ≪≫ IntrinsicPadicInjectiveCechLevelData.middleIso p X Y f I q ≪≫ IntrinsicPadicInjectiveCechLevelData.targetIso p X Y f I q

theorem named_natural : IntrinsicPadicInjectiveCechLevelData.nativeMap p X Y f n m hnm I ≫
    (IntrinsicPadicInjectiveCechLevelData.sourceIso p X Y f I n ≪≫ IntrinsicPadicInjectiveCechLevelData.middleIso p X Y f I n ≪≫ IntrinsicPadicInjectiveCechLevelData.targetIso p X Y f I n).hom =
    (IntrinsicPadicInjectiveCechLevelData.sourceIso p X Y f I m ≪≫ IntrinsicPadicInjectiveCechLevelData.middleIso p X Y f I m ≪≫ IntrinsicPadicInjectiveCechLevelData.targetIso p X Y f I m).hom ≫
      IntrinsicPadicInjectiveCechLevelData.targetMap p X Y f n m hnm I :=
  three_squares _ _ _ _ _ _ _ _ _ _ (source_square p X Y f n m hnm I)
    (middle_square p X Y f n m hnm I) (target_square p X Y f n m hnm I)

theorem bicomplex_natural : IntrinsicPadicInjectiveCechLevelData.nativeMap p X Y f n m hnm I ≫
    (comparisonIso p X Y f I n).hom =
    (comparisonIso p X Y f I m).hom ≫ IntrinsicPadicInjectiveCechLevelData.targetMap p X Y f n m hnm I :=
  named_natural p X Y f n m hnm I

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveCechLevel.IntrinsicPadicInjectiveCechLevel

end

end OAI
