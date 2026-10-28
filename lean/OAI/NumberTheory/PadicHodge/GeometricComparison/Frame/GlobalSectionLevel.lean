import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenSectionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FramePulledMap

/-! # Global Section Level -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.GlobalSectionLevel.FrameGlobalSectionLevel

noncomputable section

/-! The original global frame section maps respect an actual morphism
between bounded crystalline frames at two levels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

private theorem composeSquares {C : Type*} [Category* C] {A B D E F G H : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : A ⟶ F) (e : F ⟶ D)
    (f : F ⟶ G) (g : G ⟶ E) (l : A ⟶ H) (j : H ⟶ G)
    (h₁ : a ≫ b = d ≫ e) (h₂ : e ≫ c = f ≫ g) (h₃ : d ≫ f = l ≫ j) :
    a ≫ b ≫ c = l ≫ j ≫ g := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc, h₃, Category.assoc]

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction
universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of B)) [IsSeparated f]
  (n m : ℕ) (hnm : n ≤ m)
  {Fn : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n}
  {Fm : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f m}
  (a : (IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm).obj Fn ⟶ Fm)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p) (J := J) (δ := δ) f n m hnm
local notation "Kn" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex f n Fn
local notation "Km" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex f m Fm
local notation "b" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameMap.map f n m hnm a

def restriction : Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.globalSections (p := p) (J := J) (δ := δ) f m ⟶
    T ⋙ Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.globalSections f n :=
  IntegralComparison.Sheaf.PresheafSectionRestriction.map G R (IntegralComparison.BoundedCrystalline.Site.topology f n) (IntegralComparison.BoundedCrystalline.Site.topology f m)

theorem restriction_stage : IntegralComparison.ConstantSection.ComplexRestriction.sectionMap.{u + 1, u, u + 2} R (IntegralComparison.BoundedCrystalline.Site.topology f m)
    (IntegralComparison.BoundedFrame.DeRhamSections.frameComplex f m Fm) Km
      (IntegralComparison.BoundedFrame.DeRhamSections.sheafMap f m Fm) ≫
        ((restriction f n m hnm).mapHomologicalComplex (.up ℕ)).app Km =
    IntegralComparison.ConstantSection.ComplexMap.map.{u + 1, u, u + 1, u + 2} R (IntegralComparison.BoundedCrystalline.Site.topology f n)
      (IntegralComparison.BoundedFrame.DeRhamSections.frameComplex f m Fm) _
        (IntegralComparison.BoundedLevel.FramePulledMap.map f n m hnm (FY := Fm)) ≫
          (IntegralComparison.Sheaf.PresheafSectionComplex.complexIso.{u + 1, u, u + 1, u + 2} R (IntegralComparison.BoundedCrystalline.Site.topology f n)
            (((T).mapHomologicalComplex (.up ℕ)).obj Km)).hom :=
  IntegralComparison.ConstantSection.ComplexRestriction.naturality.{u + 1, u, u + 2} G R (IntegralComparison.BoundedCrystalline.Site.topology f n) (IntegralComparison.BoundedCrystalline.Site.topology f m)
    (IntegralComparison.BoundedFrame.DeRhamSections.frameComplex f m Fm) Km
      (IntegralComparison.BoundedFrame.DeRhamSections.sheafMap f m Fm)

theorem ext_component (i : ℕ) :
    ((IntegralComparison.Ext.ZeroPresheafSections.iso.{u + 1, u, u + 1, u + 2} R (IntegralComparison.BoundedCrystalline.Site.topology f n)).app ((T).obj ((Km).X i))).hom ≫
      (Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.globalSections f n).map ((b).f i) =
    (IntegralComparison.Ext.ModuleFunctor.functor R (IntegralComparison.BoundedCrystalline.CrystallineCohomology.constantUnit f n) 0).map ((b).f i) ≫
      ((IntegralComparison.Ext.ZeroPresheafSections.iso.{u + 1, u, u + 1, u + 2} R (IntegralComparison.BoundedCrystalline.Site.topology f n)).app ((Kn).X i)).hom :=
  ((IntegralComparison.Ext.ZeroPresheafSections.iso.{u + 1, u, u + 1, u + 2} R (IntegralComparison.BoundedCrystalline.Site.topology f n)).hom.naturality ((b).f i)).symm

theorem sectionMap : IntegralComparison.ConstantSection.ComplexRestriction.sectionMap.{u + 1, u, u + 2} R (IntegralComparison.BoundedCrystalline.Site.topology f m)
    (IntegralComparison.BoundedFrame.DeRhamSections.frameComplex f m Fm) Km
      (IntegralComparison.BoundedFrame.DeRhamSections.sheafMap f m Fm) ≫
        ((restriction f n m hnm).mapHomologicalComplex (.up ℕ)).app Km ≫
          ((Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.globalSections f n).mapHomologicalComplex (.up ℕ)).map b =
    ((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)).map
      (IntegralComparison.BoundedFrame.SectionChange.frameMap a) ≫
        IntegralComparison.ConstantSection.ComplexRestriction.sectionMap.{u + 1, u, u + 2} R (IntegralComparison.BoundedCrystalline.Site.topology f n)
          (IntegralComparison.BoundedFrame.DeRhamSections.frameComplex f n Fn) Kn
            (IntegralComparison.BoundedFrame.DeRhamSections.sheafMap f n Fn) := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact composeSquares _ _ _ _ _ _ _ _ _
    (congrArg (fun q => q.f i) (restriction_stage f n m hnm (Fm := Fm)))
    (ext_component f n m hnm a i) (IntegralComparison.BoundedLevel.FramePulledMap.sections_component f n m hnm a i)

theorem natural : (OpenSectionNaturality.FrameOpenSectionNaturality.globalTransformation f m).app (op Fm) ≫
    ((restriction f n m hnm).mapHomologicalComplex (.up ℕ)).app Km ≫
      ((Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.globalSections f n).mapHomologicalComplex (.up ℕ)).map b =
    ((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)).map
      (IntegralComparison.BoundedFrame.SectionChange.frameMap a) ≫
        (OpenSectionNaturality.FrameOpenSectionNaturality.globalTransformation f n).app (op Fn) := by
  rw [OpenSectionCoordinates.FrameOpenSectionCoordinates.global_app, OpenSectionCoordinates.FrameOpenSectionCoordinates.global_app]
  exact sectionMap f n m hnm a

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.GlobalSectionLevel.FrameGlobalSectionLevel
