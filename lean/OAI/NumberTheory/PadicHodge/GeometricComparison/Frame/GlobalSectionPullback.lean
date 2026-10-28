import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenSectionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.FramePulledMap

/-! # Global Section Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.GlobalSectionPullback.FrameGlobalSectionPullback

noncomputable section

/-! The original global frame section maps respect arbitrary geometric pullback
and an actual compatible crystalline frame morphism. -/

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
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated fX] [IsSeparated fY] (g : X ⟶ Y) (hg : g ≫ fY = fX) (n : ℕ)
  {FX : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fX n}
  {FY : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n}
  (a : (IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n).obj FX ⟶ FY)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n
local notation "Kn" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex fX n FX
local notation "Km" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex fY n FY
local notation "b" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.FrameGeometricMap.map g hg n a

def restriction : Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.globalSections (p := p) (J := J) (δ := δ) fY n ⟶
    T ⋙ Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.globalSections fX n :=
  IntegralComparison.Sheaf.PresheafSectionRestriction.map G R (IntegralComparison.BoundedCrystalline.Site.topology fX n) (IntegralComparison.BoundedCrystalline.Site.topology fY n)

omit [IsSeparated fX] in
theorem restriction_stage : IntegralComparison.ConstantSection.ComplexRestriction.sectionMap.{u + 1, u, u + 2} R (IntegralComparison.BoundedCrystalline.Site.topology fY n)
    (IntegralComparison.BoundedFrame.DeRhamSections.frameComplex fY n FY) Km
      (IntegralComparison.BoundedFrame.DeRhamSections.sheafMap fY n FY) ≫
        ((restriction g hg n).mapHomologicalComplex (.up ℕ)).app Km =
    IntegralComparison.ConstantSection.ComplexMap.map.{u + 1, u, u + 1, u + 2} R (IntegralComparison.BoundedCrystalline.Site.topology fX n)
      (IntegralComparison.BoundedFrame.DeRhamSections.frameComplex fY n FY) _
        (IntegralComparison.BoundedGeneral.FramePulledMap.map g hg n (FY := FY)) ≫
          (IntegralComparison.Sheaf.PresheafSectionComplex.complexIso.{u + 1, u, u + 1, u + 2} R (IntegralComparison.BoundedCrystalline.Site.topology fX n)
            (((T).mapHomologicalComplex (.up ℕ)).obj Km)).hom :=
  IntegralComparison.ConstantSection.ComplexRestriction.naturality.{u + 1, u, u + 2} G R (IntegralComparison.BoundedCrystalline.Site.topology fX n) (IntegralComparison.BoundedCrystalline.Site.topology fY n)
    (IntegralComparison.BoundedFrame.DeRhamSections.frameComplex fY n FY) Km
      (IntegralComparison.BoundedFrame.DeRhamSections.sheafMap fY n FY)

theorem ext_component (i : ℕ) :
    ((IntegralComparison.Ext.ZeroPresheafSections.iso.{u + 1, u, u + 1, u + 2} R (IntegralComparison.BoundedCrystalline.Site.topology fX n)).app ((T).obj ((Km).X i))).hom ≫
      (Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.globalSections fX n).map ((b).f i) =
    (IntegralComparison.Ext.ModuleFunctor.functor R (IntegralComparison.BoundedCrystalline.CrystallineCohomology.constantUnit fX n) 0).map ((b).f i) ≫
      ((IntegralComparison.Ext.ZeroPresheafSections.iso.{u + 1, u, u + 1, u + 2} R (IntegralComparison.BoundedCrystalline.Site.topology fX n)).app ((Kn).X i)).hom :=
  ((IntegralComparison.Ext.ZeroPresheafSections.iso.{u + 1, u, u + 1, u + 2} R (IntegralComparison.BoundedCrystalline.Site.topology fX n)).hom.naturality ((b).f i)).symm

theorem sectionMap : IntegralComparison.ConstantSection.ComplexRestriction.sectionMap.{u + 1, u, u + 2} R (IntegralComparison.BoundedCrystalline.Site.topology fY n)
    (IntegralComparison.BoundedFrame.DeRhamSections.frameComplex fY n FY) Km
      (IntegralComparison.BoundedFrame.DeRhamSections.sheafMap fY n FY) ≫
        ((restriction g hg n).mapHomologicalComplex (.up ℕ)).app Km ≫
          ((Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.globalSections fX n).mapHomologicalComplex (.up ℕ)).map b =
    ((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)).map
      (IntegralComparison.BoundedFrame.SectionChange.frameMap a) ≫
        IntegralComparison.ConstantSection.ComplexRestriction.sectionMap.{u + 1, u, u + 2} R (IntegralComparison.BoundedCrystalline.Site.topology fX n)
          (IntegralComparison.BoundedFrame.DeRhamSections.frameComplex fX n FX) Kn
            (IntegralComparison.BoundedFrame.DeRhamSections.sheafMap fX n FX) := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact composeSquares _ _ _ _ _ _ _ _ _
    (congrArg (fun q => q.f i) (restriction_stage g hg n (FY := FY)))
    (ext_component g hg n a i) (IntegralComparison.BoundedGeneral.FramePulledMap.sections_component g hg n a i)

theorem natural : (OpenSectionNaturality.FrameOpenSectionNaturality.globalTransformation fY n).app (op FY) ≫
    ((restriction g hg n).mapHomologicalComplex (.up ℕ)).app Km ≫
      ((Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.globalSections fX n).mapHomologicalComplex (.up ℕ)).map b =
    ((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)).map
      (IntegralComparison.BoundedFrame.SectionChange.frameMap a) ≫
        (OpenSectionNaturality.FrameOpenSectionNaturality.globalTransformation fX n).app (op FX) := by
  rw [OpenSectionCoordinates.FrameOpenSectionCoordinates.global_app, OpenSectionCoordinates.FrameOpenSectionCoordinates.global_app]
  exact sectionMap g hg n a

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.GlobalSectionPullback.FrameGlobalSectionPullback
