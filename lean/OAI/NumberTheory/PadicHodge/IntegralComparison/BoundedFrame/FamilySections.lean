import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenSectionNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.FixedFrameDiagonalNaturality

/-! # Family Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.FamilySections.Family

noncomputable section

/-! The original absolute-to-relative frame maps on a whole family
of opens are natural under a morphism of bounded crystalline frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  {C : Type v} [Category.{w} C] (O : C ⥤ Y.Opensᵒᵖ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n
local notation "Frames" => (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p) (J := J) (δ := δ) f n

abbrev restriction : (Y.Opensᵒᵖ ⥤ ModuleCat.{u + 2} R) ⥤ (C ⥤ ModuleCat.{u + 2} R) :=
  (Functor.whiskeringLeft _ _ _).obj O

abbrev sections : A ⥤ C ⥤ ModuleCat.{u + 2} R :=
  BoundedOpen.SectionComplex.functor (p := p) (J := J) (δ := δ) f n ⋙ restriction O

local instance constPreservesZero :
    (Functor.const C : ModuleCat.{u + 2} R ⥤ C ⥤ ModuleCat.{u + 2} R).PreservesZeroMorphisms where
  map_zero _ _ := rfl

variable (G : C ⥤ (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ)

abbrev source := G ⋙ GeometricComparison.Frame.OpenSectionNaturality.FrameOpenSectionNaturality.source (p := p) (J := J) (δ := δ) f n
abbrev diagram := G ⋙ Q

def openTransformation : source f n G ⋙
    (Functor.const C : ModuleCat.{u + 2} R ⥤ C ⥤ ModuleCat.{u + 2} R).mapHomologicalComplex (.up ℕ) ⟶
      diagram f n G ⋙ (sections f n O).mapHomologicalComplex (.up ℕ) :=
  Functor.whiskerRight (Functor.whiskerLeft G (GeometricComparison.Frame.OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation f n))
    ((restriction O).mapHomologicalComplex (.up ℕ))

variable {G} {G' : C ⥤ (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ}
  (τ : G ⟶ G')

theorem open_naturality : openTransformation f n O G ≫
    Functor.whiskerRight (Functor.whiskerRight τ Q) ((sections f n O).mapHomologicalComplex (.up ℕ)) =
      Functor.whiskerRight (Functor.whiskerRight τ (GeometricComparison.Frame.OpenSectionNaturality.FrameOpenSectionNaturality.source f n))
        ((Functor.const C : ModuleCat.{u + 2} R ⥤ C ⥤ ModuleCat.{u + 2} R).mapHomologicalComplex (.up ℕ)) ≫
          openTransformation f n O G' := by
  apply NatTrans.ext
  funext r
  apply HomologicalComplex.Hom.ext
  funext q
  apply NatTrans.ext
  funext t
  exact (congrArg (fun a => (a.f q).app (O.obj t))
    ((GeometricComparison.Frame.OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation f n).naturality (τ.app r))).symm

variable (F : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ)
  (ρ : (Functor.const C).obj F ⟶ G)

def cone : (Functor.const C).obj ((Q).obj F) ⟶ diagram f n G :=
  (Functor.constComp C F Q).inv ≫ Functor.whiskerRight ρ Q

theorem cone_app (r : C) : (cone f n F ρ).app r = (Q).map (ρ.app r) :=
  Category.id_comp _

variable {F} {F' : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ}
  (ρ' : (Functor.const C).obj F' ⟶ G') (a : F ⟶ F')

theorem cone_naturality (h : ∀ r, ρ.app r ≫ τ.app r = a ≫ ρ'.app r) :
    cone f n F ρ ≫ Functor.whiskerRight τ Q =
      (Functor.const C).map ((Q).map a) ≫ cone f n F' ρ' := by
  apply NatTrans.ext
  funext r
  simp only [NatTrans.comp_app, cone_app, Functor.whiskerRight_app, Functor.const_map_app]
  exact ((Q).map_comp _ _).symm.trans ((congrArg (Q).map (h r)).trans ((Q).map_comp _ _))

theorem fixed_naturality
    [IsIso (GeometricComparison.FixedDiagramTransformation.FixedDiagramSections.map (sections f n O) ((Q).obj F) (diagram f n G) (cone f n F ρ))]
    [IsIso (GeometricComparison.FixedDiagramTransformation.FixedDiagramSections.map (sections f n O) ((Q).obj F') (diagram f n G') (cone f n F' ρ'))]
    (h : ∀ r, ρ.app r ≫ τ.app r = a ≫ ρ'.app r) :
    (GeometricComparison.FixedFrameDiagonalNaturality.FixedFrameSectionNaturality.diagonal (sections f n O) (source f n G) (diagram f n G)
        (openTransformation f n O G) ≫
      inv (GeometricComparison.FixedDiagramTransformation.FixedDiagramSections.map (sections f n O) ((Q).obj F) (diagram f n G) (cone f n F ρ))) ≫
        ((sections f n O).mapHomologicalComplex (.up ℕ)).map ((Q).map a) =
      AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (Functor.whiskerRight τ (GeometricComparison.Frame.OpenSectionNaturality.FrameOpenSectionNaturality.source f n)) ≫
        (GeometricComparison.FixedFrameDiagonalNaturality.FixedFrameSectionNaturality.diagonal (sections f n O) (source f n G') (diagram f n G')
            (openTransformation f n O G') ≫
          inv (GeometricComparison.FixedDiagramTransformation.FixedDiagramSections.map (sections f n O) ((Q).obj F') (diagram f n G') (cone f n F' ρ'))) :=
  GeometricComparison.FixedFrameDiagonalNaturality.FixedFrameSectionNaturality.fixed_naturality (sections f n O)
    (source f n G) (source f n G') (diagram f n G) (diagram f n G')
    (openTransformation f n O G) (openTransformation f n O G')
    (cone f n F ρ) (cone f n F' ρ')
    (Functor.whiskerRight τ (GeometricComparison.Frame.OpenSectionNaturality.FrameOpenSectionNaturality.source f n)) ((Q).map a) (Functor.whiskerRight τ Q)
    (cone_naturality f n τ ρ ρ' a h) (open_naturality f n O τ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.FamilySections.Family
