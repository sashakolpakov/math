import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.GlobalSectionPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LargeOpenMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.CochainPullback

/-! # Open Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenNaturality.FrameGeometricOpenNaturality

noncomputable section

/-! Original frame-to-open-section comparison commutes with arbitrary
geometric pullback to inverse-image opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

private theorem composeSquares {D : Type*} [Category* D] {A B C E F G H K : D}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ E) (d : E ⟶ K)
    (e : B ⟶ F) (f : F ⟶ E) (g : F ⟶ G) (i : G ⟶ K) (l : A ⟶ H) (j : H ⟶ G)
    (h₁ : b ≫ c = e ≫ f) (h₂ : f ≫ d = g ≫ i) (h₃ : a ≫ e ≫ g = l ≫ j) :
    (a ≫ b) ≫ (c ≫ d) = l ≫ (j ≫ i) := by
  have h : b ≫ c ≫ d = (e ≫ g) ≫ i := by
    rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => a ≫ q) h).trans
      ((Category.assoc a (e ≫ g) i).symm.trans
        ((congrArg (fun q => q ≫ i) h₃).trans (Category.assoc _ _ _))))

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction
universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated fX] [IsSeparated fY] (g : X ⟶ Y) (hg : g ≫ fY = fX) (n : ℕ)
  {FX : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fX n}
  {FY : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n}
  (a : (IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n).obj FX ⟶ FY)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n
local notation "Kn" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex fX n FX
local notation "Km" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex fY n FY
local notation "b" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.FrameGeometricMap.map g hg n a
local notation "SX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.functor (p := p) (J := J) (δ := δ) fX n
local notation "SY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.functor (p := p) (J := J) (δ := δ) fY n
local notation "H" => OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LargeOpenMap.BoundedGeometricLargeOpenMap.precompose (B := B) g

local instance constXZero :
    (Functor.const X.Opensᵒᵖ : ModuleCat.{u + 2} R ⥤ X.Opensᵒᵖ ⥤ ModuleCat.{u + 2} R).PreservesZeroMorphisms where
  map_zero _ _ := rfl
local instance constYZero :
    (Functor.const Y.Opensᵒᵖ : ModuleCat.{u + 2} R ⥤ Y.Opensᵒᵖ ⥤ ModuleCat.{u + 2} R).PreservesZeroMorphisms where
  map_zero _ _ := rfl

def sectionsMap : ((SY).mapHomologicalComplex (.up ℕ)).obj Km ⟶
    ((SX ⋙ H).mapHomologicalComplex (.up ℕ)).obj Kn :=
  Section.CochainPullback.SectionCochainPullback.map T SY (SX ⋙ H) (Bounded.LargeOpenMap.BoundedGeometricLargeOpenMap.functorMap g hg n) b

theorem natural : (OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation fY n).app (op FY) ≫
    sectionsMap g hg n a =
    ((Functor.const Y.Opensᵒᵖ : ModuleCat.{u + 2} R ⥤ Y.Opensᵒᵖ ⥤ ModuleCat.{u + 2} R).mapHomologicalComplex (.up ℕ)).map
      (((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)).map
        (IntegralComparison.BoundedFrame.SectionChange.frameMap a)) ≫
          ((H).mapHomologicalComplex (.up ℕ)).map
            ((OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation fX n).app (op FX)) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext V
  have hL := congrArg (fun q => (q.app ((Km).X i)).app V)
    (Bounded.LargeOpenMap.BoundedGeometricLargeOpenMap.natural g hg n)
  have hN := congrArg (fun q => q.app (op (g ⁻¹ᵁ V.unop)))
    ((Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation fX n).naturality ((b).f i))
  have hG := congrArg (fun q => q.f i) (GlobalSectionPullback.FrameGlobalSectionPullback.natural g hg n a)
  change (((OpenSectionNaturality.FrameOpenSectionNaturality.globalTransformation fY n).app (op FY)).f i ≫
    ((Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation fY n).app ((Km).X i)).app V) ≫
      (((Bounded.LargeOpenMap.BoundedGeometricLargeOpenMap.functorMap g hg n).app ((Km).X i)).app V ≫
        ((SX).map ((b).f i)).app (op (g ⁻¹ᵁ V.unop))) =
    ((ModuleCat.uliftFunctor.{u + 2, u + 1} R).map ((IntegralComparison.BoundedFrame.SectionChange.frameMap a).f i)) ≫
      (((OpenSectionNaturality.FrameOpenSectionNaturality.globalTransformation fX n).app (op FX)).f i ≫
        ((Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation fX n).app ((Kn).X i)).app (op (g ⁻¹ᵁ V.unop)))
  exact composeSquares _ _ _ _ _ _ _ _ _ _ hL hN.symm hG

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenNaturality.FrameGeometricOpenNaturality
