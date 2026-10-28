import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.OpenMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.GlobalSectionRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.PresheafSectionRestriction

/-! # Large Open Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LargeOpenMap.BoundedGeometricLargeOpenMap

noncomputable section

/-! Geometric open-section pullback in the original large coefficient
universe commutes with the original global-to-open restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = fX) (n : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n

def precompose : (X.Opensᵒᵖ ⥤ ModuleCat.{u + 2} R) ⥤ (Y.Opensᵒᵖ ⥤ ModuleCat.{u + 2} R) :=
  (Functor.whiskeringLeft _ _ _).obj (TopologicalSpace.Opens.map g.base).op

instance precompose_additive : (precompose (B := B) g).Additive := by
  dsimp only [precompose]
  infer_instance

def functorMap : IntegralComparison.BoundedOpen.SectionComplex.functor (p := p) (J := J) (δ := δ) fY n ⟶
    T ⋙ IntegralComparison.BoundedOpen.SectionComplex.functor fX n ⋙ precompose (B := B) g :=
  Functor.whiskerRight (OpenMap.BoundedGeometricOpenMap.functorMap g hg n)
    ((Functor.whiskeringRight Y.Opensᵒᵖ (ModuleCat.{u + 1} R) (ModuleCat.{u + 2} R)).obj
      (ModuleCat.uliftFunctor.{u + 2, u + 1} R))

local instance continuous : (G).IsContinuous (IntegralComparison.BoundedCrystalline.Site.topology fX n) (IntegralComparison.BoundedCrystalline.Site.topology fY n) :=
  IntegralComparison.Bounded.PostcomposeTopology.continuous g hg n

def globalRestriction : GlobalSectionRestriction.BoundedGlobalSectionRestriction.globalSections (p := p) (J := J) (δ := δ) fY n ⟶
    T ⋙ GlobalSectionRestriction.BoundedGlobalSectionRestriction.globalSections fX n :=
  IntegralComparison.Sheaf.PresheafSectionRestriction.map G R (IntegralComparison.BoundedCrystalline.Site.topology fX n) (IntegralComparison.BoundedCrystalline.Site.topology fY n)

theorem natural : GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation (p := p) (J := J) (δ := δ) fY n ≫
    functorMap g hg n =
    Functor.whiskerRight (globalRestriction g hg n) (Functor.const Y.Opensᵒᵖ) ≫
      Functor.whiskerLeft T (Functor.whiskerRight (GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation fX n)
        (precompose (B := B) g)) := by
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LargeOpenMap.BoundedGeometricLargeOpenMap
