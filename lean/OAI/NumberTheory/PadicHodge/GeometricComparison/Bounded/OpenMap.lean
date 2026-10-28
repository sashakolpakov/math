import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.SectionFunctorMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology

/-! # Open Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.OpenMap.BoundedGeometricOpenMap

noncomputable section

/-! Arbitrary geometric pullback sends the original crystalline
sections over an open to sections over its actual inverse image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = fX) (n : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n
local notation "SX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionPresheaf.functor (p := p) (J := J) (δ := δ) fX n
local notation "SY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionPresheaf.functor (p := p) (J := J) (δ := δ) fY n
def sourceProperty (U : Y.Opens) : ObjectProperty (IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fX n) :=
  IntegralComparison.BoundedOpen.SectionPresheaf.property fX n (g ⁻¹ᵁ U)

local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.OpenMap.BoundedGeometricOpenMap.sourceProperty (p := p) (J := J) (δ := δ) (fX := fX) g n
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionPresheaf.property (p := p) (J := J) (δ := δ) fY n

theorem monotone : Monotone P := by
  intro U V h F hF
  exact IntegralComparison.BoundedOpen.SectionPresheaf.monotone fX n
    (((TopologicalSpace.Opens.map g.base).map (homOfLE h)).le) F hF

theorem preserves (U : Y.Opens) (F : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fX n) :
    P U F → Q U ((G).obj F) := by
  rintro ⟨t, ht⟩
  refine ⟨t ≫ g.resLE U (g ⁻¹ᵁ U) le_rfl, ?_⟩
  change (t ≫ g.resLE U (g ⁻¹ᵁ U) le_rfl) ≫ U.ι = F.obj.mapToX ≫ g
  rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, ht]

def precompose : (X.Opensᵒᵖ ⥤ ModuleCat.{u + 1} R) ⥤ (Y.Opensᵒᵖ ⥤ ModuleCat.{u + 1} R) :=
  (Functor.whiskeringLeft _ _ _).obj (TopologicalSpace.Opens.map g.base).op

def sectionMap (I : IntegralComparison.BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) fY n) :
    (SY).obj I ⟶ (precompose (B := B) g).obj ((SX).obj ((T).obj I)) :=
  IntegralComparison.Incoming.SectionFunctorMap.presheafMap G R (ModuleCat.of R R) P Q
    (monotone g n) (IntegralComparison.BoundedOpen.SectionPresheaf.monotone fY n) (preserves g hg n) I.obj

def functorMap : SY ⟶ T ⋙ SX ⋙ precompose (B := B) g where
  app I := sectionMap g hg n I
  naturality _ _ a :=
    (IntegralComparison.Incoming.SectionFunctorMap.functorMap G R (ModuleCat.of R R) P Q
      (monotone g n) (IntegralComparison.BoundedOpen.SectionPresheaf.monotone fY n) (preserves g hg n)).naturality a.hom

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.OpenMap.BoundedGeometricOpenMap
