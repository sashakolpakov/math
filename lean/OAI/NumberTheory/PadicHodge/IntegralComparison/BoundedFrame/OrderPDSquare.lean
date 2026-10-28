import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.LocalPDMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.FamilyCoordinates

/-! # Order PD Square -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.OrderPDSquare

noncomputable section

/-! The original bounded-frame PD square in the same order-family
coordinates as the incoming comparison, before native specialization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  {C : Type v} [Preorder C] {D : Type w} [Preorder D]
  (r : C ⥤ D) (O₁ : C →o Y.Opens) (O₂ : D →o Y.Opens)
  (G₁ : Cᵒᵖ ⥤ (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ)
  (G₂ : Dᵒᵖ ⥤ (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ)
  (F₁ F₂ : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ)
  (ρ₁ : (Functor.const Cᵒᵖ).obj F₁ ⟶ G₁) (ρ₂ : (Functor.const Dᵒᵖ).obj F₂ ⟶ G₂)
  [IsIso (LocalMap.restriction f n O₁.toFunctor.op G₁ F₁ ρ₁)]
  [IsIso (LocalMap.restriction f n O₂.toFunctor.op G₂ F₂ ρ₂)]
  (eG : G₁ ≅ r.op ⋙ G₂) (eF : F₁ ≅ F₂)
  (hρ : ∀ d, ρ₁.app d ≫ eG.hom.app d = eF.hom ≫ ρ₂.app (r.op.obj d))
  (hO : O₁ = BoundedOpen.IncomingMap.reindexedOpens O₂ r)
  (hO' : O₁.toFunctor.op = r.op ⋙ O₂.toFunctor.op)
  (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u+2} (Crystalline.ExactRestriction.Coeff (B := B))) ℕ)
  (K' : CochainComplex (Dᵒᵖ ⥤ ModuleCat.{u+2} (Crystalline.ExactRestriction.Coeff (B := B))) ℕ)
  (a : K ⟶ AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (FamilySections.Family.source f n G₁))
  (a' : K' ⟶ AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (FamilySections.Family.source f n G₂))
  (k : K ⟶ ((LocalReindexSteps.restriction (B := B) r.op).mapHomologicalComplex (.up ℕ)).obj K')
  (ha : a ≫ AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ)
      (Functor.whiskerRight eG.hom (GeometricComparison.Frame.OpenSectionNaturality.FrameOpenSectionNaturality.source f n)) =
    k ≫ ((LocalReindexSteps.restriction (B := B) r.op).mapHomologicalComplex (.up ℕ)).map a')

local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p) (J := J) (δ := δ) f n
local notation "S₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionSubsite.globalSections (p := p) (J := J) (δ := δ) f n O₁
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.LocalReindexSteps.restriction (B := B) r.op
local notation "s" => NatIso.mapHomologicalComplex
  (BoundedOpen.IncomingMap.familyIso (p := p) (J := J) (δ := δ)
    f n O₁ (BoundedOpen.IncomingMap.reindexedOpens O₂ r) hO) (ComplexShape.up ℕ)

include ha hO' hρ in
theorem comparison :
    ((a ≫ LocalMap.map f n O₁.toFunctor.op G₁ F₁ ρ₁) ≫
      ((S₁).mapHomologicalComplex (.up ℕ)).map ((Q).map eF.hom)) ≫
        ((s).app ((Q).obj F₂)).hom =
    k ≫ ((H).mapHomologicalComplex (.up ℕ)).map
      (a' ≫ LocalMap.map f n O₂.toFunctor.op G₂ F₂ ρ₂) := by
  have hp := LocalPDMap.Square.mapped_comparison f n r.op
    O₁.toFunctor.op O₂.toFunctor.op G₁ G₂ F₁ F₂ ρ₁ ρ₂ eG eF hρ hO' K K' a a' k ha
  have hs := BoundedSection.FamilyCoordinates.Family.comparison f n r O₁ O₂ hO hO' ((Q).obj F₂)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => (a ≫ LocalMap.map f n O₁.toFunctor.op G₁ F₁ ρ₁) ≫
      (((S₁).mapHomologicalComplex (.up ℕ)).map ((Q).map eF.hom) ≫ z)) hs.symm).trans hp)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.OrderPDSquare
