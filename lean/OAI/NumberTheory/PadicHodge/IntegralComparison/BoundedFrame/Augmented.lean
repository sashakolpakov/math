import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.OrderPDSquare
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.AugmentedIncoming

/-! # Augmented -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Augmented.Comparison

noncomputable section

/-! Assemble both the PD square and incoming reindexing square at the
bounded-site level, before inserting either native smooth model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

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

variable [HasFiniteProducts C]
  [HasProducts.{v} (ModuleCat.{u+2} (Crystalline.ExactRestriction.Coeff (B := B)))]
  (L : CochainComplex (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n) ℕ)
  (V V' : Y.Opens) (hV : V = V')
  (h₁ : ∀ d, O₁ d ≤ V) (h₂ : ∀ d, O₂ d ≤ V')
  (b : ((BoundedOpen.Subsite.restriction (p := p) (J := J) (δ := δ) f V'.ι n).mapHomologicalComplex (.up ℕ)).obj ((GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p) (J := J) (δ := δ) f n).obj F₂) ⟶
    ((BoundedOpen.Subsite.restriction (p := p) (J := J) (δ := δ) f V'.ι n).mapHomologicalComplex (.up ℕ)).obj L)
  (u : ((BoundedOpen.SectionSubsite.globalSections (p := p) (J := J) (δ := δ) f n O₁).mapHomologicalComplex (.up ℕ)).obj ((GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p) (J := J) (δ := δ) f n).obj F₁) ⟶
    ((BoundedOpen.SectionSubsite.globalSections (p := p) (J := J) (δ := δ) f n O₁).mapHomologicalComplex (.up ℕ)).obj L)
  (q₁ : K ⟶ ((BoundedOpen.SectionSubsite.globalSections (p := p) (J := J) (δ := δ) f n O₁).mapHomologicalComplex (.up ℕ)).obj L)
  (q₂ : K' ⟶ ((BoundedOpen.SectionSubsite.globalSections (p := p) (J := J) (δ := δ) f n O₂).mapHomologicalComplex (.up ℕ)).obj L)
  (hq₁ : q₁ = (a ≫ LocalMap.map f n O₁.toFunctor.op G₁ F₁ ρ₁) ≫ u)
  (hq₂ : q₂ = (a' ≫ LocalMap.map f n O₂.toFunctor.op G₂ F₂ ρ₂) ≫ BoundedOpen.IncomingMap.map f n V' O₂ h₂ ((GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p) (J := J) (δ := δ) f n).obj F₂) L b)
  (hi : Homotopy u ((((BoundedOpen.SectionSubsite.globalSections (p := p) (J := J) (δ := δ) f n O₁).mapHomologicalComplex (.up ℕ)).map ((GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p) (J := J) (δ := δ) f n).map eF.hom)) ≫ BoundedOpen.IncomingMap.map f n V O₁ h₁ ((GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p) (J := J) (δ := δ) f n).obj F₂) L (BoundedOpen.IncomingMap.transport f n V ((GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p) (J := J) (δ := δ) f n).obj F₂) L V' hV b)))

local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p) (J := J) (δ := δ) f n
local notation "S₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionSubsite.globalSections (p := p) (J := J) (δ := δ) f n O₁

abbrev comparison := Bounded.AugmentedIncoming.Comparison.comparison
  f n V V' hV O₂ O₁ r h₂ h₁ hO ((Q).obj F₂) L b
  K (((S₁).mapHomologicalComplex (.up ℕ)).obj ((Q).obj F₁)) K'
  q₁ (a ≫ LocalMap.map f n O₁.toFunctor.op G₁ F₁ ρ₁) u
  (((S₁).mapHomologicalComplex (.up ℕ)).map ((Q).map eF.hom))
  (a' ≫ LocalMap.map f n O₂.toFunctor.op G₂ F₂ ρ₂) q₂ k hq₁ hq₂ hi
  (OrderPDSquare.comparison f n r O₁ O₂ G₁ G₂ F₁ F₂ ρ₁ ρ₂
    eG eF hρ hO hO' K K' a a' k ha)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Augmented.Comparison
