import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Augmented
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CechHomology

/-! # Supported -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Supported.Comparison

noncomputable section

/-! Apply supported descent to the complete bounded-frame comparison
before inserting the native models. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  {C : Type u} [Preorder C] {D : Type w} [Preorder D]
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
  [HasProducts.{u} (ModuleCat.{u+2} (Crystalline.ExactRestriction.Coeff (B := B)))]
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) f n))
  (V V' : Y.Opens) (hV : V = V')
  (h₁ : ∀ d, O₁ d ≤ V) (h₂ : ∀ d, O₂ d ≤ V')
  (b : ((BoundedOpen.Subsite.restriction (p := p) (J := J) (δ := δ) f V'.ι n).mapHomologicalComplex (.up ℕ)).obj ((GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p) (J := J) (δ := δ) f n).obj F₂) ⟶
    ((BoundedOpen.Subsite.restriction (p := p) (J := J) (δ := δ) f V'.ι n).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
  (u : ((BoundedOpen.SectionSubsite.globalSections (p := p) (J := J) (δ := δ) f n O₁).mapHomologicalComplex (.up ℕ)).obj ((GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p) (J := J) (δ := δ) f n).obj F₁) ⟶
    ((BoundedOpen.SectionSubsite.globalSections (p := p) (J := J) (δ := δ) f n O₁).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
  (q₁ : K ⟶ ((BoundedOpen.SectionSubsite.globalSections (p := p) (J := J) (δ := δ) f n O₁).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
  (q₂ : K' ⟶ ((BoundedOpen.SectionSubsite.globalSections (p := p) (J := J) (δ := δ) f n O₂).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
  (hq₁ : q₁ = (a ≫ LocalMap.map f n O₁.toFunctor.op G₁ F₁ ρ₁) ≫ u)
  (hq₂ : q₂ = (a' ≫ LocalMap.map f n O₂.toFunctor.op G₂ F₂ ρ₂) ≫ BoundedOpen.IncomingMap.map f n V' O₂ h₂ ((GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p) (J := J) (δ := δ) f n).obj F₂) I.cocomplex b)
  (hi : Homotopy u ((((BoundedOpen.SectionSubsite.globalSections (p := p) (J := J) (δ := δ) f n O₁).mapHomologicalComplex (.up ℕ)).map ((GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p) (J := J) (δ := δ) f n).map eF.hom)) ≫ BoundedOpen.IncomingMap.map f n V O₁ h₁ ((GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p) (J := J) (δ := δ) f n).obj F₂) I.cocomplex (BoundedOpen.IncomingMap.transport f n V ((GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p) (J := J) (δ := δ) f n).obj F₂) I.cocomplex V' hV b)))

local notation "S₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionSubsite.globalSections (p := p) (J := J) (δ := δ) f n O₁
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.IncomingReindexSteps.restriction (B := B) r

variable (ι : Type u) [LinearOrder ι] (U : ι → C) (O : Y.Opens)
  (hOcover : ∀ i, O₁.toFunctor.obj (U i) ≤ O)
  (hcover : O₁.toFunctor.obj (⊤_ C) ⊓ O ≤ ⨆ i, O₁.toFunctor.obj (U i))
  (hrows : ∀ q t, ((Supported.OrderedCechEdge.bicomplex.{u+1,u,u,u+2}
    (Crystalline.ExactRestriction.Coeff (B := B)) Y.carrier O₁.toFunctor U
    (BoundedOpen.FlasqueComplex.complex f n I)).X q).ExactAt (t+1))
  (hglobal : O₁.toFunctor.obj (⊤_ C) ⊔ O = ⊤)

abbrev comparison (i : ℕ) :=
  BoundedSupported.CechHomology.map_eq f n I O₁.toFunctor U O hOcover hcover hrows hglobal K
    q₁ ((k ≫ ((H).mapHomologicalComplex (.up ℕ)).map q₂) ≫
      ((NatIso.mapHomologicalComplex (BoundedOpen.IncomingMap.familyIso
        (p := p) (J := J) (δ := δ) f n O₁
        (BoundedOpen.IncomingMap.reindexedOpens O₂ r) hO) (.up ℕ)).app I.cocomplex).inv)
    i (Augmented.Comparison.comparison f n r O₁ O₂ G₁ G₂ F₁ F₂ ρ₁ ρ₂
      eG eF hρ hO hO' K K' a a' k ha I.cocomplex V V' hV h₁ h₂ b u q₁ q₂ hq₁ hq₂ hi ι U i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Supported.Comparison
