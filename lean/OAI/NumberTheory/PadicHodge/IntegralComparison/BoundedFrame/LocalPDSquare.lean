import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.LocalReindex

/-! # Local PD Square -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.LocalPDSquare

noncomputable section

/-! The local PD comparison square assembled before specializing
its frame families and coefficient complexes to a smooth model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem compose {C : Type*} [Category C] {K A F F' A' K' Q : C}
    (a : K ⟶ A) (l : A ⟶ F) (b : F ⟶ F') (e : F' ⟶ Q)
    (q : A ⟶ A') (t : A' ⟶ F') (k : K ⟶ K') (a' : K' ⟶ A') (l' : A' ⟶ Q)
    (h₁ : l ≫ b = q ≫ t) (h₂ : t ≫ e = l') (h₃ : a ≫ q = k ≫ a') :
    (a ≫ l) ≫ (b ≫ e) = k ≫ (a' ≫ l') := by
  calc
    (a ≫ l) ≫ (b ≫ e) = (a ≫ (l ≫ b)) ≫ e := by simp only [Category.assoc]
    _ = (a ≫ (q ≫ t)) ≫ e := by rw [h₁]
    _ = (a ≫ q) ≫ (t ≫ e) := by simp only [Category.assoc]
    _ = (k ≫ a') ≫ l' := by rw [h₂, h₃]
    _ = k ≫ (a' ≫ l') := Category.assoc _ _ _

universe u v w v' w'
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  {C : Type v} [Category.{w} C] {D : Type v'} [Category.{w'} D]
  (r : D ⥤ C) (O₁ : D ⥤ Y.Opensᵒᵖ) (O₂ : C ⥤ Y.Opensᵒᵖ)
  (G₁ : D ⥤ (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ)
  (G₂ : C ⥤ (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ)
  (F₁ F₂ : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ)
  (ρ₁ : (Functor.const D).obj F₁ ⟶ G₁) (ρ₂ : (Functor.const C).obj F₂ ⟶ G₂)
  [IsIso (LocalMap.restriction f n O₁ G₁ F₁ ρ₁)]
  [IsIso (LocalMap.restriction f n O₂ G₂ F₂ ρ₂)]
  (eG : G₁ ≅ r ⋙ G₂) (eF : F₁ ≅ F₂)
  (hρ : ∀ d, ρ₁.app d ≫ eG.hom.app d = eF.hom ≫ ρ₂.app (r.obj d))
  (hO : O₁ = r ⋙ O₂)

local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p) (J := J) (δ := δ) f n
local notation "ρ'" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SectionReindex.cone f n r G₂ F₂ ρ₂
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.LocalReindexSteps.restriction (B := B) r
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)

variable (K : CochainComplex (D ⥤ ModuleCat.{u+2} (Crystalline.ExactRestriction.Coeff (B := B))) ℕ)
  (K' : CochainComplex (C ⥤ ModuleCat.{u+2} (Crystalline.ExactRestriction.Coeff (B := B))) ℕ)
  (a : K ⟶ AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (FamilySections.Family.source f n G₁))
  (a' : K' ⟶ AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (FamilySections.Family.source f n G₂))
  (k : K ⟶ ((LocalReindexSteps.restriction (B := B) r).mapHomologicalComplex (.up ℕ)).obj K')
  (ha : a ≫ AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ)
      (Functor.whiskerRight eG.hom (GeometricComparison.Frame.OpenSectionNaturality.FrameOpenSectionNaturality.source f n)) =
    k ≫ ((LocalReindexSteps.restriction (B := B) r).mapHomologicalComplex (.up ℕ)).map a')

abbrev comparison := by
  let : IsIso (LocalMap.restriction f n O₁ (r ⋙ G₂) F₂ ρ') :=
    FamilyIsoSections.Family.fixed_isIso f n O₁ eG eF ρ₁ ρ' hρ
  exact compose a
    (LocalMap.map f n O₁ G₁ F₁ ρ₁)
    (((FamilySections.Family.sections f n O₁).mapHomologicalComplex (.up ℕ)).map ((Q).map eF.hom))
    ((NatIso.mapHomologicalComplex
      (LocalMap.sectionsIso f n O₁ (r ⋙ O₂) hO) (.up ℕ)).app ((Q).obj F₂)).hom
    (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (Functor.whiskerRight eG.hom (GeometricComparison.Frame.OpenSectionNaturality.FrameOpenSectionNaturality.source f n)))
    (LocalMap.map f n O₁ (r ⋙ G₂) F₂ ρ') k
    (((H).mapHomologicalComplex (.up ℕ)).map a')
    (((H).mapHomologicalComplex (.up ℕ)).map (LocalMap.map f n O₂ G₂ F₂ ρ₂))
    (FamilyIsoSections.Family.naturality f n O₁ eG eF ρ₁ ρ' hρ)
    (LocalReindex.coordinates f n r O₂ G₂ F₂ ρ₂ O₁ hO)
    ha

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.LocalPDSquare
