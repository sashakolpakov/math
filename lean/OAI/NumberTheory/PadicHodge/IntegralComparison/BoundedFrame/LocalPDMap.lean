import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.LocalPDSquare

/-! # Local PD Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.LocalPDMap.Square

noncomputable section

/-! The entire target local comparison is reindexed before native
model specialization, preserving the original composite map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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

abbrev mapped_comparison :=
  (LocalPDSquare.comparison f n r O₁ O₂ G₁ G₂ F₁ F₂ ρ₁ ρ₂ eG eF hρ hO K K' a a' k ha).trans
    (congrArg (fun z => k ≫ z)
      (((H).mapHomologicalComplex (.up ℕ)).map_comp a'
        (LocalMap.map f n O₂ G₂ F₂ ρ₂)).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.LocalPDMap.Square
