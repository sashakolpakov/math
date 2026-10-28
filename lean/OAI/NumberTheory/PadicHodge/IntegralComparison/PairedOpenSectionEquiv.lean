import OAI.NumberTheory.PadicHodge.IntegralComparison.Open.SectionAlgebraIso
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Paired Open Section Equiv -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PairedOpenSectionEquiv

noncomputable section

/-! Restrict an original section-algebra isomorphism represented by
 two open embeddings of a common scheme. All smaller maps are induced
 by those same embeddings. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R]
  (T X₁ X₂ : Over (Spec (CommRingCat.of R)))
  (f₁ : T.left ⟶ X₁.left) (f₂ : T.left ⟶ X₂.left)
  [IsOpenImmersion f₁] [IsOpenImmersion f₂]
  (hf₁ : f₁ ≫ X₁.hom = T.hom) (hf₂ : f₂ ≫ X₂.hom = T.hom)

def iso (U : T.left.Opens) :
    (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X₁).obj (op (f₁ ''ᵁ U)) ≅
      (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X₂).obj (op (f₂ ''ᵁ U)) :=
  (Open.SectionAlgebraIso.component R T X₁ f₁ hf₁ U).symm ≪≫
    Open.SectionAlgebraIso.component R T X₂ f₂ hf₂ U

def equiv (U : T.left.Opens) := CommAlgCat.algEquivOfIso (iso R T X₁ X₂ f₁ f₂ hf₁ hf₂ U)

theorem naturality {U V : T.left.Opens} (i : V ⟶ U) :
    (iso R T X₁ X₂ f₁ f₂ hf₁ hf₂ U).hom ≫
      (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X₂).map (f₂.opensFunctor.map i).op =
    (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X₁).map (f₁.opensFunctor.map i).op ≫
      (iso R T X₁ X₂ f₁ f₂ hf₁ hf₂ V).hom := by
  have h₁ := (Open.SectionAlgebraIso.iso R T X₁ f₁ hf₁).inv.naturality i.op
  have h₂ := (Open.SectionAlgebraIso.iso R T X₂ f₂ hf₂).hom.naturality i.op
  change (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X₁).map (f₁.opensFunctor.map i).op ≫
    (Open.SectionAlgebraIso.component R T X₁ f₁ hf₁ V).inv =
      (Open.SectionAlgebraIso.component R T X₁ f₁ hf₁ U).inv ≫
        (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R T).map i.op at h₁
  change (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R T).map i.op ≫
    (Open.SectionAlgebraIso.component R T X₂ f₂ hf₂ V).hom =
      (Open.SectionAlgebraIso.component R T X₂ f₂ hf₂ U).hom ≫
        (OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X₂).map (f₂.opensFunctor.map i).op at h₂
  change (iso R T X₁ X₂ f₁ f₂ hf₁ hf₂ U).hom ≫ _ = _
  dsimp only [iso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, ← h₂, ← Category.assoc, ← h₁, Category.assoc]

omit hf₁ hf₂ in
theorem affine (U : T.left.Opens) (hU : IsAffineOpen U) :
    IsAffineOpen (f₁ ''ᵁ U) ∧ IsAffineOpen (f₂ ''ᵁ U) :=
  ⟨hU.image_of_isOpenImmersion f₁, hU.image_of_isOpenImmersion f₂⟩

omit hf₁ hf₂ in
theorem contains {S : Scheme.{u}} (s : S ⟶ T.left) (U : T.left.Opens)
    (hs : ⊤ ≤ s ⁻¹ᵁ U) :
    (⊤ ≤ (s ≫ f₁) ⁻¹ᵁ (f₁ ''ᵁ U)) ∧ (⊤ ≤ (s ≫ f₂) ⁻¹ᵁ (f₂ ''ᵁ U)) := by
  constructor <;> intro x hx
  · exact ⟨s x, hs hx, rfl⟩
  · exact ⟨s x, hs hx, rfl⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PairedOpenSectionEquiv
