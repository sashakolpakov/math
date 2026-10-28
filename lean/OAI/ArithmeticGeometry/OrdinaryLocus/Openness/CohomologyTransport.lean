import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CohomologyLifting
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionsFromCohomology

/-! # Cohomology Transport -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CohomologyTransport.Construction

noncomputable section

/-! Transporting degree-one vanishing through exact functors preserving global sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u u' v w w'

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {D : Type u'} [Category.{v} D] (K : GrothendieckTopology D)
    [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]

abbrev abelianSheafSections (T : C) : CategoryTheory.Sheaf J AddCommGrpCat.{v} ⥤
    AddCommGrpCat.{v} :=
  sheafToPresheaf J AddCommGrpCat ⋙ (evaluation Cᵒᵖ AddCommGrpCat).obj (op T)

variable (G : CategoryTheory.Sheaf J AddCommGrpCat.{v} ⥤
    CategoryTheory.Sheaf K AddCommGrpCat.{v}) (T : C) (T' : D)
    (η : G ⋙ abelianSheafSections K T' ≅ abelianSheafSections J T)

include η

omit [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}] in
theorem sections_surjective_of_transport
    {F E : CategoryTheory.Sheaf J AddCommGrpCat.{v}} (φ : F ⟶ E)
    (hφ : Function.Surjective ((G.map φ).hom.app (op T'))) :
    Function.Surjective (φ.hom.app (op T)) := by
  intro s
  obtain ⟨t, ht⟩ := hφ ((η.app E).inv s)
  refine ⟨(η.app F).hom t, ?_⟩
  have h := congrArg (fun f : (G.obj F).obj.obj (op T') ⟶ E.obj.obj (op T) ↦ f t)
    (η.hom.naturality φ)
  change (η.app E).hom ((G.map φ).hom.app (op T') t) =
    φ.hom.app (op T) ((η.app F).hom t) at h
  rw [ht] at h
  exact h.symm.trans ((η.app E).addCommGroupIsoToAddEquiv.apply_symm_apply s)

variable [EnoughInjectives (CategoryTheory.Sheaf J AddCommGrpCat.{v})]
    [HasExt.{w} (CategoryTheory.Sheaf J AddCommGrpCat.{v})]
    [HasExt.{w'} (CategoryTheory.Sheaf K AddCommGrpCat.{v})]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

theorem H_one_subsingleton_of_exact_section_transport
    (hT : IsTerminal T) (hT' : IsTerminal T')
    (F : CategoryTheory.Sheaf J AddCommGrpCat.{v})
    [hF : Subsingleton (CategoryTheory.Sheaf.H (G.obj F) 1)] :
    Subsingleton (CategoryTheory.Sheaf.H F 1) := by
  apply CohomologyLifting.Construction.H_one_subsingleton_of_section_lifting J F T hT
  intro S hS hSF
  have : Mono S.f := hS.mono_f
  have : Epi S.g := hS.epi_g
  have : Subsingleton (CategoryTheory.Sheaf.H (S.map G).X₁ 1) := by
    change Subsingleton (CategoryTheory.Sheaf.H (G.obj S.X₁) 1)
    rw [hSF]
    exact hF
  apply sections_surjective_of_transport J K G T T' η S.g
  exact SectionsFromCohomology.Construction.sections_surjective_of_H_one_zero K hT' (S.map G) (hS.map G)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CohomologyTransport.Construction
