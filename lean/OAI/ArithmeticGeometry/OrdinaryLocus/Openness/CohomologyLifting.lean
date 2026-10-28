import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FreeSheafSections
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ExtOneLifting

/-! # Cohomology Lifting -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CohomologyLifting.Construction

noncomputable section

/-! Vanishing of degree-one sheaf cohomology from lifting sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.CategoryTheory.Abelian

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}]
    [EnoughInjectives (CategoryTheory.Sheaf J AddCommGrpCat.{v})]
    [HasExt.{w} (CategoryTheory.Sheaf J AddCommGrpCat.{v})]
    (F : CategoryTheory.Sheaf J AddCommGrpCat.{v}) (U : C)

theorem H'_one_eq_zero_of_section_lifting
    (hlift : ∀ (S : ShortComplex (CategoryTheory.Sheaf J AddCommGrpCat.{v}))
      (_hS : S.ShortExact) (_hF : S.X₁ = F), Function.Surjective (S.g.hom.app (op U)))
    (e : F.H' 1 U) : e = 0 := by
  apply ExtOneLifting.Construction.ext_one_eq_zero_of_hom_lifting (FreeSheafSections.Construction.freeAbelianRepresentableSheaf J U) F _ e
  intro S hS hF q
  let e₂ := FreeSheafSections.Construction.freeAbelianSheafHomSectionsEquiv J U S.X₂
  let e₃ := FreeSheafSections.Construction.freeAbelianSheafHomSectionsEquiv J U S.X₃
  obtain ⟨t, ht⟩ := hlift S hS hF (e₃ q)
  refine ⟨e₂.symm t, e₃.injective ?_⟩
  change FreeSheafSections.Construction.freeAbelianSheafHomSectionsEquiv J U S.X₃ (e₂.symm t ≫ S.g) = e₃ q
  rw [FreeSheafSections.Construction.freeAbelianSheafHomSectionsEquiv_naturality]
  exact (congrArg (S.g.hom.app (op U)) (e₂.apply_symm_apply t)).trans ht

theorem H_one_subsingleton_of_section_lifting (hU : IsTerminal U)
    (hlift : ∀ (S : ShortComplex (CategoryTheory.Sheaf J AddCommGrpCat.{v}))
      (_hS : S.ShortExact) (_hF : S.X₁ = F), Function.Surjective (S.g.hom.app (op U))) :
    Subsingleton (CategoryTheory.Sheaf.H F 1) := by
  have : Subsingleton (F.H' 1 U) :=
    subsingleton_of_forall_eq 0 (H'_one_eq_zero_of_section_lifting J F U hlift)
  exact (CohomologyTerminal.Construction.cohomologyAtTerminalIso hU J F 1).addCommGroupIsoToAddEquiv.symm.injective.subsingleton

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CohomologyLifting.Construction
