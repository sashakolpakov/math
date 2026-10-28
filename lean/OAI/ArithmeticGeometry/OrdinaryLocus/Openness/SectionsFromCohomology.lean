import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FreeSheafSections

/-! # Sections From Cohomology -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionsFromCohomology.Construction

noncomputable section

/-! Degree-one cohomology vanishing gives lifting of global sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.CategoryTheory.Abelian

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w} (CategoryTheory.Sheaf J AddCommGrpCat.{v})]
    {T : C} (hT : IsTerminal T)

include hT in
theorem sections_surjective_of_H_one_zero
    (S : ShortComplex (CategoryTheory.Sheaf J AddCommGrpCat.{v}))
    (hS : S.ShortExact) [Subsingleton (CategoryTheory.Sheaf.H S.X₁ 1)] :
    Function.Surjective (S.g.hom.app (op T)) := by
  intro s
  let q := (CategoryTheory.Sheaf.H.equiv₀ S.X₃ hT).symm s
  obtain ⟨t, ht⟩ := Ext.covariant_sequence_exact₃ _ hS q (rfl : 0 + 1 = 1)
    (Subsingleton.elim _ 0)
  refine ⟨CategoryTheory.Sheaf.H.equiv₀ S.X₂ hT t, ?_⟩
  rw [CategoryTheory.Sheaf.H.equiv₀_naturality]
  change CategoryTheory.Sheaf.H.equiv₀ S.X₃ hT
    (t.comp (Ext.mk₀ S.g) (add_zero 0)) = s
  rw [ht]
  exact (CategoryTheory.Sheaf.H.equiv₀ S.X₃ hT).apply_symm_apply s

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionsFromCohomology.Construction
