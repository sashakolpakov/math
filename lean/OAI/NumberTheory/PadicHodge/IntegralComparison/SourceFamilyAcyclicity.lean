import OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.Acyclicity

/-! # Source Family Acyclicity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SourceFamilyAcyclicity.Family

noncomputable section

/-! Source acyclicity from differential-compatible families of actual resolution morphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v z w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {Q H : C} {ι : Type w} (P : ι → C) (I : InjectiveResolution H)
  (e : ∀ q, (Q ⟶ I.cocomplex.X q) ≃+ (∀ j, P j ⟶ I.cocomplex.X q))
  (he : ∀ q (a : Q ⟶ I.cocomplex.X q) j,
    e (q + 1) (a ≫ I.cocomplex.d q (q + 1)) j = e q a j ≫ I.cocomplex.d q (q + 1))

include he in
theorem subsingleton (n : ℕ) [∀ j, Subsingleton (Abelian.Ext.{z} (P j) H (n + 1))] :
    Subsingleton (Abelian.Ext.{z} Q H (n + 1)) := by
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨a, ha, rfl⟩ := I.extMk_surjective x (n + 2) rfl
  have hc (j : ι) : e (n + 1) a j ≫ I.cocomplex.d (n + 1) (n + 2) = 0 := by
    rw [← he, ha, AddEquiv.map_zero]
    rfl
  have hb (j : ι) : ∃ b : P j ⟶ I.cocomplex.X n,
      b ≫ I.cocomplex.d n (n + 1) = e (n + 1) a j :=
    (I.extMk_eq_zero_iff (e (n + 1) a j) (n + 2) rfl (hc j) n rfl).mp
      (Subsingleton.elim _ _)
  choose b hb using hb
  apply (I.extMk_eq_zero_iff a (n + 2) rfl ha n rfl).mpr
  refine ⟨(e n).symm b, ?_⟩
  apply (e (n + 1)).injective
  funext j
  rw [he, AddEquiv.apply_symm_apply, hb]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SourceFamilyAcyclicity.Family
