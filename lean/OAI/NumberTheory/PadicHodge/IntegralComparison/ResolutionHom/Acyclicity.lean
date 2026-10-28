import Mathlib

/-! # Acyclicity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.Acyclicity

noncomputable section

/-!
# IntegralComparison: transferring Ext vanishing between actual resolution Hom complexes
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u u' v v' w w'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
  {A M : C} {B N : D} (I : InjectiveResolution M) (J : InjectiveResolution N)
  (e : ∀ n, (A ⟶ I.cocomplex.X n) ≃+ (B ⟶ J.cocomplex.X n))
  (he : ∀ n (a : A ⟶ I.cocomplex.X n),
    e (n + 1) (a ≫ I.cocomplex.d n (n + 1)) = e n a ≫ J.cocomplex.d n (n + 1))

include he in
theorem subsingleton (n : ℕ) [Subsingleton (Abelian.Ext.{w'} B N (n + 1))] :
    Subsingleton (Abelian.Ext.{w} A M (n + 1)) := by
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨a, ha, rfl⟩ := I.extMk_surjective x (n + 2) rfl
  have ha' : e (n + 1) a ≫ J.cocomplex.d (n + 1) (n + 2) = 0 := by
    rw [← he, ha, AddEquiv.map_zero]
  obtain ⟨b, hb⟩ := (J.extMk_eq_zero_iff (e (n + 1) a) (n + 2) rfl ha' n rfl).mp
    (Subsingleton.elim _ _)
  apply (I.extMk_eq_zero_iff a (n + 2) rfl ha n rfl).mpr
  refine ⟨(e n).symm b, ?_⟩
  apply (e (n + 1)).injective
  rw [he, AddEquiv.apply_symm_apply, hb]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionHom.Acyclicity
