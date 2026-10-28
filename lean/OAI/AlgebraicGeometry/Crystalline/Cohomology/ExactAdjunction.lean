import OAI.AlgebraicGeometry.Crystalline.Cohomology.ExactInjective
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Exact Adjunction -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ExactAdjunction.ExactAdjunctionExtVanishing

noncomputable section

/-! # Transporting positive Ext vanishing across an exact adjunction -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v' e e'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{e} C]

theorem of_sourceIso {X X' Y : C} (i : X ≅ X') (n : ℕ)
    (h : ∀ α : Abelian.Ext X' Y n, α = 0) (α : Abelian.Ext X Y n) : α = 0 := by
  have hz := congrArg (fun β : Abelian.Ext X' Y n =>
    (Abelian.Ext.mk₀ i.hom).comp β (zero_add n))
      (h ((Abelian.Ext.mk₀ i.inv).comp α (zero_add n)))
  simpa only [Abelian.Ext.mk₀_comp_mk₀_assoc, i.hom_inv_id,
    Abelian.Ext.mk₀_id_comp, Abelian.Ext.comp_zero] using hz

variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{e'} D]
  {F : C ⥤ D} [F.Additive] {G : D ⥤ C} [G.Additive]
  [G.PreservesHomology] [G.PreservesInjectiveObjects] (adj : F ⊣ G)
  {X : C} {Y : D} (I : InjectiveResolution Y) (n : ℕ)

include adj I in
theorem rightAdjoint
    (h : ∀ α : Abelian.Ext (F.obj X) Y (n + 1), α = 0)
    (α : Abelian.Ext X (G.obj Y) (n + 1)) : α = 0 := by
  let I' : InjectiveResolution (G.obj Y) := ExactInjective.ExactInjectiveResolution.map G I
  obtain ⟨f, hf, rfl⟩ := I'.extMk_surjective α (n + 2) rfl
  change X ⟶ G.obj (I.cocomplex.X (n + 1)) at f
  let f' : F.obj X ⟶ I.cocomplex.X (n + 1) := (adj.homEquiv X _).symm f
  have hf' : f' ≫ I.cocomplex.d (n + 1) (n + 2) = 0 := by
    apply (adj.homEquiv X (I.cocomplex.X (n + 2))).injective
    rw [adj.homEquiv_naturality_right, adj.homAddEquiv_zero]
    change adj.homEquiv X _ ((adj.homEquiv X _).symm f) ≫
      G.map (I.cocomplex.d (n + 1) (n + 2)) = 0
    rw [Equiv.apply_symm_apply]
    exact hf
  obtain ⟨g, hg⟩ := (I.extMk_eq_zero_iff f' (n + 2) rfl hf' n rfl).mp (h (I.extMk f' (n + 2) rfl hf'))
  apply (I'.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).mpr
  refine ⟨adj.homEquiv X _ g, ?_⟩
  change adj.homEquiv X _ g ≫ G.map (I.cocomplex.d n (n + 1)) = f
  rw [← adj.homEquiv_naturality_right, hg]
  exact (adj.homEquiv X _).apply_symm_apply f

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ExactAdjunction.ExactAdjunctionExtVanishing
