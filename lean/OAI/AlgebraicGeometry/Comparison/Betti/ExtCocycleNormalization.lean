import OAI.AlgebraicGeometry.Comparison.Betti.ResolutionCocycleClass

/-! # Ext Cocycle Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ExtCocycleNormalization

noncomputable section

/-! The existing Ext constructor is the derived class of its actual cocycle. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

universe w u v

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] [HasExt.{w} C]
  {X Y : C} (I : InjectiveResolution Y) {n : ℕ}

theorem extMk_hom_resolutionCocycleHom (f : X ⟶ I.cocomplex.X n)
    (hf : f ≫ I.cocomplex.d n (n + 1) = 0) :
    (I.extMk f (n + 1) rfl hf).hom =
      ResolutionCocycleClass.Ext.resolutionCocycleHom I.ι' (f ≫ (I.cochainComplexXIso n n rfl).inv)
        (by
          rw [I.cochainComplex_d (n : ℤ) ((n : ℤ) + 1) n (n + 1) rfl (by omega)]
          rw [Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc, hf, zero_comp]) := by
  rw [I.extMk_hom]
  simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    ShiftedHom.comp_mk₀]
  erw [ShiftedHom.mk₀_id_comp, Category.comp_id]
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.ExtCocycleNormalization
