import Mathlib

/-! # Shift Coherence -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Derived.ShiftCoherence

/-! Shift compatibility for the canonical comparisons used in derived naturality. -/

open _root_.CategoryTheory

section Cochains

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]

instance mapCochainNatTransCommShift (τ : F ⟶ G) :
    NatTrans.CommShift (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)) ℤ where
  shift_comm n := by
    apply NatTrans.ext
    funext K
    apply HomologicalComplex.Hom.ext
    funext i
    change 𝟙 _ ≫ τ.app (K.X (i + n)) = τ.app (K.X (i + n)) ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]

end Cochains

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [L.CommShift ℤ]
  {F G : D ⥤ E} [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G)
  [NatTrans.CommShift (Functor.whiskerLeft L τ) ℤ]

include L W in
theorem commShift_of_localization : NatTrans.CommShift τ ℤ := by
  refine ⟨fun n => ?_⟩
  apply Localization.natTrans_ext L W
  intro X
  change (F.commShiftIso n).hom.app (L.obj X) ≫ (τ.app (L.obj X))⟦n⟧' =
    τ.app ((L.obj X)⟦n⟧) ≫ (G.commShiftIso n).hom.app (L.obj X)
  let t := (L.commShiftIso n).hom.app X
  have h := NatTrans.shift_app_comm (Functor.whiskerLeft L τ) n X
  simp only [Functor.commShiftIso_comp_hom_app, Functor.whiskerLeft_app] at h
  change (F.map t ≫ (F.commShiftIso n).hom.app (L.obj X)) ≫ (τ.app (L.obj X))⟦n⟧' =
    τ.app (L.obj (X⟦n⟧)) ≫ G.map t ≫ (G.commShiftIso n).hom.app (L.obj X) at h
  erw [← Category.assoc (τ.app (L.obj (X⟦n⟧))) (G.map t), ← τ.naturality t,
    Category.assoc, Category.assoc] at h
  exact (cancel_epi (F.map t)).mp h

end OAI.AlgebraicGeometry.Comparison.Betti.Derived.ShiftCoherence
