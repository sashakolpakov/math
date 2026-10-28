import Mathlib

/-! # Augmentation Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.AugmentationTransport

noncomputable section

/-!
# IntegralComparison: augmentation transport through a natural sheafification comparison
-/

open _root_.CategoryTheory

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {H : Type u₄} [Category.{v₄} H]
  (r : C ⥤ D) (SY : C ⥤ E) (SX : D ⥤ H) (R : E ⥤ H)
  (ψ : SY ⋙ R ≅ r ⋙ SX) {A : C} {Z : E} {Z' : H}
  (e : SY.obj A ≅ Z) (t : R.obj Z ≅ Z') (s : SX.obj (r.obj A) ≅ Z')
  (h : ψ.inv.app A ≫ R.map e.hom ≫ t.hom = s.hom)

include h

theorem inverse : t.inv ≫ R.map e.inv ≫ ψ.hom.app A = s.inv := by
  have he : ψ.symm.app A ≪≫ R.mapIso e ≪≫ t = s := Iso.ext h
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun a => a.inv) he)

theorem augmentation {K : C} {L : D} (a : A ⟶ K) (q : r.obj K ⟶ L)
    (b : r.obj A ⟶ L) (ha : r.map a ≫ q = b) :
    t.inv ≫ R.map (e.inv ≫ SY.map a) ≫ (ψ.hom.app K ≫ SX.map q) =
      s.inv ≫ SX.map b := by
  have hn : R.map (SY.map a) ≫ ψ.hom.app K = ψ.hom.app A ≫ SX.map (r.map a) :=
    ψ.hom.naturality a
  calc
    _ = (t.inv ≫ R.map e.inv ≫ ψ.hom.app A) ≫ SX.map (r.map a ≫ q) := by
      rw [R.map_comp, SX.map_comp]
      simp only [Category.assoc]
      rw [← Category.assoc (R.map (SY.map a)), hn]
      simp only [Category.assoc]
    _ = s.inv ≫ SX.map b := by rw [inverse r SY SX R ψ e t s h, ha]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.AugmentationTransport
