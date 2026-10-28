import Mathlib.Algebra.Category.Grp.Basic

/-! # Trace Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.TraceTransport

noncomputable section

/-! Transport of an actual trace square through coefficient identifications. -/
open _root_.CategoryTheory
universe u v
theorem transport {C : Type u} [Category C] (F : C ⥤ AddCommGrpCat.{v})
    {A B A' B' : C} {T : AddCommGrpCat.{v}}
    (a : A ≅ A') (b : B ≅ B') (d : B ⟶ A) (t : B' ⟶ A')
    (hd : b.hom ≫ t = d ≫ a.hom)
    {α : F.obj A ⟶ T} {β : F.obj B ⟶ T} (h : F.map d ≫ α = β) :
    F.map t ≫ (F.map a.inv ≫ α) = F.map b.inv ≫ β := by
  rw [← h]
  simp only [← Category.assoc, ← F.map_comp]
  congr 1
  apply congrArg F.map
  apply (cancel_mono a.hom).mp
  apply (cancel_epi b.hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.hom_inv_id_assoc] using hd

theorem transportInferred {C : Type u} [Category C] {F : C ⥤ AddCommGrpCat.{v}}
    {A B : C} {T : AddCommGrpCat.{v}} {d : B ⟶ A}
    {α : F.obj A ⟶ T} {β : F.obj B ⟶ T} (h : F.map d ≫ α = β)
    {A' B' : C} (a : A ≅ A') (b : B ≅ B') (t : B' ⟶ A')
    (hd : b.hom ≫ t = d ≫ a.hom) :
    F.map t ≫ (F.map a.inv ≫ α) = F.map b.inv ≫ β :=
  transport F a b d t hd h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.TraceTransport
