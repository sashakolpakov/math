import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Iso

/-! # Cohomology Endpoints -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyEndpoints.Comparison

noncomputable section

/-! Join the actual local comparison identities after applying cohomology. -/

open _root_.CategoryTheory

variable {D : Type*} [Category D] {K A B I K' B' I' : D}

theorem eq (s : I ≅ I') {q : K ⟶ I} {p : K ⟶ A} {a : A ⟶ I}
    {f : A ⟶ B} {b : B ⟶ I} {sB : B ⟶ B'} {r : K ⟶ K'}
    {p' : K' ⟶ B'} {a' : B' ⟶ I'} {q' : K' ⟶ I'}
    (hq : q = p ≫ a) (hq' : q' = p' ≫ a')
    (ha : a = f ≫ b) (hb : b ≫ s.hom = sB ≫ a')
    (hp : (p ≫ f) ≫ sB = r ≫ p') :
    q = (r ≫ q') ≫ s.inv := by
  have h : q ≫ s.hom = r ≫ q' := by
    rw [hq, ha, hq']
    calc
      (p ≫ (f ≫ b)) ≫ s.hom = (p ≫ f) ≫ (b ≫ s.hom) := by
        simp only [Category.assoc]
      _ = ((p ≫ f) ≫ sB) ≫ a' := by rw [hb]; simp only [Category.assoc]
      _ = _ := by rw [hp]; simp only [Category.assoc]
  calc
    q = (q ≫ s.hom) ≫ s.inv := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = _ := congrArg (fun z => z ≫ s.inv) h

theorem from_incoming (s : I ≅ I') {q : K ⟶ I} {p : K ⟶ A} {a : A ⟶ I}
    {f : A ⟶ B} {b : B ⟶ I} {p' : K' ⟶ B'} {a' : B' ⟶ I'} {q' : K' ⟶ I'}
    (hq : q = p ≫ a) (hq' : q' = p' ≫ a') (ha : a = f ≫ b) :
    ∀ (sB : B ⟶ B') (r : K ⟶ K'),
      b ≫ s.hom = sB ≫ a' → (p ≫ f) ≫ sB = r ≫ p' →
        q = (r ≫ q') ≫ s.inv := by
  intro sB r hb hp
  exact eq s hq hq' ha hb hp

variable {C E : Type*} [Category C] [Category E]

theorem mapped_transport (F : C ⥤ D) (G : E ⥤ C)
    {K I : C} {K' I' : E} (s : I ≅ G.obj I')
    {q : K ⟶ I} {r : K ⟶ G.obj K'} {q' : K' ⟶ I'}
    (h : F.map q = (F.map r ≫ (G ⋙ F).map q') ≫ (F.mapIso s).inv) :
    F.map q = F.map ((r ≫ G.map q') ≫ s.inv) := by
  simpa only [Functor.comp_map, Functor.mapIso_inv, F.map_comp] using h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CohomologyEndpoints.Comparison
