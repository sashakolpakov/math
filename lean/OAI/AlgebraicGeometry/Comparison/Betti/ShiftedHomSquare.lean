import Mathlib.CategoryTheory.Shift.ShiftedHom

/-! # Shifted Hom Square -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ShiftedHomSquare

noncomputable section

/-! Naturality of cohomology maps with specified source and target identifications. -/

open _root_.CategoryTheory

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]

def transport (F : A ⥤ B) [F.CommShift ℤ] {a k : A} {b l : B}
    (s : F.obj a ≅ b) (t : F.obj k ⟶ l) {n : ℤ} (α : ShiftedHom a k n) : ShiftedHom b l n :=
  s.inv ≫ ShiftedHom.map α F ≫ t⟦n⟧'

theorem map_with_coefficients (F : A ⥤ B) [F.CommShift ℤ] {a k a' k' : A}
    (s : a' ⟶ a) (t : k ⟶ k') {n : ℤ} (α : ShiftedHom a k n) :
    ShiftedHom.map (s ≫ α ≫ t⟦n⟧') F = F.map s ≫ ShiftedHom.map α F ≫ (F.map t)⟦n⟧' := by
  have h := ShiftedHom.map_comp (ShiftedHom.mk₀ (0 : ℤ) rfl s)
    (α.comp (ShiftedHom.mk₀ (0 : ℤ) rfl t) (zero_add n)) (add_zero n) F
  have hp : ShiftedHom.map (α ≫ t⟦n⟧') F = ShiftedHom.map α F ≫ (F.map t)⟦n⟧' := by
    simpa only [ShiftedHom.comp_mk₀, ShiftedHom.map_mk₀] using
      ShiftedHom.map_comp α (ShiftedHom.mk₀ (0 : ℤ) rfl t) (zero_add n) F
  simpa only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, ShiftedHom.map_mk₀, hp] using h

theorem transport_comp (F : A ⥤ B) (G : B ⥤ C) [F.CommShift ℤ] [G.CommShift ℤ]
    {a k : A} {b l : B} {c m : C} (s : F.obj a ≅ b) (u : G.obj b ≅ c)
    (t : F.obj k ⟶ l) (v : G.obj l ⟶ m) {n : ℤ} (α : ShiftedHom a k n) :
    transport G u v (transport F s t α) =
      transport (F ⋙ G) (G.mapIso s ≪≫ u) (G.map t ≫ v) α := by
  change u.inv ≫ ShiftedHom.map (s.inv ≫ ShiftedHom.map α F ≫ t⟦n⟧') G ≫ v⟦n⟧' = _
  rw [map_with_coefficients]
  change u.inv ≫ (G.map s.inv ≫ ShiftedHom.map (ShiftedHom.map α F) G ≫
    (G.map t)⟦n⟧') ≫ v⟦n⟧' =
      (u.inv ≫ G.map s.inv) ≫ ShiftedHom.map α (F ⋙ G) ≫ (G.map t ≫ v)⟦n⟧'
  rw [ShiftedHom.comp_map, (shiftFunctor C n).map_comp]
  simp only [Category.assoc]

theorem transport_iso (F G : A ⥤ B) [F.CommShift ℤ] [G.CommShift ℤ]
    (e : F ≅ G) [NatTrans.CommShift e.hom ℤ]
    {a k : A} {b l : B} (s : F.obj a ≅ b) (u : G.obj a ≅ b)
    (t : F.obj k ⟶ l) (v : G.obj k ⟶ l)
    (hs : s.hom = e.hom.app a ≫ u.hom) (ht : t = e.hom.app k ≫ v)
    {n : ℤ} (α : ShiftedHom a k n) : transport F s t α = transport G u v α := by
  have he : s = e.app a ≪≫ u := Iso.ext hs
  have hn : e.inv.app a ≫ ShiftedHom.map α F ≫ (e.hom.app k)⟦n⟧' = ShiftedHom.map α G := by
    simpa only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀] using ShiftedHom.map_naturality_1 α e
  change s.inv ≫ ShiftedHom.map α F ≫ t⟦n⟧' = u.inv ≫ ShiftedHom.map α G ≫ v⟦n⟧'
  rw [he, ht, (shiftFunctor B n).map_comp]
  change (u.inv ≫ e.inv.app a) ≫ ShiftedHom.map α F ≫
    ((e.hom.app k)⟦n⟧' ≫ v⟦n⟧') = _
  simp only [Category.assoc]
  rw [← Category.assoc (ShiftedHom.map α F) ((e.hom.app k)⟦n⟧'),
    ← Category.assoc (e.inv.app a), hn]

theorem transport_square (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (J : C ⥤ D)
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ] [J.CommShift ℤ]
    (e : F ⋙ G ≅ H ⋙ J) [NatTrans.CommShift e.hom ℤ]
    {a k : A} {b l : B} {c m : C} {d q : D}
    (sF : F.obj a ≅ b) (sG : G.obj b ≅ d) (sH : H.obj a ≅ c) (sJ : J.obj c ≅ d)
    (tF : F.obj k ⟶ l) (tG : G.obj l ⟶ q) (tH : H.obj k ⟶ m) (tJ : J.obj m ⟶ q)
    (hs : G.map sF.hom ≫ sG.hom = e.hom.app a ≫ J.map sH.hom ≫ sJ.hom)
    (ht : J.map tH ≫ tJ = e.inv.app k ≫ G.map tF ≫ tG)
    {n : ℤ} (α : ShiftedHom a k n) :
    transport G sG tG (transport F sF tF α) = transport J sJ tJ (transport H sH tH α) := by
  rw [transport_comp, transport_comp]
  apply transport_iso (F ⋙ G) (H ⋙ J) e _ _ _ _ hs
  apply ((e.app k).inv_comp_eq).mp
  exact ht.symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.ShiftedHomSquare
