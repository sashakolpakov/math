import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.Comparisons

/-! # Pointed Diagram Transport -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedDiagramTransport

noncomputable section

section

/-! Pointed diagram calculations, proved before specializing to the
nested coefficient-ring pullbacks. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {C D E : Type*} [Category C] [Category D] [Category E]

theorem comparison_remove_target_inverse {W Z U V A : C}
    (f : W ⟶ Z) (c : Z ⟶ U) (s : W ⟶ V) (a : V ⟶ A) (e : U ≅ A)
    (h : f ≫ c = s ≫ a ≫ e.inv) : f ≫ (c ≫ e.hom) = s ≫ a := by
  rw [← Category.assoc, h, Category.assoc, Category.assoc, e.inv_hom_id, Category.comp_id]

theorem baseChanged_map_change_source (G : C ⥤ D) {M N U : C} {P V : D}
    (k : M ≅ U) (b : M ⟶ N) (a : P ⟶ V) (eM : G.obj M ≅ P) (eN : G.obj N ≅ V)
    (h : G.map b ≫ eN.hom = eM.hom ≫ a) :
    G.map (k.inv ≫ b) ≫ eN.hom = (G.mapIso k.symm ≪≫ eM).hom ≫ a := by
  simp only [G.map_comp, Category.assoc, h, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]

theorem baseChanged_map_after_comparisons
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (c : F ⋙ G ≅ H)
    {X Y : C} {U : D} {V W : E}
    (k : F.obj X ≅ U) (eX : H.obj X ≅ V) (eY : H.obj Y ≅ W)
    (b : F.obj X ⟶ F.obj Y) (a : V ⟶ W)
    (h : G.map b ≫ (c.app Y).hom = (c.app X).hom ≫ eX.hom ≫ a ≫ eY.inv) :
    G.map (k.inv ≫ b) ≫ (c.app Y ≪≫ eY).hom =
      (G.mapIso k.symm ≪≫ c.app X ≪≫ eX).hom ≫ a := by
  have hb : G.map b ≫ (c.app Y ≪≫ eY).hom = (c.app X ≪≫ eX).hom ≫ a :=
    comparison_remove_target_inverse (G.map b) (c.app Y).hom
      (c.app X ≪≫ eX).hom a eY (by simpa only [Iso.trans_hom, Category.assoc] using h)
  exact baseChanged_map_change_source G k b a (c.app X ≪≫ eX) (c.app Y ≪≫ eY) hb

variable [CartesianMonoidalCategory C] [CartesianMonoidalCategory D] [CartesianMonoidalCategory E]

theorem iterated_comparison_comp_isMonHom
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) [F.Monoidal] [G.Monoidal] [H.Monoidal]
    (c : F ⋙ G ≅ H) (Y : C) [GrpObj Y] {A : E} [GrpObj A]
    (e : H.obj Y ≅ A) [IsMonHom e.hom] :
    IsMonHom (show G.obj (F.obj Y) ⟶ A from (c.app Y ≪≫ e).hom) := by
  let cY : G.obj (F.obj Y) ≅ H.obj Y := c.app Y
  have : IsMonHom cY.hom := Section.Comparisons.iterated_comparison_isMonHom F G H c Y
  exact inferInstanceAs (IsMonHom (cY.hom ≫ e.hom))

theorem mappedSection_eq_one_of_map (F : C ⥤ D) [F.Monoidal]
    {X Y : C} [GrpObj Y] (x : 𝟙_ C ⟶ X) (b : F.obj X ⟶ F.obj Y)
    (h : F.map x ≫ b = F.map (1 : 𝟙_ C ⟶ Y)) : Section.Comparisons.mappedSection F x ≫ b = 1 := by
  rw [Section.Comparisons.mappedSection, Category.assoc, h]
  exact Section.Comparisons.mappedSection_one F Y

theorem section_comparison_change_source
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) [F.Monoidal] [G.Monoidal] [H.Monoidal]
    (c : F ⋙ G ≅ H) {M : C} {U : D} {Z : E}
    (p : 𝟙_ C ⟶ M) (q : 𝟙_ D ⟶ U) (z : 𝟙_ E ⟶ Z)
    (k : F.obj M ≅ U) (e : H.obj M ≅ Z)
    (hp : q ≫ k.inv = Section.Comparisons.mappedSection F p) (he : Section.Comparisons.mappedSection H p ≫ e.hom = z) :
    Section.Comparisons.mappedSection G q ≫ (G.mapIso k.symm ≪≫ c.app M ≪≫ e).hom = z := by
  change Section.Comparisons.mappedSection G q ≫ (G.map k.inv ≫ (c.app M).hom ≫ e.hom) = z
  have hc : Section.Comparisons.mappedSection G (Section.Comparisons.mappedSection F p) ≫ (c.app M).hom = Section.Comparisons.mappedSection H p :=
    Section.Comparisons.mappedSection_comp_naturality F G H c.hom p
  rw [← Category.assoc, Section.Comparisons.mappedSection_map G, hp, ← Category.assoc,
    hc, he]

end

/-! Source transport preserves the section and exact complex map. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {C D : Type*} [Category C] [Category D]
  [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]

theorem pointed_map_change_source {X U Y : C} [GrpObj Y]
    (e : X ≅ U) (x : 𝟙_ C ⟶ X) (u : 𝟙_ C ⟶ U) (a : X ⟶ Y)
    (he : x ≫ e.hom = u) (ha : x ≫ a = 1) : u ≫ (e.inv ≫ a) = 1 := by
  rw [← he, Category.assoc, Iso.hom_inv_id_assoc, ha]

theorem mapped_section_change_source (F : C ⥤ D) [F.Monoidal]
    {X U : C} {W : D} (e : X ≅ U) (x : 𝟙_ C ⟶ X) (u : 𝟙_ C ⟶ U)
    (c : F.obj X ≅ W) (w : 𝟙_ D ⟶ W)
    (he : x ≫ e.hom = u) (hc : Section.Comparisons.mappedSection F x ≫ c.hom = w) :
    Section.Comparisons.mappedSection F u ≫ (F.mapIso e.symm ≪≫ c).hom = w := by
  have hi : u ≫ e.inv = x := by rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change Section.Comparisons.mappedSection F u ≫ F.map e.inv ≫ c.hom = w
  rw [← Category.assoc, Section.Comparisons.mappedSection_map, hi, hc]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedDiagramTransport
