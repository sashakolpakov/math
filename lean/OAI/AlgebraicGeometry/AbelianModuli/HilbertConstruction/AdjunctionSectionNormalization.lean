import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Adjunction Section Normalization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AdjunctionSectionNormalization.AdjunctionSections

noncomputable section

/-! Normalization of the sections comparison obtained from affine adjunctions. -/

open _root_.CategoryTheory

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
variable {F : C ⥤ D} {G : D ⥤ C} {F' : C' ⥤ D'} {G' : D' ⥤ C'}
variable {L : D ⥤ D'} {Q : D' ⥤ D} {E : C ⥤ C'} {H : C' ⥤ C}
variable (a : F ⊣ G) (b : F' ⊣ G') (l : L ⊣ Q) (e : E ⊣ H)
variable (t : Q ⋙ G ≅ G' ⋙ H)

def leftComparison : F ⋙ L ≅ E ⋙ F' :=
  (a.comp l).leftAdjointUniq ((e.comp b).ofNatIsoRight t.symm)

def sectionsMap (M : D) : E.obj (G.obj M) ⟶ G'.obj (L.obj M) :=
  b.homEquiv _ _ ((leftComparison a b l e t).inv.app (G.obj M) ≫ L.map (a.counit.app M))

private theorem compare_homEquiv {X : C} {Y : D'} (f : (F ⋙ L).obj X ⟶ Y) :
    ((e.comp b).ofNatIsoRight t.symm).homEquiv X Y
        ((leftComparison a b l e t).inv.app X ≫ f) = (a.comp l).homEquiv X Y f := by
  rw [Adjunction.homEquiv_naturality_right]
  change ((e.comp b).ofNatIsoRight t.symm).homEquiv _ _
      (((a.comp l).leftAdjointUniq ((e.comp b).ofNatIsoRight t.symm)).inv.app X) ≫ _ = _
  rw [Adjunction.leftAdjointUniq_inv_app, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.homEquiv_unit]

private theorem counit_homEquiv (M : D) :
    (a.comp l).homEquiv (G.obj M) (L.obj M) (L.map (a.counit.app M)) =
      G.map (l.unit.app M) := by
  have hn : l.unit.app (F.obj (G.obj M)) ≫ Q.map (L.map (a.counit.app M)) =
      a.counit.app M ≫ l.unit.app M := (l.unit.naturality (a.counit.app M)).symm
  have ht : a.unit.app (G.obj M) ≫ G.map (a.counit.app M) = 𝟙 (G.obj M) :=
    a.right_triangle_components M
  simp only [Adjunction.homEquiv_unit, Adjunction.comp_unit_app, Functor.comp_map,
    Category.assoc, ← G.map_comp]
  rw [hn, G.map_comp, ← Category.assoc, ht, Category.id_comp]

theorem normalization (M : D) :
    e.homEquiv _ _ (sectionsMap a b l e t M) = G.map (l.unit.app M) ≫ t.hom.app (L.obj M) := by
  have hc := compare_homEquiv a b l e t (L.map (a.counit.app M))
  have hc := hc.trans (counit_homEquiv a l M)
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at hc
  change e.homEquiv _ _ (sectionsMap a b l e t M) ≫ t.inv.app (L.obj M) =
    G.map (l.unit.app M) at hc
  have h := congrArg (fun z => z ≫ t.hom.app (L.obj M)) hc
  simpa only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AdjunctionSectionNormalization.AdjunctionSections
