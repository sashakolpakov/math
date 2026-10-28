import Mathlib.CategoryTheory.Whiskering

/-! # Functor Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.FunctorComparison

noncomputable section

/-! Exact cover and base equations for a family transported through two
compatible base-change functors. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory

theorem cartesian_functor_comparison
    {C D E A : Type*} [Category* C] [Category* D] [Category* E] [Category* A]
    (P : C ⥤ D) (H : D ⥤ E) (F : C ⥤ E) (J : E ⥤ A)
    (L : D ⥤ A) (G : C ⥤ A)
    (e : P ⋙ H ≅ F) (eg : H ⋙ J ≅ L) (ef : P ⋙ L ≅ G)
    {W X : C} {M : D} {Y : A} (em : L.obj M ≅ Y)
    (q₀ : P.obj W ⟶ M) (b₀ : M ⟶ P.obj X)
    (q : G.obj W ⟶ Y) (b : Y ⟶ G.obj X)
    (hq : L.map q₀ ≫ em.hom = (ef.app W).hom ≫ q)
    (hb : L.map b₀ ≫ (ef.app X).hom = em.hom ≫ b) :
    ∃ ec : F ⋙ J ≅ G, ∃ ey : J.obj (H.obj M) ≅ Y,
      J.map ((e.app W).inv ≫ H.map q₀) ≫ ey.hom = (ec.app W).hom ≫ q ∧
      J.map (H.map b₀ ≫ (e.app X).hom) ≫ (ec.app X).hom = ey.hom ≫ b := by
  let ec : F ⋙ J ≅ G := (Functor.isoWhiskerRight e J).symm ≪≫
    Functor.isoWhiskerLeft P eg ≪≫ ef
  let ey : J.obj (H.obj M) ≅ Y := eg.app M ≪≫ em
  have hnq : J.map (H.map q₀) ≫ (eg.app M).hom =
      (eg.app (P.obj W)).hom ≫ L.map q₀ := eg.hom.naturality q₀
  have hnb : J.map (H.map b₀) ≫ (eg.app (P.obj X)).hom =
      (eg.app M).hom ≫ L.map b₀ := eg.hom.naturality b₀
  have hqcomp : J.map (H.map q₀) ≫ (eg.app M).hom ≫ em.hom =
      (eg.app (P.obj W)).hom ≫ (ef.app W).hom ≫ q := by
    rw [← Category.assoc, hnq, Category.assoc, hq]
  have hbcomp : J.map (H.map b₀) ≫ (eg.app (P.obj X)).hom ≫ (ef.app X).hom =
      (eg.app M).hom ≫ em.hom ≫ b := by
    rw [← Category.assoc, hnb, Category.assoc, hb]
  refine ⟨ec, ey, ?_, ?_⟩
  · change J.map ((e.app W).inv ≫ H.map q₀) ≫ ((eg.app M).hom ≫ em.hom) =
      (J.map (e.app W).inv ≫ (eg.app (P.obj W)).hom ≫ (ef.app W).hom) ≫ q
    simp only [J.map_comp, Category.assoc]
    rw [hqcomp]
  · change J.map (H.map b₀ ≫ (e.app X).hom) ≫
      (J.map (e.app X).inv ≫ (eg.app (P.obj X)).hom ≫ (ef.app X).hom) =
        ((eg.app M).hom ≫ em.hom) ≫ b
    have hh : J.map (e.app X).hom ≫ J.map (e.app X).inv = 𝟙 _ := by
      rw [← J.map_comp, Iso.hom_inv_id, J.map_id]
    simp only [J.map_comp, Category.assoc]
    rw [← Category.assoc (J.map (e.app X).hom) (J.map (e.app X).inv), hh,
      Category.id_comp, hbcomp]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.FunctorComparison
