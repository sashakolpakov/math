import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Whiskering

/-! # Family Functor Transport -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.FamilyFunctorTransport

noncomputable section

/-! Compatible base-change functors transport actual cartesian family
diagrams and their exact kernel pairs. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u₁ u₂ u₃ v₁ v₂ v₃
variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (e : F ⋙ G ≅ H)

theorem cartesian_family_functor_transport {W T X : C} {Y : D}
    (a : W ⟶ T) (u : T ⟶ X) (q : F.obj W ⟶ Y) (b : Y ⟶ F.obj X)
    [PreservesLimit (cospan (F.map u) b) G]
    (hc : IsPullback (F.map a) q (F.map u) b) :
    IsPullback (H.map a) ((e.app W).inv ≫ G.map q) (H.map u) (G.map b ≫ (e.app X).hom) := by
  exact (hc.map G).of_iso (e.app W) (e.app T) (Iso.refl (G.obj Y)) (e.app X)
    (e.hom.naturality a)
    (by simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc])
    (e.hom.naturality u) (Category.id_comp _).symm

theorem kernelPair_functor_transport {R W : C} {Y : D}
    (s t : R ⟶ W) (q : F.obj W ⟶ Y) [PreservesLimit (cospan q q) G]
    (hk : IsKernelPair q (F.map s) (F.map t)) :
    IsKernelPair ((e.app W).inv ≫ G.map q) (H.map s) (H.map t) := by
  exact (hk.map G).of_iso (e.app R) (e.app W) (e.app W) (Iso.refl (G.obj Y))
    (e.hom.naturality s) (e.hom.naturality t)
    (by simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc])
    (by simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc])

theorem coequalizer_functor_transport {R W : C} {Y : D}
    (s t : R ⟶ W) (q : F.obj W ⟶ Y) (he : F.map s ≫ q = F.map t ≫ q) :
    H.map s ≫ ((e.app W).inv ≫ G.map q) = H.map t ≫ ((e.app W).inv ≫ G.map q) := by
  have hs : H.map s ≫ (e.app W).inv = (e.app R).inv ≫ G.map (F.map s) := e.inv.naturality s
  have ht : H.map t ≫ (e.app W).inv = (e.app R).inv ≫ G.map (F.map t) := e.inv.naturality t
  rw [← Category.assoc, hs, Category.assoc, ← G.map_comp, he, G.map_comp,
    ← Category.assoc, ← ht, Category.assoc]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.FamilyFunctorTransport
