import OAI.ArithmeticGeometry.Models.SpreadingOut.GroupReflection

/-! # Group Base Change -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.GroupBaseChange.Construction

noncomputable section

/-! Compatibility of descended group operations with successive base change. -/

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.CategoryTheory.Functor

universe u₁ v₁ u₂ v₂ u₃ v₃

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
    {C' : Type u₂} [Category.{v₂} C'] [CartesianMonoidalCategory C']
    {D : Type u₃} [Category.{v₃} D] [CartesianMonoidalCategory D]
    (F : C ⥤ C') [F.Monoidal] (G : C' ⥤ D) [G.Monoidal]
    (H : C ⥤ D) [H.Monoidal] (c : F ⋙ G ≅ H)

theorem baseChange_comparison_unit :
    G.map (LaxMonoidal.ε F) ≫ (c.app (𝟙_ C)).hom ≫ OplaxMonoidal.η H =
      OplaxMonoidal.η G := by
  have hc : LaxMonoidal.ε G ≫ G.map (LaxMonoidal.ε F) ≫ (c.app (𝟙_ C)).hom =
      LaxMonoidal.ε H := by
    simpa only [LaxMonoidal.comp_ε, Category.assoc, Iso.app_hom] using
      (NatTrans.IsMonoidal.unit (τ := c.hom))
  apply (cancel_epi (LaxMonoidal.ε G)).mp
  simpa only [← Category.assoc, Monoidal.ε_η] using
    congrArg (fun k ↦ k ≫ OplaxMonoidal.η H) hc

theorem baseChange_comparison_product (X : C) :
    G.map (LaxMonoidal.μ F X X) ≫ (c.app (X ⊗ X)).hom ≫ OplaxMonoidal.δ H X X =
      OplaxMonoidal.δ G (F.obj X) (F.obj X) ≫
        ((c.app X).hom ⊗ₘ (c.app X).hom) := by
  have hc : LaxMonoidal.μ G (F.obj X) (F.obj X) ≫ G.map (LaxMonoidal.μ F X X) ≫
      (c.app (X ⊗ X)).hom = ((c.app X).hom ⊗ₘ (c.app X).hom) ≫ LaxMonoidal.μ H X X := by
    simpa only [LaxMonoidal.comp_μ, Category.assoc, Iso.app_hom, Functor.comp_obj] using
      (NatTrans.IsMonoidal.tensor (τ := c.hom) X X)
  apply (cancel_epi (LaxMonoidal.μ G (F.obj X) (F.obj X))).mp
  simpa only [← Category.assoc, Monoidal.μ_δ_assoc, Category.id_comp,
    Category.assoc, Monoidal.μ_δ, Category.comp_id] using
    congrArg (fun k ↦ k ≫ OplaxMonoidal.δ H X X) hc

variable (X : C) [GrpObj (H.obj X)]

theorem descended_one_image (a : F.obj (𝟙_ C) ⟶ F.obj X)
    (ha : G.map a ≫ (c.app X).hom =
      (c.app (𝟙_ C)).hom ≫ OplaxMonoidal.η H ≫ η[H.obj X]) :
    letI : GrpObj (G.obj (F.obj X)) := GrpObj.ofIso (c.app X).symm
    G.map (LaxMonoidal.ε F ≫ a) = OplaxMonoidal.η G ≫ η[G.obj (F.obj X)] := by
  change G.map (LaxMonoidal.ε F ≫ a) =
    OplaxMonoidal.η G ≫ η[H.obj X] ≫ (c.app X).inv
  apply (cancel_mono (c.app X).hom).mp
  rw [G.map_comp, Category.assoc, ha]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ η[H.obj X])
    (baseChange_comparison_unit F G H c)

theorem descended_mul_image (a : F.obj (X ⊗ X) ⟶ F.obj X)
    (ha : G.map a ≫ (c.app X).hom =
      (c.app (X ⊗ X)).hom ≫ OplaxMonoidal.δ H X X ≫ μ[H.obj X]) :
    letI : GrpObj (G.obj (F.obj X)) := GrpObj.ofIso (c.app X).symm
    G.map (LaxMonoidal.μ F X X ≫ a) =
      OplaxMonoidal.δ G (F.obj X) (F.obj X) ≫ μ[G.obj (F.obj X)] := by
  change G.map (LaxMonoidal.μ F X X ≫ a) =
    OplaxMonoidal.δ G (F.obj X) (F.obj X) ≫
      (((c.app X).hom ⊗ₘ (c.app X).hom) ≫ μ[H.obj X] ≫ (c.app X).inv)
  apply (cancel_mono (c.app X).hom).mp
  rw [G.map_comp, Category.assoc, ha]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ μ[H.obj X])
    (baseChange_comparison_product F G H c X)

omit [CartesianMonoidalCategory C] [CartesianMonoidalCategory C']
  [F.Monoidal] [G.Monoidal] [H.Monoidal] in
theorem descended_inv_image (a : F.obj X ⟶ F.obj X)
    (ha : G.map a ≫ (c.app X).hom = (c.app X).hom ≫ ι[H.obj X]) :
    letI : GrpObj (G.obj (F.obj X)) := GrpObj.ofIso (c.app X).symm
    G.map a = ι[G.obj (F.obj X)] := by
  change G.map a = (c.app X).hom ≫ ι[H.obj X] ≫ (c.app X).inv
  simpa only [Category.assoc] using (Iso.eq_comp_inv (c.app X)).mpr ha

omit [GrpObj (H.obj X)] in
theorem baseChange_comparison_group_hom [GrpObj X] :
    let e : G.obj (F.obj X) ≅ H.obj X := c.app X
    letI : GrpObj (F.obj X) := Functor.grpObjObj (F := F)
    letI : GrpObj (G.obj (F.obj X)) := Functor.grpObjObj (F := G)
    letI : GrpObj (H.obj X) := Functor.grpObjObj (F := H)
    IsMonHom e.hom := by
  let : GrpObj (F.obj X) := Functor.grpObjObj (F := F)
  let : GrpObj (G.obj (F.obj X)) := Functor.grpObjObj (F := G)
  let : GrpObj (H.obj X) := Functor.grpObjObj (F := H)
  have hn {A B : C} (f : A ⟶ B) :
      G.map (F.map f) ≫ (c.app B).hom = (c.app A).hom ≫ H.map f := c.hom.naturality f
  refine { one_hom := ?_, mul_hom := ?_ }
  · change (LaxMonoidal.ε G ≫ G.map (LaxMonoidal.ε F ≫ F.map η[X])) ≫ (c.app X).hom =
      LaxMonoidal.ε H ≫ H.map η[X]
    simp only [G.map_comp, Category.assoc]
    rw [hn]
    have hc : LaxMonoidal.ε G ≫ G.map (LaxMonoidal.ε F) ≫ (c.app (𝟙_ C)).hom =
        LaxMonoidal.ε H := by
      simpa only [LaxMonoidal.comp_ε, Category.assoc, Iso.app_hom] using
        (NatTrans.IsMonoidal.unit (τ := c.hom))
    simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ H.map η[X]) hc
  · change (LaxMonoidal.μ G (F.obj X) (F.obj X) ≫
      G.map (LaxMonoidal.μ F X X ≫ F.map μ[X])) ≫ (c.app X).hom =
      ((c.app X).hom ⊗ₘ (c.app X).hom) ≫ LaxMonoidal.μ H X X ≫ H.map μ[X]
    simp only [G.map_comp, Category.assoc]
    rw [hn]
    have hc : LaxMonoidal.μ G (F.obj X) (F.obj X) ≫ G.map (LaxMonoidal.μ F X X) ≫
        (c.app (X ⊗ X)).hom = ((c.app X).hom ⊗ₘ (c.app X).hom) ≫ LaxMonoidal.μ H X X := by
      simpa only [LaxMonoidal.comp_μ, Category.assoc, Iso.app_hom, Functor.comp_obj] using
        (NatTrans.IsMonoidal.tensor (τ := c.hom) X X)
    simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ H.map μ[X]) hc

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.GroupBaseChange.Construction
