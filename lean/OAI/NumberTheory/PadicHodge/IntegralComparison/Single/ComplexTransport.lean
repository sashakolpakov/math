import Mathlib

/-! # Complex Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ComplexTransport

noncomputable section

/-!
# IntegralComparison: degree zero of an augmentation transported through an additive functor
-/

open _root_.CategoryTheory

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D] (F : C ⥤ D) [F.Additive]
  {Z : C} {Z' : D} (e : F.obj Z ≅ Z')

def sourceIso : (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj ((CochainComplex.single₀ C).obj Z) ≅
    (CochainComplex.single₀ D).obj Z' :=
  (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).app Z ≪≫
    (CochainComplex.single₀ D).mapIso e

theorem sourceIso_inv_zero : (sourceIso F e).inv.f 0 = e.inv := by
  have h : ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).app Z).inv.f 0 =
      𝟙 (F.obj Z) :=
    (HomologicalComplex.singleMapHomologicalComplex_inv_app_self F (ComplexShape.up ℕ) 0 Z).trans
      (by
        simp only [CochainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv]
        change 𝟙 (F.obj Z) ≫ F.map (𝟙 Z) = 𝟙 (F.obj Z)
        rw [F.map_id, Category.id_comp])
  change ((CochainComplex.single₀ D).map e.inv).f 0 ≫
    ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).app Z).inv.f 0 = e.inv
  exact (congrArg₂ (fun a b => a ≫ b) (CochainComplex.single₀_map_f_zero e.inv) h).trans (Category.comp_id _)

variable {K : CochainComplex C ℕ} (ι : (CochainComplex.single₀ C).obj Z ⟶ K)

def map : (CochainComplex.single₀ D).obj Z' ⟶ (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K :=
  (sourceIso F e).inv ≫ (F.mapHomologicalComplex (ComplexShape.up ℕ)).map ι

theorem map_zero : (ComplexTransport.map F e ι).f 0 = e.inv ≫ F.map (ι.f 0) :=
  congrArg (fun a => a ≫ F.map (ι.f 0)) (sourceIso_inv_zero F e)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ComplexTransport
