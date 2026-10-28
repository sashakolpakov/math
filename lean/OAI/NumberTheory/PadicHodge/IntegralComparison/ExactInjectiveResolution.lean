import Mathlib

/-! # Exact Injective Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ExactInjectiveResolution

noncomputable section

/-!
# IntegralComparison: transporting actual injective resolutions through exact functors
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe v v' u u'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesInjectiveObjects] {Z : C} (I : InjectiveResolution Z)

def sourceIso :
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj ((CochainComplex.single₀ C).obj Z) ≅
      (CochainComplex.single₀ D).obj (F.obj Z) :=
  (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).app Z

def map : InjectiveResolution (F.obj Z) where
  cocomplex := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  injective n := Functor.PreservesInjectiveObjects.injective_obj (I.injective n)
  ι := (sourceIso F).inv ≫ (F.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι

theorem map_ι_zero : (ExactInjectiveResolution.map F I).ι.f 0 = F.map (I.ι.f 0) := by
  have h : (sourceIso F (Z := Z)).inv.f 0 = 𝟙 (F.obj Z) :=
    (HomologicalComplex.singleMapHomologicalComplex_inv_app_self F (ComplexShape.up ℕ) 0 Z).trans
      (by
        simp only [CochainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv]
        change 𝟙 (F.obj Z) ≫ F.map (𝟙 Z) = 𝟙 (F.obj Z)
        rw [F.map_id, Category.id_comp])
  change (sourceIso F).inv.f 0 ≫ F.map (I.ι.f 0) = _
  exact (congrArg (fun t => t ≫ F.map (I.ι.f 0)) h).trans (Category.id_comp _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ExactInjectiveResolution
