import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ConstantSections

/-! # Presheaf Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.PresheafSections

noncomputable section

/-!
# IntegralComparison: sections of an already separated and glued module presheaf
-/

open _root_.CategoryTheory

universe u v w z

variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{w} R)]
  (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (hP : Presheaf.IsSheaf J P)

def homLinearEquiv (M : ModuleCat.{w} R) :
    ((constantSheaf J (ModuleCat.{w} R)).obj M ⟶ (presheafToSheaf J (ModuleCat.{w} R)).obj P) ≃ₗ[R]
      ((Functor.const Cᵒᵖ).obj M ⟶ P) :=
  (LinearAdjunction.homLinearEquiv R (sheafificationAdjunction J (ModuleCat.{w} R))
    ((Functor.const Cᵒᵖ).obj M) ((presheafToSheaf J (ModuleCat.{w} R)).obj P)).trans
      (Linear.homCongr R (Iso.refl _) (isoSheafify J hP).symm)

theorem homLinearEquiv_map (M : ModuleCat.{w} R) (γ : (Functor.const Cᵒᵖ).obj M ⟶ P) :
    homLinearEquiv R J P hP M ((presheafToSheaf J (ModuleCat.{w} R)).map γ) = γ := by
  change 𝟙 _ ≫ ((sheafificationAdjunction J (ModuleCat.{w} R)).homEquiv _ _
    ((presheafToSheaf J (ModuleCat.{w} R)).map γ)) ≫ (isoSheafify J hP).inv = γ
  rw [Category.id_comp, Adjunction.homEquiv_unit]
  have h := (sheafificationAdjunction J (ModuleCat.{w} R)).unit.naturality γ
  exact (congrArg (fun t => t ≫ (isoSheafify J hP).inv) h.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun t => γ ≫ t) (isoSheafify J hP).hom_inv_id).trans (Category.comp_id γ)))

variable [HasExt.{z} (Sheaf J (ModuleCat.{w} R))]

def degreeZeroLinearEquiv :
    Abelian.Ext.{z} (Module.ConstantSections.constantUnit R J)
      ((presheafToSheaf J (ModuleCat.{w} R)).obj P) 0 ≃ₗ[R]
        ((Functor.const Cᵒᵖ).obj (ModuleCat.of R R) ⟶ P) :=
  Abelian.Ext.linearEquiv₀.trans (homLinearEquiv R J P hP (ModuleCat.of R R))

theorem degreeZero_section (M : ModuleCat.{w} R) (γ : (Functor.const Cᵒᵖ).obj M ⟶ P) (m : M) :
    degreeZeroLinearEquiv R J P hP (Module.ConstantSections.sectionMap R J M
      ((presheafToSheaf J (ModuleCat.{w} R)).obj P)
        ((presheafToSheaf J (ModuleCat.{w} R)).map γ) m) =
      (Functor.const Cᵒᵖ).map (Module.ConstantSections.elementHom R M m) ≫ γ := by
  have h : (constantSheaf J (ModuleCat.{w} R)).map (Module.ConstantSections.elementHom R M m) ≫
      (presheafToSheaf J (ModuleCat.{w} R)).map γ =
        (presheafToSheaf J (ModuleCat.{w} R)).map
          ((Functor.const Cᵒᵖ).map (Module.ConstantSections.elementHom R M m) ≫ γ) :=
    ((presheafToSheaf J (ModuleCat.{w} R)).map_comp _ _).symm
  have he := Module.ConstantSections.section_apply R J M
    ((presheafToSheaf J (ModuleCat.{w} R)).obj P) ((presheafToSheaf J (ModuleCat.{w} R)).map γ) m
  exact (congrArg (degreeZeroLinearEquiv R J P hP) he).trans
    ((congrArg (fun a => degreeZeroLinearEquiv R J P hP (Abelian.Ext.mk₀ a)) h).trans
      ((congrArg (homLinearEquiv R J P hP (ModuleCat.of R R))
        (Abelian.Ext.linearEquiv₀.apply_symm_apply _)).trans (homLinearEquiv_map R J P hP _ _)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.PresheafSections
