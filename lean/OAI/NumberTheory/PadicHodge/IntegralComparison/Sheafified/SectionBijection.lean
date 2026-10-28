import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.PresheafSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.PresheafSections

/-! # Section Bijection -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.SectionBijection

noncomputable section

/-!
# IntegralComparison: a canonical presheaf-section bijection computes actual degree-zero Ext
-/

open _root_.CategoryTheory

universe u v w z

variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{w} R)]
  [HasExt.{z} (Sheaf J (ModuleCat.{w} R))]
  (M : ModuleCat.{w} R) (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (hP : Presheaf.IsSheaf J P)
  (γ : (Functor.const Cᵒᵖ).obj M ⟶ P)

include hP in
theorem sectionMap_bijective
    (hγ : Function.Bijective (Module.PresheafSections.sectionMap R M P γ)) :
    Function.Bijective (Module.ConstantSections.sectionMap R J M
      ((presheafToSheaf J (ModuleCat.{w} R)).obj P) ((presheafToSheaf J (ModuleCat.{w} R)).map γ)) := by
  let e := PresheafSections.degreeZeroLinearEquiv R J P hP
  have he (m : M) : e (Module.ConstantSections.sectionMap R J M
      ((presheafToSheaf J (ModuleCat.{w} R)).obj P) ((presheafToSheaf J (ModuleCat.{w} R)).map γ) m) =
        Module.PresheafSections.sectionMap R M P γ m :=
    PresheafSections.degreeZero_section R J P hP M γ m
  constructor
  · intro m m' h
    apply hγ.1
    exact (he m).symm.trans ((congrArg e h).trans (he m'))
  · intro a
    obtain ⟨m, hm⟩ := hγ.2 (e a)
    exact ⟨m, e.injective ((he m).trans hm)⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.SectionBijection
