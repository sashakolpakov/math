import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.ConstantSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections

/-! # Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.Coordinates

noncomputable section

/-! Canonical Ext-zero sections from constant modules retain their actual presheaf values. -/

open _root_.CategoryTheory

universe u v w z

variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{w} R)]
  [HasExt.{max u w z} (Sheaf J (ModuleCat.{w} R))]
  (M : ModuleCat.{w} R) (N : Sheaf J (ModuleCat.{w} R))
  (a : (constantSheaf J (ModuleCat.{w} R)).obj M ⟶ N) (m : M)

theorem section_eq : Ext.ZeroPresheafSections.equivalence R J N
    (Module.ConstantSections.sectionMap R J M N a m) =
      ULift.up ((Functor.const Cᵒᵖ).map (Module.ConstantSections.elementHom R M m) ≫
        (sheafificationAdjunction J (ModuleCat.{w} R)).homEquiv _ _ a) := by
  rw [Module.ConstantSections.section_apply, Ext.ZeroPresheafSections.equivalence_mk]
  apply congrArg ULift.up
  exact (sheafificationAdjunction J (ModuleCat.{w} R)).homEquiv_naturality_left
    ((Functor.const Cᵒᵖ).map (Module.ConstantSections.elementHom R M m)) a

theorem section_apply (U : Cᵒᵖ) (r : R) :
    (Ext.ZeroPresheafSections.equivalence R J N
      (Module.ConstantSections.sectionMap R J M N a m)).down.app U r =
    ((sheafificationAdjunction J (ModuleCat.{w} R)).homEquiv _ _ a).app U (r • m) := by
  rw [section_eq]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.Coordinates
