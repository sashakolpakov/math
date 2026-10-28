import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Augmentation
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-! # Structure Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Global.StructureUnit

noncomputable section

/-! The actual constant-function map into the global sections of a
direct-image structure sheaf, with its normalization at one. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S)

abbrev directImage := (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)

def map : ModuleCat.of Γ(S, ⊤) Γ(S, ⊤) ⟶
    (OrderedCech.Augmentation.sections π).obj (directImage f) :=
  ModuleCat.ofHom (X := ModuleCat.of Γ(S, ⊤) Γ(S, ⊤))
    (Y := (OrderedCech.Augmentation.sections π).obj (directImage f))
    { toFun := fun r => f.appTop (π.appTop r)
      map_add' := by intro r s; simp only [map_add]
      map_smul' := by
        intro r s
        change f.appTop (π.appTop (r * s)) = f.appTop (π.appTop r) * f.appTop (π.appTop s)
        simp only [map_mul] }

@[simp]
theorem map_apply (r : Γ(S, ⊤)) : map f π r = f.appTop (π.appTop r) := rfl

@[simp]
theorem map_one : map f π 1 = (1 : Γ(X, ⊤)) := by
  change f.appTop.hom (π.appTop.hom 1) = 1
  rw [RingHom.map_one, RingHom.map_one]

theorem bijective [IsIso (f ≫ π).appTop] : Function.Bijective (map f π) := by
  have h := ConcreteCategory.bijective_of_isIso (f ≫ π).appTop
  rw [Scheme.Hom.comp_appTop] at h
  exact h

instance map_isIso [IsIso (f ≫ π).appTop] : IsIso (map f π) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (bijective f π)

def iso [IsIso (f ≫ π).appTop] : ModuleCat.of Γ(S, ⊤) Γ(S, ⊤) ≅
    (OrderedCech.Augmentation.sections π).obj (directImage f) := asIso (map f π)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Global.StructureUnit
