import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.FunctionsBaseChange
import Mathlib.Topology.Sheaves.Functors

/-! # Function Sheaf Affine Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FunctionSheafAffineCriterion

noncomputable section

/-! A scheme morphism identifies all function sections if it does so on affine opens. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

def functionSheafMap (f : X ⟶ Y) :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf :=
  ⟨{ app U := f.app U.unop
     naturality _ _ h := f.naturality h }⟩

theorem functionSheafMap_isIso_of_affine (f : X ⟶ Y)
    (hf : ∀ U : Y.Opens, IsAffineOpen U → IsIso (f.app U)) : IsIso (functionSheafMap f) := by
  let B : Y.affineOpens → Y.Opens := fun U => U.1
  have hB : TopologicalSpace.Opens.IsBasis (Set.range B) := by
    have h : Set.range B = Y.affineOpens := by ext U; exact Subtype.exists.trans (by simp [B])
    rw [h]
    exact Y.isBasis_affineOpens
  apply TopCat.Sheaf.isIso_iff_isIso_basis hB
  intro U
  exact hf U.1 U.2

theorem function_app_isIso_of_affine (f : X ⟶ Y)
    (hf : ∀ U : Y.Opens, IsAffineOpen U → IsIso (f.app U)) (V : Y.Opens) : IsIso (f.app V) := by
  have : IsIso (functionSheafMap f) := functionSheafMap_isIso_of_affine f hf
  have : IsIso ((TopCat.Sheaf.forget CommRingCat Y).map (functionSheafMap f)) :=
    (TopCat.Sheaf.forget CommRingCat Y).map_isIso _
  have : IsIso f.c := this
  exact NatIso.isIso_app_of_isIso _ (Opposite.op V)

theorem morphismRestrict_appTop_isIso_iff (f : X ⟶ Y) (U : Y.Opens) :
    IsIso (f ∣_ U).appTop ↔ IsIso (f.app U) := by
  have h := Open.FunctionsBaseChange.morphismRestrict_appTop_topIso f U
  constructor
  · intro hf
    have : IsIso ((f ∣_ U).appTop ≫ (f ⁻¹ᵁ U).topIso.hom) := inferInstance
    have : IsIso (U.topIso.hom ≫ f.app U) := h ▸ this
    exact IsIso.of_isIso_comp_left U.topIso.hom (f.app U)
  · intro hf
    have : IsIso (U.topIso.hom ≫ f.app U) := inferInstance
    have : IsIso ((f ∣_ U).appTop ≫ (f ⁻¹ᵁ U).topIso.hom) := h.symm ▸ this
    exact IsIso.of_isIso_comp_right (f ∣_ U).appTop (f ⁻¹ᵁ U).topIso.hom

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FunctionSheafAffineCriterion
