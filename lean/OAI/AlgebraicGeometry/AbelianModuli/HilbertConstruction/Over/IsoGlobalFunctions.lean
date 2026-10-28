import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Iso Global Functions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.IsoGlobalFunctions

noncomputable section

/-! An isomorphism of relative schemes preserves whether their global regular functions come from the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem overIso_appTop_isIso_iff {S : Scheme.{u}} {X Y : Over S} (e : X ≅ Y) :
    IsIso X.hom.appTop ↔ IsIso Y.hom.appTop := by
  have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
  have : IsIso e.hom.left.appTop := inferInstanceAs (IsIso (Scheme.Γ.map e.hom.left.op))
  have h : Y.hom.appTop ≫ e.hom.left.appTop = X.hom.appTop :=
    (Scheme.Hom.comp_appTop e.hom.left Y.hom).symm.trans (congrArg Scheme.Hom.appTop e.hom.w)
  rw [← h, isIso_comp_right_iff]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.IsoGlobalFunctions
