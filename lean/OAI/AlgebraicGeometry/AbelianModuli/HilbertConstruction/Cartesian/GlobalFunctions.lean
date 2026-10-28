import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Over.IsoGlobalFunctions
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Global Functions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.GlobalFunctions

noncomputable section

/-! Global-function isomorphisms are independent of the chosen Cartesian base-change model. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem cartesian_globalFunctions_isIso_iff
    {X S T Y : Scheme.{u}} {a : Y ⟶ X} {b : Y ⟶ T} {p : X ⟶ S} {c : T ⟶ S}
    (H : IsPullback a b p c) : IsIso b.appTop ↔ IsIso (pullback.snd p c).appTop := by
  let e : Over.mk b ≅ Over.mk (pullback.snd p c) :=
    Over.isoMk H.isoPullback H.isoPullback_hom_snd
  exact HilbertConstruction.Over.IsoGlobalFunctions.overIso_appTop_isIso_iff e

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.GlobalFunctions
