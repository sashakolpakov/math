import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Flat Sections -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.FlatSections.Construction

noncomputable section

/-! # Completion: actual global sections under flat affine base change of a proper family -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- Flat affine base change computes actual proper global functions by a ring pushout. -/
theorem proper_flat_affine_sections_isPushout {X Y Z : Scheme.{u}}
    [IsAffine Y] [IsAffine Z] (f : X ⟶ Y) [IsProper f] (g : Z ⟶ Y) [Flat g] :
    IsPushout f.appTop g.appTop (pullback.fst f g).appTop (pullback.snd f g).appTop := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have h := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (IsPullback.of_hasPullback f g) (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤)
    (by simp) (by simp) (by simp) (isAffineOpen_top _) (isAffineOpen_top _)
    isCompact_univ isQuasiSeparated_univ
  have hs := (isIso_pushoutSection_iff
    (IsPullback.of_hasPullback f g) (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤)
    (by simp) (by simp) (by simp)).mp h
  simpa only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, TopologicalSpace.Opens.map_top] using hs

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.FlatSections.Construction
