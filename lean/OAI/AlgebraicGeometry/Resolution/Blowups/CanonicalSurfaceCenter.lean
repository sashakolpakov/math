import OAI.AlgebraicGeometry.Resolution.Blowups.CanonicalGlobalCoefficientBound
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MinimalCoefficientBound
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalSurface.CenterIndependence

/-! # Canonical Surface Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! The proper native surface center at the intrinsic least coefficient bound. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData} {n : ℕ}
    (A : GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas f J n) (hc : A.center = ⊤)
    (hn : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n ≠ ⊤)

include hn

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.coefficientBound_factorial_le : (n + 1).factorial ≤ A.coefficientBound hc := by
  by_contra h
  exact hn (A.terminal_of_uniform_bound_lt_factorial (A.hasBound_coefficientBound hc) (by omega))

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.canonicalSurface_bound :
    ∀ i, (A.choice i).HasBound (A.coefficientBound hc - 1 + 1) := by
  have hp : 1 ≤ A.coefficientBound hc :=
    (Nat.factorial_pos (n + 1)).trans_le (A.coefficientBound_factorial_le hc hn)
  rw [Nat.sub_add_cancel hp]
  exact A.hasBound_coefficientBound hc

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.canonicalSurface_level : (n + 1).factorial ≤ A.coefficientBound hc - 1 + 1 := by
  have h := A.coefficientBound_factorial_le hc hn
  have hp := Nat.factorial_pos (n + 1)
  omega

variable (hdim : ∀ i, ringKrullDim (A.rings i) ≤ 2)

def GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.canonicalSurfaceCenter : X.IdealSheafData :=
  A.surfaceCenter (A.coefficientBound hc - 1) (A.canonicalSurface_bound hc hn) hdim
    (A.canonicalSurface_level hc hn)

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.canonicalSurfaceCenter_nonzero [Nonempty X] : A.canonicalSurfaceCenter hc hn hdim ≠ ⊥ :=
  A.surfaceCenter_nonzero _ _ _ _

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.canonicalSurfaceCenter_proper : A.canonicalSurfaceCenter hc hn hdim ≠ ⊤ := by
  intro ht
  have hb := (A.surfaceCenter_eq_top_iff (A.coefficientBound hc - 1)
    (A.canonicalSurface_bound hc hn) hdim (A.canonicalSurface_level hc hn)).mp ht
  have h := (A.coefficientBound_le_iff hc (A.coefficientBound hc - 1)).mpr hb
  have hl := A.coefficientBound_factorial_le hc hn
  have hp := Nat.factorial_pos (n + 1)
  omega

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.canonicalSurfaceCenter_permissible : J ≤ (A.canonicalSurfaceCenter hc hn hdim) ^ (n + 1) :=
  A.surfaceCenter_isPermissible _ _ _ _

theorem GlobalComponent.ChoiceAtlas.Construction.GlobalComponentChoiceAtlas.canonicalSurfaceCenter_smooth : Smooth ((A.canonicalSurfaceCenter hc hn hdim).subschemeι ≫ f) :=
  A.surfaceCenter_isSmooth _ _ _ _

end

end OAI.AlgebraicGeometry.Resolution.Blowups
