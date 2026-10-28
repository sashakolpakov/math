import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.UnitRestrictions

/-! # Transition Cocycle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.TransitionCocycle

noncomputable section

/-! An actual regular-unit transition cocycle retains its identity
and composition laws on every smaller algebraic overlap. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X : Scheme.{u}} {I : Type u} (U : I → X.Opens)

abbrev RegularTransitionCoefficients := ∀ i j : I, Γ(X, U i ⊓ U j)ˣ

def regularTransitionOn (r : RegularTransitionCoefficients U) (i j : I)
    (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) : Γ(X, W)ˣ :=
  UnitRestrictions.regularUnitRestrict X (le_inf hi hj) (r i j)

def RegularTransitionCocycle (r : RegularTransitionCoefficients U) : Prop :=
  ∀ i j k : I,
    regularTransitionOn U r i j ((U i ⊓ U j) ⊓ U k) (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) *
      regularTransitionOn U r j k ((U i ⊓ U j) ⊓ U k) (inf_le_left.trans inf_le_right) inf_le_right =
        regularTransitionOn U r i k ((U i ⊓ U j) ⊓ U k) (inf_le_left.trans inf_le_left) inf_le_right

theorem regularTransitionOn_restrict (r : RegularTransitionCoefficients U) (i j : I)
    {V W : X.Opens} (h : W ≤ V) (hi : V ≤ U i) (hj : V ≤ U j) :
    UnitRestrictions.regularUnitRestrict X h (regularTransitionOn U r i j V hi hj) =
      regularTransitionOn U r i j W (h.trans hi) (h.trans hj) :=
  UnitRestrictions.regularUnitRestrict_comp X (le_inf hi hj) h (r i j)

theorem regularTransition_cocycle_on (r : RegularTransitionCoefficients U) (hr : RegularTransitionCocycle U r)
    (i j k : I) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
    regularTransitionOn U r i j W hi hj * regularTransitionOn U r j k W hj hk =
      regularTransitionOn U r i k W hi hk := by
  have h := congrArg (UnitRestrictions.regularUnitRestrict X (le_inf (le_inf hi hj) hk)) (hr i j k)
  rw [map_mul, regularTransitionOn_restrict, regularTransitionOn_restrict, regularTransitionOn_restrict] at h
  exact h

theorem regularTransition_self_on (r : RegularTransitionCoefficients U) (hr : RegularTransitionCocycle U r)
    (i : I) (W : X.Opens) (hi : W ≤ U i) : regularTransitionOn U r i i W hi hi = 1 := by
  have h := regularTransition_cocycle_on U r hr i i i W hi hi hi
  exact mul_right_cancel (h.trans (one_mul _).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.TransitionCocycle
