import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.UnitCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.TransitionCocycle

/-! # Transition Cocycle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.TransitionCocycle

noncomputable section

/-! The finite overlap equations can be expressed on actual open
subschemes without changing the original regular-unit cocycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme.{0}} {I : Type} (U : I → X.Opens)

abbrev OpenTransitionCoefficients := ∀ i j : I, Γ((U i ⊓ U j).toScheme, ⊤)ˣ

def openTransitionOn (r : OpenTransitionCoefficients U) (i j : I)
    (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) : Γ(W.toScheme, ⊤)ˣ :=
  Units.map (X.homOfLE (le_inf hi hj)).appTop.hom.toMonoidHom (r i j)

def OpenTransitionCocycle (r : OpenTransitionCoefficients U) : Prop :=
  ∀ i j k : I,
    openTransitionOn U r i j ((U i ⊓ U j) ⊓ U k) (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) *
      openTransitionOn U r j k ((U i ⊓ U j) ⊓ U k) (inf_le_left.trans inf_le_right) inf_le_right =
        openTransitionOn U r i k ((U i ⊓ U j) ⊓ U k) (inf_le_left.trans inf_le_left) inf_le_right

def regularCoefficientsOfOpen (r : OpenTransitionCoefficients U) : Regular.TransitionCocycle.RegularTransitionCoefficients U :=
  fun i j => UnitCoordinates.openUnitToRegular (U i ⊓ U j) (r i j)

theorem regularCoefficientsOfOpen_on (r : OpenTransitionCoefficients U)
    (i j : I) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) :
    Regular.TransitionCocycle.regularTransitionOn U (regularCoefficientsOfOpen U r) i j W hi hj =
      UnitCoordinates.openUnitToRegular W (openTransitionOn U r i j W hi hj) :=
  (UnitCoordinates.openUnitToRegular_restrict (le_inf hi hj) (r i j)).symm

theorem regularCoefficientsOfOpen_cocycle_iff (r : OpenTransitionCoefficients U) :
    Regular.TransitionCocycle.RegularTransitionCocycle U (regularCoefficientsOfOpen U r) ↔ OpenTransitionCocycle U r := by
  constructor
  · intro h i j k
    apply UnitCoordinates.openUnitToRegular_injective
    rw [map_mul, ← regularCoefficientsOfOpen_on, ← regularCoefficientsOfOpen_on,
      ← regularCoefficientsOfOpen_on]
    exact h i j k
  · intro h i j k
    rw [regularCoefficientsOfOpen_on, regularCoefficientsOfOpen_on, regularCoefficientsOfOpen_on,
      ← map_mul, h i j k]

def openCoefficientsOfRegular (r : Regular.TransitionCocycle.RegularTransitionCoefficients U) : OpenTransitionCoefficients U :=
  fun i j => UnitCoordinates.regularUnitToOpen (U i ⊓ U j) (r i j)

theorem regularCoefficientsOfOpen_ofRegular (r : Regular.TransitionCocycle.RegularTransitionCoefficients U) :
    regularCoefficientsOfOpen U (openCoefficientsOfRegular U r) = r := by
  funext i j
  exact UnitCoordinates.openUnitToRegular_toOpen _ _

theorem openCoefficientsOfRegular_cocycle (r : Regular.TransitionCocycle.RegularTransitionCoefficients U)
    (hr : Regular.TransitionCocycle.RegularTransitionCocycle U r) : OpenTransitionCocycle U (openCoefficientsOfRegular U r) := by
  apply (regularCoefficientsOfOpen_cocycle_iff U _).mp
  rw [regularCoefficientsOfOpen_ofRegular]
  exact hr

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.TransitionCocycle
