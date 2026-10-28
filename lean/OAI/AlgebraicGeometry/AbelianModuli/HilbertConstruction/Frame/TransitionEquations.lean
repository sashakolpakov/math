import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.Transitions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionUnits

/-! # Transition Equations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.TransitionEquations

noncomputable section

/-! Frame transition equations on common subopens, with an equality-of-opens transport rule. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens} (D : OpenFrame.Transitions.OpenFrameTransitions U)

def FrameTransitionEquation (i j : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j)
    (x : Γ(X, U i)) (y : Γ(X, U j)) : Prop :=
  X.presheaf.map (homOfLE hi).op x = (D.value V i j hi hj).val * X.presheaf.map (homOfLE hj).op y

theorem frameTransitionEquation_of_open_eq (i j : ι) {V W : X.Opens}
    (hi : V ≤ U i) (hj : V ≤ U j) (ki : W ≤ U i) (kj : W ≤ U j) (h : V = W)
    (x : Γ(X, U i)) (y : Γ(X, U j)) :
    FrameTransitionEquation D i j V hi hj x y ↔ FrameTransitionEquation D i j W ki kj x y := by
  subst W
  rfl

def FrameCompatible (x : (i : ι) → Γ(X, U i)) : Prop :=
  ∀ i j, FrameTransitionEquation D i j (U i ⊓ U j) inf_le_left inf_le_right (x i) (x j)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.TransitionEquations
