import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.TransitionEquations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReindexedOpenFrameTransitions

/-! # Lifted Frame Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LiftedFrameCompatibility

noncomputable section

/-! Universe lifting a finite cover preserves the actual frame compatibility equations and its coefficient tuples. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v} {U : ι → X.Opens} (D : OpenFrame.Transitions.OpenFrameTransitions U)

theorem frameCompatible_ulift (x : (i : ULift.{u} ι) → Γ(X, U i.down)) :
    Frame.TransitionEquations.FrameCompatible (D.reindex ULift.down) x ↔ Frame.TransitionEquations.FrameCompatible D (fun i => x (ULift.up i)) := by
  constructor
  · intro h i j
    exact h (ULift.up i) (ULift.up j)
  · intro h i j
    exact h i.down j.down

def coefficientTupleULiftEquiv {R : Type u} [CommRing R] (f : R →+* Γ(X, ⊤)) :
    ((i : ULift.{u} ι) → Coefficient.AlgebraPresheaf.coefficientAlgebraSections f (U i.down)) ≃ₗ[R]
      ((i : ι) → Coefficient.AlgebraPresheaf.coefficientAlgebraSections f (U i)) where
  toFun x i := x (ULift.up i)
  invFun x i := x i.down
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LiftedFrameCompatibility
