import Mathlib

/-! # Finite Continuous Sections -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteContinuousSections

noncomputable section

/-!
# Finiteness of continuous coefficient sections on noetherian sober spaces

The generic points of the finitely many irreducible components form a
finite dense set. Evaluation there injects continuous sections with
Hausdorff values into a finite product of the coefficient space.
-/

open _root_.TopologicalSpace

variable (R X V : Type*) [Field R] [TopologicalSpace X]
  [AddCommGroup V] [Module R V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousConstSMul R V] [T2Space V]

def genericPointEvaluation : C(X, V) →ₗ[R] (genericPoints X → V) where
  toFun f x := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [QuasiSober X]

theorem genericPointEvaluation_injective : Function.Injective (genericPointEvaluation R X V) := by
  intro f g hfg
  have hd : Dense (genericPoints X) := dense_iff_closure_eq.mpr genericPoints.closure
  apply ContinuousMap.injective_restrict hd
  apply ContinuousMap.ext
  intro x
  exact congrFun hfg x

variable [T0Space X] [NoetherianSpace X] [FiniteDimensional R V]

instance continuousMap_finite : FiniteDimensional R C(X, V) := by
  let _ : Fintype (genericPoints X) :=
    (genericPoints.finite (NoetherianSpace.finite_irreducibleComponents (α := X))).fintype
  exact FiniteDimensional.of_injective (genericPointEvaluation R X V) (genericPointEvaluation_injective R X V)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteContinuousSections
