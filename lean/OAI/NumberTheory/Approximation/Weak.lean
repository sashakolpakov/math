import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.NumberTheory.NumberField.Basic

/-! # Weak -/

namespace OAI.NumberTheory.Approximation.Weak.HodgeWeakApproximation

/-
WeakApproximation uses nontrivial, pairwise inequivalent real-valued absolute values to model
finitely many distinct places. Mathlib's abstract weak approximation theorem
gives density in the product of the corresponding `WithAbs` spaces; the
continuous dense completion maps then give the specified local completions.
The number-field hypothesis is retained from the statement specification.
-/

/-- Weak approximation for finitely many distinct places of a number field. -/
theorem weak_approximation
    (K : Type*) [Field K] [NumberField K]
    {ι : Type*} [Finite ι]
    (v : ι → AbsoluteValue K ℝ)
    (h_nontrivial : ∀ i, (v i).IsNontrivial)
    (h_distinct : Pairwise fun i j => ¬ (v i).IsEquiv (v j)) :
    DenseRange
      (fun x : K => fun i : ι => (x : (v i).Completion)) := by
  let c : ((i : ι) → WithAbs (v i)) → ((i : ι) → (v i).Completion) :=
    fun x i => (x i : (v i).Completion)
  have hc : DenseRange c :=
    DenseRange.piMap (fun i =>
      (UniformSpace.Completion.denseRange_coe :
        DenseRange ((↑) : WithAbs (v i) → (v i).Completion)))
  have hcont : Continuous c :=
    continuous_pi (fun i =>
      (UniformSpace.Completion.continuous_coe (WithAbs (v i)) :
        Continuous ((↑) : WithAbs (v i) → (v i).Completion)).comp (continuous_apply i))
  exact hc.comp (AbsoluteValue.denseRange_algebraMap_pi h_nontrivial h_distinct) hcont

end OAI.NumberTheory.Approximation.Weak.HodgeWeakApproximation
