import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingSplitFlow
import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.ConjugationBracketOperators

/-! # Raising Split Flow Inverse -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingSplitFlowInverse.Construction

noncomputable section

/-! Reversing the split parameter inverts its action on the
weight-raising operator space. -/

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem weightRaisingSplitFlow_inverse {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric)
    (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i) (t : ℝ)
    (X : Positive.DerivationNilpotence.Construction.weightRaisingOperators b w) :
    RaisingSplitFlow.Construction.weightRaisingSplitFlow b H hH w heig (-t) (RaisingSplitFlow.Construction.weightRaisingSplitFlow b H hH w heig t X) = X := by
  apply Subtype.ext
  rw [RaisingSplitFlow.Construction.weightRaisingSplitFlow_val, RaisingSplitFlow.Construction.weightRaisingSplitFlow_val]
  exact Split.ConjugationBracketOperators.Construction.split_conjugation_inverse H X.val t

theorem weightRaisingSplitFlow_symm_apply {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric)
    (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i) (t : ℝ)
    (X : Positive.DerivationNilpotence.Construction.weightRaisingOperators b w) :
    (RaisingSplitFlow.Construction.weightRaisingSplitFlow b H hH w heig t).symm X =
      RaisingSplitFlow.Construction.weightRaisingSplitFlow b H hH w heig (-t) X := by
  have hi := weightRaisingSplitFlow_inverse b H hH w heig t
    ((RaisingSplitFlow.Construction.weightRaisingSplitFlow b H hH w heig t).symm X)
  rw [ContinuousLinearEquiv.apply_symm_apply] at hi
  exact hi.symm

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingSplitFlowInverse.Construction
