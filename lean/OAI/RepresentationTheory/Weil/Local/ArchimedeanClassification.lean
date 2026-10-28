import OAI.RepresentationTheory.Weil.Local.Coordinates
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Archimedean Classification -/

namespace OAI.RepresentationTheory.Weil.Local.ArchimedeanClassification.Construction

noncomputable section

/-! Archimedean local fields are topologically isomorphic to the real or complex field. -/

theorem localField_archimedean_classification
    (k : Type) [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    (h : ¬ ∀ n : ℕ, ‖(n : k)‖ ≤ 1) :
    (∃ e : k ≃+* ℝ, Continuous e ∧ Continuous e.symm) ∨
      (∃ e : k ≃+* ℂ, Continuous e ∧ Continuous e.symm) := by
  let : Algebra ℝ k := (Coordinates.Construction.realEmbeddingOfUnbounded k h).toAlgebra
  let : ContinuousSMul ℝ k := continuousSMul_of_algebraMap ℝ k
    (Coordinates.Construction.realEmbeddingOfUnbounded_continuous k h)
  let : FiniteDimensional ℝ k := FiniteDimensional.of_locallyCompactSpace ℝ
  rcases Real.nonempty_algEquiv_or k with hR | hC
  · obtain ⟨e⟩ := hR
    exact Or.inl ⟨e.toRingEquiv, e.toLinearEquiv.toContinuousLinearEquiv.continuous,
      e.toLinearEquiv.toContinuousLinearEquiv.symm.continuous⟩
  · obtain ⟨e⟩ := hC
    exact Or.inr ⟨e.toRingEquiv, e.toLinearEquiv.toContinuousLinearEquiv.continuous,
      e.toLinearEquiv.toContinuousLinearEquiv.symm.continuous⟩

end

end OAI.RepresentationTheory.Weil.Local.ArchimedeanClassification.Construction
