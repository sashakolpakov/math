import Mathlib

/-! # Char Zero Field Smooth -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.CharZeroFieldSmooth.Construction

noncomputable section

/-! Every extension of fields of characteristic zero is formally
smooth, using a transcendence basis followed by a separable algebraic
extension. No finite-generation assumption is required. -/

theorem charZero_field_extension_formallySmooth
    (k K : Type*) [Field k] [CharZero k] [Field K] [Algebra k K] :
    Algebra.FormallySmooth k K := by
  obtain ⟨ι, v, hv⟩ := exists_isTranscendenceBasis' k K
  let F := IntermediateField.adjoin k (Set.range v)
  let : Algebra.IsAlgebraic F K := hv.isAlgebraic_field
  let : Algebra.IsSeparable F K := inferInstance
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hv.1

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.CharZeroFieldSmooth.Construction
