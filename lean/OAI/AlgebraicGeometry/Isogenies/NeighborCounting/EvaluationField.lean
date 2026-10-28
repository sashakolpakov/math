import Mathlib.RingTheory.TotallySplit

/-! # Evaluation Field -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationField.Lifts

noncomputable section

/-!
A finite field extension evaluates every point of a finite etale algebra.
First construct the finite etale splitting algebra, then take a maximal
residue field. Base change preserves the constructed splitting.
-/

open scoped TensorProduct

universe u

variable (K C : Type u) [Field K] [CommRing C] [Algebra K C]
variable [Module.Finite K C] [Algebra.Etale K C]

/-- All generic points become individually evaluable over one finite
field extension. The splitting is constructed from finite etaleness. -/
theorem exists_finite_evaluation_field :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L),
      Algebra.IsFiniteSplit L (L ⊗[K] C) := by
  obtain ⟨T, _, _, hfaithful, hfinite, _, hsplit⟩ :=
    Algebra.IsFiniteSplit.exists_tensorProduct_of_etale
      (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := C))
  have : Nontrivial T := by
    have : Nontrivial (K ⊗[K] T) := inferInstance
    exact (TensorProduct.lid K T).symm.toEquiv.nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal T
  have : m.IsMaximal := hm
  let L := T ⧸ m
  let : Field L := Ideal.Quotient.field m
  let : Algebra K L := Ideal.Quotient.algebra K
  have : Module.Finite K L := Module.Finite.trans T L
  refine ⟨L, inferInstance, inferInstance, inferInstance, ?_⟩
  exact Algebra.IsFiniteSplit.of_algEquiv (Algebra.TensorProduct.cancelBaseChange K T L L C)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationField.Lifts
