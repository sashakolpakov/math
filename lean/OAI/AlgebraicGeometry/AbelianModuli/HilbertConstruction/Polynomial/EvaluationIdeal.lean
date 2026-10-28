import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.Translation
import Mathlib.RingTheory.Ideal.Maps

/-! # Evaluation Ideal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.EvaluationIdeal

noncomputable section

/-! The evaluation kernel at a rational polynomial point has an explicit regular generating sequence, with length equal to the number of variables. -/
universe u v
variable {R : Type u} [CommRing R] {ι : Type v}

theorem polynomial_evaluation_kernel (a : ι → R) :
    RingHom.ker (MvPolynomial.eval a) =
      Ideal.span (Set.range fun i => MvPolynomial.X i - MvPolynomial.C (a i)) := by
  let I : Ideal (MvPolynomial ι R) :=
    Ideal.span (Set.range fun i => MvPolynomial.X i - MvPolynomial.C (a i))
  let φ := Ideal.Quotient.mk I
  have hx (i : ι) : φ (MvPolynomial.X i) = φ (MvPolynomial.C (a i)) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  have hφ : φ = (φ.comp MvPolynomial.C).comp (MvPolynomial.eval a) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      simpa using hx i
  apply le_antisymm
  · intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change φ p = 0
    rw [hφ]
    change φ (MvPolynomial.C (MvPolynomial.eval a p)) = 0
    rw [show MvPolynomial.eval a p = 0 from hp, map_zero, map_zero]
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    simp

theorem polynomial_evaluation_regular_generators [Nontrivial R] [Finite ι]
    (a : ι → R) :
    ∃ rs : List (MvPolynomial ι R), Regular.SequenceBasic.RingTheory.Sequence.IsRegular (MvPolynomial ι R) rs ∧
      Regular.SequenceBasic.Ideal.ofList rs = RingHom.ker (MvPolynomial.eval a) ∧ rs.length = Nat.card ι := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let xs : List ι := Finset.univ.toList
  refine ⟨xs.map (fun i => MvPolynomial.X i - MvPolynomial.C (a i)),
    Translation.coordinate_difference_list_regular a xs (Finset.nodup_toList _), ?_, ?_⟩
  · rw [polynomial_evaluation_kernel]
    apply congrArg Ideal.span
    ext p
    simp [xs]
  · simp only [xs, List.length_map, Finset.length_toList, Finset.card_univ, Nat.card_eq_fintype_card]

theorem polynomial_evaluation_kernel_isMaximal
    {K : Type u} [Field K] (a : ι → K) :
    (RingHom.ker (MvPolynomial.eval a)).IsMaximal := by
  apply RingHom.ker_isMaximal_of_surjective
  intro r
  exact ⟨MvPolynomial.C r, MvPolynomial.eval_C _⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.EvaluationIdeal
