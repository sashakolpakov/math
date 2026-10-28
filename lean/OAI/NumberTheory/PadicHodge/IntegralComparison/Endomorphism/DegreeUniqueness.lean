import OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.FiniteSumDegree
import OAI.NumberTheory.PadicHodge.IntegralComparison.MultivariateTailIdentity

/-! # Degree Uniqueness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeUniqueness

noncomputable section

/-! Integer shifts make the genuine degree polynomial unique for a
family containing the identity endomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe v
variable {K : Type} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  {ι : Type v} [Fintype ι] (f : ι → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A)

def withIdentity : Option ι → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A := fun i => Option.elim i 1 f

omit [IsAlgClosed K] [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom] in
theorem withIdentity_sum (a : ι → ℕ) (n : ℕ) :
    (∑ i, Option.elim i n a • withIdentity A f i) =
      (n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) + ∑ i, a i • f i := by
  simp only [Fintype.sum_option, withIdentity, Option.elim_none, Option.elim_some, nsmul_one]

theorem withIdentity_eventually_isogeny (a : ι → ℕ) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      IsFinite (∑ i, Option.elim i n a • withIdentity A f i).toMul.hom.hom.left ∧
      IsDominant (∑ i, Option.elim i n a • withIdentity A f i).toMul.hom.hom.left := by
  obtain ⟨b, hb⟩ := Frobenius.ShiftIsogeny.endomorphism_shift_eventually_isogeny A
    (-(∑ i, a i • f i))
  refine ⟨b, fun n hn => ?_⟩
  obtain ⟨hf, hs, _⟩ := hb n hn
  rw [withIdentity_sum, ← sub_neg_eq_add]
  have : Surjective ((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) - -(∑ i, a i • f i)).toMul.hom.hom.left := hs
  exact ⟨hf, inferInstance⟩

theorem eq_of_finite_dominant_evals (P Q : MvPolynomial (Option ι) ℚ)
    (h : ∀ a : Option ι → ℕ,
      IsFinite (∑ i, a i • withIdentity A f i).toMul.hom.hom.left →
      IsDominant (∑ i, a i • withIdentity A f i).toMul.hom.hom.left →
      MvPolynomial.eval (fun i => (a i : ℚ)) P =
        MvPolynomial.eval (fun i => (a i : ℚ)) Q) : P = Q := by
  apply MultivariateTailIdentity.eq_of_option_tail_eval
  intro a
  obtain ⟨b, hb⟩ := withIdentity_eventually_isogeny A f a
  exact ⟨b, fun n hn => h _ (hb n hn).1 (hb n hn).2⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeUniqueness
