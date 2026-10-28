import OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeUniqueness

/-! # Degree Coordinate Uniqueness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.DegreeCoordinateUniqueness.Endomorphism

noncomputable section

/-! Any coordinate representing the actual identity endomorphism
detects equality of degree polynomials. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

theorem eq_of_identity_evals {ι : Type*} [Fintype ι] (f : ι → AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A)
    (i₀ : ι) (hi₀ : f i₀ = 1) (P Q : MvPolynomial ι ℚ)
    (h : ∀ a : ι → ℕ,
      IsFinite (∑ i, a i • f i).toMul.hom.hom.left →
      IsDominant (∑ i, a i • f i).toMul.hom.hom.left →
      MvPolynomial.eval (fun i => (a i : ℚ)) P =
        MvPolynomial.eval (fun i => (a i : ℚ)) Q) : P = Q := by
  classical
  let e := Equiv.optionSubtypeNe i₀
  apply (MvPolynomial.renameEquiv ℚ e.symm).injective
  apply Endomorphism.DegreeUniqueness.eq_of_finite_dominant_evals A (fun i : {j // j ≠ i₀} => f i)
  intro a hf hd
  have he : (∑ i, a (e.symm i) • f i) =
      ∑ j, a j • Endomorphism.DegreeUniqueness.withIdentity A (fun i : {j // j ≠ i₀} => f i) j := by
    calc
      _ = ∑ j, a j • f (e j) :=
        Fintype.sum_equiv e.symm _ _ (fun i => by simp only [Equiv.apply_symm_apply])
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        cases j <;> simp only [e, Equiv.optionSubtypeNe_none, Equiv.optionSubtypeNe_some,
          Endomorphism.DegreeUniqueness.withIdentity, Option.elim_none, Option.elim_some, hi₀]
  have hf' : IsFinite (∑ i, a (e.symm i) • f i).toMul.hom.hom.left := he.symm ▸ hf
  have hd' : IsDominant (∑ i, a (e.symm i) • f i).toMul.hom.hom.left := he.symm ▸ hd
  simp only [MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename]
  change MvPolynomial.eval (fun i => (a (e.symm i) : ℚ)) P =
    MvPolynomial.eval (fun i => (a (e.symm i) : ℚ)) Q
  exact h (fun i => a (e.symm i)) hf' hd'

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.DegreeCoordinateUniqueness.Endomorphism
