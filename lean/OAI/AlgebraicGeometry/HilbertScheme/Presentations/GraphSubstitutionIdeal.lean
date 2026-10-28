import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.RetractionKernel
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Graph Substitution Ideal -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.GraphSubstitutionIdeal.GradedHilbert

noncomputable section

/-! Graph equations realize polynomial substitution kernels over arbitrary coefficient rings. -/

open _root_.MvPolynomial

variable {R ι τ : Type*} [CommRing R]

def graphSubstitution (h : ι → MvPolynomial τ R) :
    MvPolynomial (ι ⊕ τ) R →ₐ[R] MvPolynomial (ι ⊕ τ) R :=
  aeval (Sum.elim (fun i => rename Sum.inr (h i)) (fun j => X (Sum.inr j)))

def graphEquation (h : ι → MvPolynomial τ R) (i : ι) : MvPolynomial (ι ⊕ τ) R :=
  X (Sum.inl i) - rename Sum.inr (h i)

theorem graphSubstitution_rename (h : ι → MvPolynomial τ R) (p : MvPolynomial τ R) :
    graphSubstitution h (rename Sum.inr p) = rename Sum.inr p := by
  have he : (graphSubstitution h).comp (rename Sum.inr) = rename Sum.inr := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [graphSubstitution]
  exact AlgHom.congr_fun he p

theorem graphSubstitution_idempotent (h : ι → MvPolynomial τ R) :
    (graphSubstitution h).comp (graphSubstitution h) = graphSubstitution h := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | inl i =>
    change graphSubstitution h (graphSubstitution h (X (Sum.inl i))) =
      graphSubstitution h (X (Sum.inl i))
    simp only [graphSubstitution, aeval_X, Sum.elim_inl]
    exact graphSubstitution_rename h (h i)
  | inr i => simp [graphSubstitution]

theorem graphSubstitution_kernel (h : ι → MvPolynomial τ R) :
    RingHom.ker (graphSubstitution h).toRingHom = Ideal.span (Set.range (graphEquation h)) := by
  rw [Polynomial.RetractionKernel.GradedHilbert.polynomial_retraction_kernel _ (graphSubstitution_idempotent h)]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    cases i with
    | inl i =>
      change X (Sum.inl i) - graphSubstitution h (X (Sum.inl i)) ∈
        Ideal.span (Set.range (graphEquation h))
      simpa only [graphSubstitution, aeval_X, Sum.elim_inl, graphEquation, SetLike.mem_coe] using
        (Ideal.subset_span (Set.mem_range_self i) : graphEquation h i ∈ Ideal.span (Set.range (graphEquation h)))
    | inr i => simp [graphSubstitution]
  · apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    apply Ideal.subset_span
    exact ⟨Sum.inl i, by simp [graphEquation, graphSubstitution]⟩

theorem graphEquation_ne_zero [Nontrivial R] (h : ι → MvPolynomial τ R) (i : ι) :
    graphEquation h i ≠ 0 := by
  classical
  intro hz
  have he (p : MvPolynomial τ R) :
      sumAlgEquiv R ι τ (rename Sum.inr p) = C p :=
    AlgHom.congr_fun (sumAlgEquiv_comp_rename_inr (R := R) (S₁ := ι) (S₂ := τ)) p
  have hz' := congrArg (sumAlgEquiv R ι τ) hz
  rw [graphEquation, map_sub, sumAlgEquiv_X_inl, he, map_zero] at hz'
  have hc := congrArg (fun p => AddMonoidAlgebra.coeff p (Finsupp.single i 1)) hz'
  have hs : (0 : ι →₀ ℕ) ≠ Finsupp.single i 1 := (Finsupp.single_ne_zero.mpr one_ne_zero).symm
  simp [hs] at hc

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.GraphSubstitutionIdeal.GradedHilbert
