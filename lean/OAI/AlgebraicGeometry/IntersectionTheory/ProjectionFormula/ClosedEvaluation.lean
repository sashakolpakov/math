import Mathlib.RingTheory.Nullstellensatz

/-! # Closed Evaluation -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ClosedEvaluation

noncomputable section

/-! A nonzero element of a finite type domain over an algebraically closed
field survives evaluation at a rational point. -/

open scoped Classical

theorem exists_nonzero (K R : Type*) [Field K] [IsAlgClosed K]
    [CommRing R] [IsDomain R] [Algebra K R] [Algebra.FiniteType K R]
    (a : R) (ha : a ≠ 0) : ∃ f : R →ₐ[K] K, f a ≠ 0 := by
  let : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K) (B := R)
  have hn : a ∉ (⊥ : Ideal R).jacobson := by
    rw [IsJacobsonRing.out' _ Ideal.isRadical_bot]
    exact ha
  rw [Ideal.jacobson, Ideal.mem_sInf] at hn
  push Not at hn
  obtain ⟨M, ⟨_, hM⟩, haM⟩ := hn
  let : M.IsMaximal := hM
  let : Field (R ⧸ M) := Ideal.Quotient.field M
  let : Module.Finite K (R ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ M)
  let e : K ≃ₐ[K] R ⧸ M :=
    AlgEquiv.ofBijective (Algebra.ofId K (R ⧸ M)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K M), ?_⟩
  intro h
  apply haM
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  exact e.symm.injective (by simpa using h)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ClosedEvaluation
