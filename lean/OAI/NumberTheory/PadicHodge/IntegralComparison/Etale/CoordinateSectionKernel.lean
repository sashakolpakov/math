import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.SectionKernel
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.ConormalRank
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.LocalCoordinates

/-! # Coordinate Section Kernel -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateSectionKernel

noncomputable section

/-! Centered étale coordinates generate the actual section ideal
after a principal shrinking which contains the whole section. -/

universe u
open _root_.MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type u} {A : Type u} [CommRing A]
  [Algebra R A] [Algebra (MvPolynomial σ R) A]
  [IsScalarTower R (MvPolynomial σ R) A]
  [Algebra.Etale (MvPolynomial σ R) A] (ε : A →ₐ[R] R)

def point (i : σ) : R := ε (algebraMap (MvPolynomial σ R) A (X i))

def parameter (i : σ) : A :=
  algebraMap (MvPolynomial σ R) A (X i - C (point (σ := σ) ε i))

def ideal : Ideal A :=
  (AlgebraicGeometry.Resolution.Blowups.PolynomialTranslation.Construction.polynomialPointIdeal (point (σ := σ) ε)).map (algebraMap (MvPolynomial σ R) A)

omit [IsScalarTower R (MvPolynomial σ R) A] [Algebra.Etale (MvPolynomial σ R) A] in
theorem ideal_eq_span : ideal (σ := σ) ε = Ideal.span (Set.range (parameter (σ := σ) ε)) := by
  rw [ideal, AlgebraicGeometry.Resolution.Blowups.Etale.LocalCoordinates.Construction.polynomialPointIdeal_eq_span_coordinates, Ideal.map_span, ← Set.range_comp]
  rfl

omit [Algebra.Etale (MvPolynomial σ R) A] in
theorem parameter_eval (i : σ) : ε (parameter (σ := σ) ε i) = 0 := by
  change ε (algebraMap (MvPolynomial σ R) A (X i - C (point (σ := σ) ε i))) = 0
  rw [map_sub, map_sub]
  change point (σ := σ) ε i - ε (algebraMap (MvPolynomial σ R) A
    (algebraMap R (MvPolynomial σ R) (point (σ := σ) ε i))) = 0
  rw [← IsScalarTower.algebraMap_apply, ε.commutes]
  exact sub_self _

omit [Algebra.Etale (MvPolynomial σ R) A] in
theorem ideal_le_kernel : ideal (σ := σ) ε ≤ RingHom.ker ε.toRingHom := by
  rw [ideal_eq_span]
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact parameter_eval ε i

def evaluation (x : σ → R) : MvPolynomial σ R →ₐ[R] R where
  toRingHom := eval x
  commutes' r := by simp

def polynomialQuotientEquiv (x : σ → R) :
    (MvPolynomial σ R ⧸ AlgebraicGeometry.Resolution.Blowups.PolynomialTranslation.Construction.polynomialPointIdeal x) ≃ₐ[R] R :=
  Ideal.quotientKerAlgEquivOfSurjective
    (f := evaluation x) (fun r => ⟨C r, by simp [evaluation]⟩)

theorem quotient_etale : Algebra.Etale R (A ⧸ ideal (σ := σ) ε) := by
  let I := AlgebraicGeometry.Resolution.Blowups.PolynomialTranslation.Construction.polynomialPointIdeal (point (σ := σ) ε)
  let Q := MvPolynomial σ R ⧸ I
  let : Algebra.Etale R Q := Algebra.Etale.of_equiv (polynomialQuotientEquiv (point (σ := σ) ε)).symm
  let : Algebra Q (A ⧸ ideal (σ := σ) ε) := by
    change Algebra (MvPolynomial σ R ⧸ I) (A ⧸ I.map (algebraMap (MvPolynomial σ R) A))
    infer_instance
  let : Algebra.Etale Q (A ⧸ ideal (σ := σ) ε) := ConormalRank.quotient_etale I
  let : IsScalarTower R Q (A ⧸ ideal (σ := σ) ε) := AlgebraicGeometry.Resolution.Blowups.Smooth.TransformedCoordinateHypersurface.Construction.extendedQuotient_scalarTower I
  exact Algebra.Etale.comp R Q (A ⧸ ideal (σ := σ) ε)

def quotientEvaluation : (A ⧸ ideal (σ := σ) ε) →ₐ[R] R :=
  Ideal.Quotient.liftₐ (ideal (σ := σ) ε) ε (ideal_le_kernel (σ := σ) ε)

theorem exists_principal :
    ∃ s : A, ε s = 1 ∧ ∀ x, ε x = 0 → s * x ∈ Ideal.span (Set.range (parameter (σ := σ) ε)) := by
  let : Algebra.Etale R (A ⧸ ideal (σ := σ) ε) := quotient_etale (σ := σ) ε
  obtain ⟨u, hu, hann⟩ := SectionKernel.exists_annihilator (quotientEvaluation (σ := σ) ε)
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective u
  refine ⟨s, ?_, ?_⟩
  · have h := congrArg (quotientEvaluation (σ := σ) ε) hs
    exact h.trans hu
  · intro x hx
    rw [← ideal_eq_span]
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mk (ideal (σ := σ) ε) s * Ideal.Quotient.mk (ideal (σ := σ) ε) x = 0
    rw [hs]
    exact hann (Ideal.Quotient.mk (ideal (σ := σ) ε) x) hx

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateSectionKernel
