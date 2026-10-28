import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwoStagePresentation

/-! # Negative Presentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.NegativePresentation

noncomputable section

/-! Actual coherent sheaves admit two-stage negative-twist presentations
whose exponents all exceed any prescribed bound. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_presentation_above
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (j : σ) (B : ℕ) :
    ∃ P : AlgebraicGeometry.SheafCohomology.Projective.TwoStagePresentation.MvPolynomial.CoordinateNegativeTwistPresentation j M,
      (∀ k, B ≤ P.rowDegree k) ∧ (∀ l, B ≤ P.columnDegree l) := by
  classical
  obtain ⟨r, d, f, hd, hf⟩ := AlgebraicGeometry.SheafCohomology.Projective.BoundedNegativeQuotient.MvPolynomial.exists_fin_fixedCoordinateNegativeTwist_quotient_above M j B
  let Q := ∐ fun k : Fin r => AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d k)
  have : Q.IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_quasicoherent j d
  have : Q.IsFiniteType := AlgebraicGeometry.SheafCohomology.Projective.TwoStagePresentation.MvPolynomial.negativeTwistCoproduct_finiteType j d
  have : LocallyOfFiniteType (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) :=
    AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ_locallyOfFiniteType
  have : IsLocallyNoetherian (Proj (homogeneousSubmodule σ R)) :=
    LocallyOfFiniteType.isLocallyNoetherian (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
  have : (kernel f).IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_kernel f
  have : (kernel f).IsFiniteType := AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isFiniteType_kernel f
  let D := max B (Finset.univ.sup d)
  obtain ⟨s, e, p, he, hp⟩ := AlgebraicGeometry.SheafCohomology.Projective.BoundedNegativeQuotient.MvPolynomial.exists_fin_fixedCoordinateNegativeTwist_quotient_above (kernel f) j D
  have : Epi p := hp
  let g := p ≫ kernel.ι f
  have hg : g ≫ f = 0 := by simp [g]
  have hex : (ShortComplex.mk g f hg).Exact := by
    rw [ShortComplex.exact_iff_epi_kernel_lift]
    have heq : kernel.lift f g hg = p := by
      apply (cancel_mono (kernel.ι f)).mp
      simp [g]
    rw [heq]
    infer_instance
  refine ⟨{ rows := r
            columns := s
            rowDegree := d
            columnDegree := e
            projection := f
            relations := g
            epi := hf
            zero := hg
            exact := hex
            degree_order := ?_ }, hd, ?_⟩
  · intro k l
    exact (Finset.le_sup (f := d) (Finset.mem_univ k)).trans ((le_max_right B _).trans (he l))
  · intro l
    exact (le_max_left B _).trans (he l)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.NegativePresentation
