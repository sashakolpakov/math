import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CoverModule
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.EndpointSubstitution
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.CoverPreimage
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.TopLinearCoverExpansion
import Mathlib.Data.Fintype.WithTopBot

/-! # Cover Expansion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CoverExpansion.ProjectiveCech

noncomputable section

/-! Adding a linear combination to a finite homogeneous cover preserves its actual graded Čech exactness. -/

open _root_.MvPolynomial DirectSum

universe u v w t

variable {σ : Type u} {τ : Type w} [Fintype σ] [LinearOrder σ] [Fintype τ]
variable (R : Type v) [CommRing R]
variable (M : Type t) [AddCommGroup M] [Module R M] [Module (MvPolynomial τ R) M]
  [IsScalarTower R (MvPolynomial τ R) M]
variable (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := τ) R) ℳ]

theorem polynomialCover_prepend_exact_iff (a : σ → MvPolynomial τ R)
    (ha : ∀ i, (a i).IsHomogeneous 1) (l : MvPolynomial σ R) (hl : l.IsHomogeneous 1)
    (d : ℤ) (q : ℕ) :
    CoverModule.ProjectiveCech.polynomialCoverCechExactAt R (MvPolynomial τ R) M
        (Linear.EndpointSubstitution.ProjectiveCech.prependFamily a (MvPolynomial.aeval a l)) ℳ d q ↔
      CoverModule.ProjectiveCech.polynomialCoverCechExactAt R (MvPolynomial τ R) M a ℳ d q := by
  let b := Linear.EndpointSubstitution.ProjectiveCech.prependFamily a (MvPolynomial.aeval a l)
  have hb : ∀ i, (b i).IsHomogeneous 1 := by
    intro i
    by_cases hi : i = ⊥
    · subst i
      change (MvPolynomial.aeval a l).IsHomogeneous 1
      simpa only [one_mul] using hl.aeval a ha
    · obtain ⟨j, rfl⟩ := WithBot.ne_bot_iff_exists.mp hi
      exact ha j
  let f := Linear.EndpointSubstitution.ProjectiveCech.prependLinearSubstitution R l
  let := f.toRingHom.toAlgebra
  let := CoverModule.ProjectiveCech.polynomialCoverModule R (MvPolynomial τ R) M a
  let := CoverModule.ProjectiveCech.polynomialCoverModule R (MvPolynomial τ R) M b
  let := CoverModule.ProjectiveCech.polynomialCover_scalarTower R (MvPolynomial τ R) M a
  let := CoverModule.ProjectiveCech.polynomialCover_scalarTower R (MvPolynomial τ R) M b
  let := CoverModule.ProjectiveCech.polynomialCover_composition_tower R (MvPolynomial τ R) M a b f (Linear.EndpointSubstitution.ProjectiveCech.aeval_prependFamily R a l)
  let := CoverModule.ProjectiveCech.polynomialCover_gradedSMul R M ℳ a ha
  let := CoverModule.ProjectiveCech.polynomialCover_gradedSMul R M ℳ b hb
  change Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := WithBot σ) R M ℳ d q ↔ Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d q
  exact Linear.CoverExpansion.ProjectiveCech.linearCoverExpansion_moduleCechExactAt_iff R (Linear.EndpointSubstitution.ProjectiveCech.prependLinearSubstitution_coe R l)
    M l (Linear.EndpointSubstitution.ProjectiveCech.prependLinearSubstitution_bot R l) ℳ hl d q

theorem polynomialCover_append_exact_iff (a : σ → MvPolynomial τ R)
    (ha : ∀ i, (a i).IsHomogeneous 1) (l : MvPolynomial σ R) (hl : l.IsHomogeneous 1)
    (d : ℤ) (q : ℕ) :
    CoverModule.ProjectiveCech.polynomialCoverCechExactAt R (MvPolynomial τ R) M
        (Linear.EndpointSubstitution.ProjectiveCech.appendFamily a (MvPolynomial.aeval a l)) ℳ d q ↔
      CoverModule.ProjectiveCech.polynomialCoverCechExactAt R (MvPolynomial τ R) M a ℳ d q := by
  let b := Linear.EndpointSubstitution.ProjectiveCech.appendFamily a (MvPolynomial.aeval a l)
  have hb : ∀ i, (b i).IsHomogeneous 1 := by
    intro i
    by_cases hi : i = ⊤
    · subst i
      change (MvPolynomial.aeval a l).IsHomogeneous 1
      simpa only [one_mul] using hl.aeval a ha
    · obtain ⟨j, rfl⟩ := WithTop.ne_top_iff_exists.mp hi
      exact ha j
  let f := Linear.EndpointSubstitution.ProjectiveCech.appendLinearSubstitution R l
  let := f.toRingHom.toAlgebra
  let := CoverModule.ProjectiveCech.polynomialCoverModule R (MvPolynomial τ R) M a
  let := CoverModule.ProjectiveCech.polynomialCoverModule R (MvPolynomial τ R) M b
  let := CoverModule.ProjectiveCech.polynomialCover_scalarTower R (MvPolynomial τ R) M a
  let := CoverModule.ProjectiveCech.polynomialCover_scalarTower R (MvPolynomial τ R) M b
  let := CoverModule.ProjectiveCech.polynomialCover_composition_tower R (MvPolynomial τ R) M a b f (Linear.EndpointSubstitution.ProjectiveCech.aeval_appendFamily R a l)
  let := CoverModule.ProjectiveCech.polynomialCover_gradedSMul R M ℳ a ha
  let := CoverModule.ProjectiveCech.polynomialCover_gradedSMul R M ℳ b hb
  change Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := WithTop σ) R M ℳ d q ↔ Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := σ) R M ℳ d q
  exact TopLinearCoverExpansion.ProjectiveCech.topLinearCoverExpansion_moduleCechExactAt_iff R (Linear.EndpointSubstitution.ProjectiveCech.appendLinearSubstitution_coe R l)
    M l (Linear.EndpointSubstitution.ProjectiveCech.appendLinearSubstitution_top R l) ℳ hl d q

theorem polynomialCover_prepend_span_exact_iff (a : σ → MvPolynomial τ R)
    (ha : ∀ i, (a i).IsHomogeneous 1) (x : MvPolynomial τ R)
    (hx : x ∈ Submodule.span R (Set.range a)) (d : ℤ) (q : ℕ) :
    CoverModule.ProjectiveCech.polynomialCoverCechExactAt R (MvPolynomial τ R) M (Linear.EndpointSubstitution.ProjectiveCech.prependFamily a x) ℳ d q ↔
      CoverModule.ProjectiveCech.polynomialCoverCechExactAt R (MvPolynomial τ R) M a ℳ d q := by
  obtain ⟨l, hl, rfl⟩ := Linear.CoverPreimage.ProjectiveCech.exists_linear_cover_preimage R a x hx
  exact polynomialCover_prepend_exact_iff R M ℳ a ha l hl d q

theorem polynomialCover_append_span_exact_iff (a : σ → MvPolynomial τ R)
    (ha : ∀ i, (a i).IsHomogeneous 1) (x : MvPolynomial τ R)
    (hx : x ∈ Submodule.span R (Set.range a)) (d : ℤ) (q : ℕ) :
    CoverModule.ProjectiveCech.polynomialCoverCechExactAt R (MvPolynomial τ R) M (Linear.EndpointSubstitution.ProjectiveCech.appendFamily a x) ℳ d q ↔
      CoverModule.ProjectiveCech.polynomialCoverCechExactAt R (MvPolynomial τ R) M a ℳ d q := by
  obtain ⟨l, hl, rfl⟩ := Linear.CoverPreimage.ProjectiveCech.exists_linear_cover_preimage R a x hx
  exact polynomialCover_append_exact_iff R M ℳ a ha l hl d q

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CoverExpansion.ProjectiveCech
