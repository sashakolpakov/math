import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CoverExpansion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CoverReindexing
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.EndpointOrders
import Mathlib.Data.Fin.Tuple.Basic

/-! # Polynomial Cover Expansion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.PolynomialCoverExpansion.ProjectiveCech

noncomputable section

/-! Prepending and appending a redundant homogeneous chart for covers indexed by `Fin`. -/

open _root_.MvPolynomial DirectSum

universe u v w

variable {τ : Type u} [Fintype τ] (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial τ R) M]
  [IsScalarTower R (MvPolynomial τ R) M]
variable (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := τ) R) ℳ]

theorem polynomialCover_cons_span_exact_iff {n : ℕ} (a : Fin n → MvPolynomial τ R)
    (ha : ∀ i, (a i).IsHomogeneous 1) (x : MvPolynomial τ R)
    (hx : x ∈ Submodule.span R (Set.range a)) (d : ℤ) (q : ℕ) :
    Polynomial.CoverModule.ProjectiveCech.polynomialCoverCechExactAt R (MvPolynomial τ R) M (Fin.cons x a) ℳ d q ↔
      Polynomial.CoverModule.ProjectiveCech.polynomialCoverCechExactAt R (MvPolynomial τ R) M a ℳ d q := by
  have h (i : Fin (n + 1)) : Linear.EndpointSubstitution.ProjectiveCech.prependFamily a x (EndpointOrders.finSuccWithBotOrderIso n i) =
      (Fin.cons x a : Fin (n + 1) → MvPolynomial τ R) i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · change Linear.EndpointSubstitution.ProjectiveCech.prependFamily a x (EndpointOrders.finSuccWithBotEquiv n 0) = x
      rw [EndpointOrders.finSuccWithBotEquiv_zero]
      rfl
    · change Linear.EndpointSubstitution.ProjectiveCech.prependFamily a x (EndpointOrders.finSuccWithBotEquiv n j.succ) = a j
      rw [EndpointOrders.finSuccWithBotEquiv_succ]
      rfl
  exact (Polynomial.CoverReindexing.ProjectiveCech.polynomialCover_ordered_exact_iff R (MvPolynomial τ R) M
    (EndpointOrders.finSuccWithBotOrderIso n) (Fin.cons x a) (Linear.EndpointSubstitution.ProjectiveCech.prependFamily a x) h ℳ d q).symm.trans
      (Polynomial.CoverExpansion.ProjectiveCech.polynomialCover_prepend_span_exact_iff R M ℳ a ha x hx d q)

theorem polynomialCover_snoc_span_exact_iff {n : ℕ} (a : Fin n → MvPolynomial τ R)
    (ha : ∀ i, (a i).IsHomogeneous 1) (x : MvPolynomial τ R)
    (hx : x ∈ Submodule.span R (Set.range a)) (d : ℤ) (q : ℕ) :
    Polynomial.CoverModule.ProjectiveCech.polynomialCoverCechExactAt R (MvPolynomial τ R) M (Fin.snoc a x) ℳ d q ↔
      Polynomial.CoverModule.ProjectiveCech.polynomialCoverCechExactAt R (MvPolynomial τ R) M a ℳ d q := by
  have h (i : Fin (n + 1)) : Linear.EndpointSubstitution.ProjectiveCech.appendFamily a x (EndpointOrders.finSuccWithTopOrderIso n i) =
      (Fin.snoc a x : Fin (n + 1) → MvPolynomial τ R) i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.snoc_last]
      change Linear.EndpointSubstitution.ProjectiveCech.appendFamily a x (EndpointOrders.finSuccWithTopEquiv n (Fin.last n)) = x
      rw [EndpointOrders.finSuccWithTopEquiv_last]
      rfl
    · rw [Fin.snoc_castSucc]
      change Linear.EndpointSubstitution.ProjectiveCech.appendFamily a x (EndpointOrders.finSuccWithTopEquiv n j.castSucc) = a j
      rw [EndpointOrders.finSuccWithTopEquiv_castSucc]
      rfl
  exact (Polynomial.CoverReindexing.ProjectiveCech.polynomialCover_ordered_exact_iff R (MvPolynomial τ R) M
    (EndpointOrders.finSuccWithTopOrderIso n) (Fin.snoc a x) (Linear.EndpointSubstitution.ProjectiveCech.appendFamily a x) h ℳ d q).symm.trans
      (Polynomial.CoverExpansion.ProjectiveCech.polynomialCover_append_span_exact_iff R M ℳ a ha x hx d q)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.PolynomialCoverExpansion.ProjectiveCech
