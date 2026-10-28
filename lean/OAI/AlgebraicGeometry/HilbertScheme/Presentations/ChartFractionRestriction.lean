import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.FractionDegrees

/-! # Chart Fraction Restriction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ChartFractionRestriction.ProjectiveCech

noncomputable section

/-! Restriction of a polynomial fraction to a larger projective chart. -/

open _root_.MvPolynomial

universe u v

variable {σ : Type u} [Fintype σ] [DecidableEq σ]
variable (R : Type v) [CommRing R]

omit [Fintype σ] in
theorem extendExponent_ofNumerator {s t : Finset σ} (h : s ⊆ t) (d : σ →₀ ℕ) (k : ℕ) :
    LaurentRestriction.ProjectiveCech.extendExponent h (LaurentExponents.ProjectiveCech.exponentOfNumerator s d k) =
      LaurentExponents.ProjectiveCech.exponentOfNumerator t (d + k • LaurentExponents.ProjectiveCech.inversionExponent (t \ s)) k := by
  apply Subtype.ext
  funext i
  change (d i : ℤ) - (k : ℤ) * (LaurentExponents.ProjectiveCech.inversionExponent s i : ℤ) =
    ((d + k • LaurentExponents.ProjectiveCech.inversionExponent (t \ s)) i : ℤ) - (k : ℤ) * (LaurentExponents.ProjectiveCech.inversionExponent t i : ℤ)
  have hi := congrArg (fun e : σ →₀ ℕ => (e i : ℤ)) (LaurentRestriction.ProjectiveCech.inversionExponent_sdiff h)
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, Nat.cast_add, Nat.cast_mul] at hi ⊢
  rw [← hi]
  ring

theorem chartRestriction_fraction_monomial {s t : Finset σ} (h : s ⊆ t) (k : ℕ) (d : σ →₀ ℕ) :
    LaurentRestriction.ProjectiveCech.chartRestriction R h (LaurentBasis.ProjectiveCech.chartFractionLinearMap R s k (monomial d 1)) =
      LaurentBasis.ProjectiveCech.chartFractionLinearMap R t k (monomial d 1 * LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s) ^ k) := by
  rw [LaurentMonomials.ProjectiveCech.inversionMonomial_pow, monomial_mul_monomial, one_mul, LaurentBasis.ProjectiveCech.chartFractionLinearMap_apply,
    ← LaurentMonomials.ProjectiveCech.laurentMonomial_ofNumerator, LaurentRestriction.ProjectiveCech.chartRestriction_laurentMonomial,
    LaurentBasis.ProjectiveCech.chartFractionLinearMap_apply, ← LaurentMonomials.ProjectiveCech.laurentMonomial_ofNumerator, extendExponent_ofNumerator]

theorem chartRestriction_fraction {s t : Finset σ} (h : s ⊆ t) (k : ℕ) (p : MvPolynomial σ R) :
    LaurentRestriction.ProjectiveCech.chartRestriction R h (LaurentBasis.ProjectiveCech.chartFractionLinearMap R s k p) =
      LaurentBasis.ProjectiveCech.chartFractionLinearMap R t k (p * LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s) ^ k) := by
  have he : (LaurentRestriction.ProjectiveCech.chartRestriction R h).toLinearMap.comp (LaurentBasis.ProjectiveCech.chartFractionLinearMap R s k) =
      (LaurentBasis.ProjectiveCech.chartFractionLinearMap R t k).comp (LinearMap.mulRight R (LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s) ^ k)) := by
    apply (basisMonomials σ R).ext
    intro d
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, coe_basisMonomials,
      LinearMap.mulRight_apply]
    exact chartRestriction_fraction_monomial R h k d
  exact LinearMap.congr_fun he p

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ChartFractionRestriction.ProjectiveCech
