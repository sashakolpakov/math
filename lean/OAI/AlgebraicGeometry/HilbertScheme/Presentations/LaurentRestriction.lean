import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LaurentBasis

/-! # Laurent Restriction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.LaurentRestriction.ProjectiveCech

noncomputable section

/-! Restriction between projective chart localizations preserves Laurent monomials. -/

open _root_.MvPolynomial

universe u v

variable {σ : Type u} [Fintype σ] [DecidableEq σ]
variable (R : Type v) [CommRing R]

def extendExponent {s t : Finset σ} (h : s ⊆ t) (a : LaurentExponents.ProjectiveCech.LaurentExponent s) : LaurentExponents.ProjectiveCech.LaurentExponent t :=
  ⟨a.val, fun i hi => a.property i (fun his => hi (h his))⟩

omit [Fintype σ] in
theorem inversionExponent_sdiff {s t : Finset σ} (h : s ⊆ t) :
    LaurentExponents.ProjectiveCech.inversionExponent s + LaurentExponents.ProjectiveCech.inversionExponent (t \ s) = LaurentExponents.ProjectiveCech.inversionExponent t := by
  ext i
  simp only [Finsupp.add_apply, LaurentExponents.ProjectiveCech.inversionExponent_apply, Finset.mem_sdiff]
  by_cases hs : i ∈ s
  · simp [hs, h hs]
  · simp [hs]

omit [Fintype σ] in
theorem inversionMonomial_sdiff {s t : Finset σ} (h : s ⊆ t) :
    LaurentMonomials.ProjectiveCech.inversionMonomial R s * LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s) = LaurentMonomials.ProjectiveCech.inversionMonomial R t := by
  simp only [LaurentMonomials.ProjectiveCech.inversionMonomial, monomial_mul_monomial, one_mul, inversionExponent_sdiff h]

theorem numeratorExponent_extend {s t : Finset σ} (h : s ⊆ t) (a : LaurentExponents.ProjectiveCech.LaurentExponent s)
    (k : ℕ) (hk : LaurentExponents.ProjectiveCech.denominatorBound a ≤ k) :
    LaurentExponents.ProjectiveCech.numeratorExponent a k + k • LaurentExponents.ProjectiveCech.inversionExponent (t \ s) =
      LaurentExponents.ProjectiveCech.numeratorExponent (extendExponent h a) k := by
  have hb : LaurentExponents.ProjectiveCech.denominatorBound (extendExponent h a) ≤ k := hk
  ext i
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  have hi := congrArg (fun d : σ →₀ ℕ => (d i : ℤ)) (inversionExponent_sdiff h)
  simp only [Finsupp.add_apply, Nat.cast_add] at hi
  have he : (LaurentExponents.ProjectiveCech.numeratorExponent a k i : ℤ) + (k : ℤ) * (LaurentExponents.ProjectiveCech.inversionExponent (t \ s) i : ℤ) =
      (LaurentExponents.ProjectiveCech.numeratorExponent (extendExponent h a) k i : ℤ) := by
    rw [LaurentExponents.ProjectiveCech.numeratorExponent_cast a k hk, LaurentExponents.ProjectiveCech.numeratorExponent_cast _ k hb]
    change a.val i + (k : ℤ) * (LaurentExponents.ProjectiveCech.inversionExponent s i : ℤ) +
      (k : ℤ) * (LaurentExponents.ProjectiveCech.inversionExponent (t \ s) i : ℤ) =
      a.val i + (k : ℤ) * (LaurentExponents.ProjectiveCech.inversionExponent t i : ℤ)
    rw [← hi]
    ring
  exact_mod_cast he

omit [Fintype σ] in
theorem inversionMonomial_subset_isUnit {s t : Finset σ} (h : s ⊆ t) :
    IsUnit (algebraMap (MvPolynomial σ R) (LaurentMonomials.ProjectiveCech.ChartLocalization R t) (LaurentMonomials.ProjectiveCech.inversionMonomial R s)) := by
  apply isUnit_of_dvd_unit
    (map_dvd (algebraMap (MvPolynomial σ R) (LaurentMonomials.ProjectiveCech.ChartLocalization R t))
      ⟨LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s), (inversionMonomial_sdiff R h).symm⟩)
  exact IsLocalization.Away.algebraMap_isUnit (LaurentMonomials.ProjectiveCech.inversionMonomial R t)

def chartRestriction {s t : Finset σ} (h : s ⊆ t) :
    LaurentMonomials.ProjectiveCech.ChartLocalization R s →ₐ[R] LaurentMonomials.ProjectiveCech.ChartLocalization R t :=
  IsLocalization.Away.liftAlgHom (LaurentMonomials.ProjectiveCech.inversionMonomial R s)
    (f := IsScalarTower.toAlgHom R (MvPolynomial σ R) (LaurentMonomials.ProjectiveCech.ChartLocalization R t))
    (inversionMonomial_subset_isUnit R h)

omit [Fintype σ] in
theorem chartRestriction_algebraMap {s t : Finset σ} (h : s ⊆ t) (p : MvPolynomial σ R) :
    chartRestriction R h (algebraMap (MvPolynomial σ R) (LaurentMonomials.ProjectiveCech.ChartLocalization R s) p) =
      algebraMap (MvPolynomial σ R) (LaurentMonomials.ProjectiveCech.ChartLocalization R t) p :=
  IsLocalization.Away.lift_eq (LaurentMonomials.ProjectiveCech.inversionMonomial R s)
    (inversionMonomial_subset_isUnit R h) p

theorem chartRestriction_laurentMonomial {s t : Finset σ} (h : s ⊆ t) (a : LaurentExponents.ProjectiveCech.LaurentExponent s) :
    chartRestriction R h (LaurentMonomials.ProjectiveCech.laurentMonomial R a) = LaurentMonomials.ProjectiveCech.laurentMonomial R (extendExponent h a) := by
  let k := LaurentExponents.ProjectiveCech.denominatorBound a
  let φ := algebraMap (MvPolynomial σ R) (LaurentMonomials.ProjectiveCech.ChartLocalization R t)
  have hclear := congrArg (chartRestriction R h) (LaurentMonomials.ProjectiveCech.laurentMonomial_clear R a k le_rfl)
  rw [map_mul, chartRestriction_algebraMap, chartRestriction_algebraMap] at hclear
  have hn : monomial (LaurentExponents.ProjectiveCech.numeratorExponent a k) (1 : R) * LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s) ^ k =
      monomial (LaurentExponents.ProjectiveCech.numeratorExponent (extendExponent h a) k) 1 := by
    rw [LaurentMonomials.ProjectiveCech.inversionMonomial_pow, monomial_mul_monomial, one_mul, numeratorExponent_extend h a k le_rfl]
  have hg : LaurentMonomials.ProjectiveCech.inversionMonomial R s ^ k * LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s) ^ k =
      LaurentMonomials.ProjectiveCech.inversionMonomial R t ^ k := by rw [← mul_pow, inversionMonomial_sdiff R h]
  apply (IsLocalization.map_units (LaurentMonomials.ProjectiveCech.ChartLocalization R t) (LaurentMonomials.ProjectiveCech.chartDenominator R t k)).mul_right_inj.mp
  change φ (LaurentMonomials.ProjectiveCech.inversionMonomial R t ^ k) * _ = φ (LaurentMonomials.ProjectiveCech.inversionMonomial R t ^ k) * _
  rw [LaurentMonomials.ProjectiveCech.laurentMonomial_clear R (extendExponent h a) k le_rfl]
  calc
    φ (LaurentMonomials.ProjectiveCech.inversionMonomial R t ^ k) * chartRestriction R h (LaurentMonomials.ProjectiveCech.laurentMonomial R a) =
        φ (LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s) ^ k) *
          (φ (LaurentMonomials.ProjectiveCech.inversionMonomial R s ^ k) * chartRestriction R h (LaurentMonomials.ProjectiveCech.laurentMonomial R a)) := by
      rw [← hg, map_mul]
      ring
    _ = φ (LaurentMonomials.ProjectiveCech.inversionMonomial R (t \ s) ^ k) * φ (monomial (LaurentExponents.ProjectiveCech.numeratorExponent a k) 1) := by
      rw [hclear]
    _ = φ (monomial (LaurentExponents.ProjectiveCech.numeratorExponent (extendExponent h a) k) 1) := by
      rw [mul_comm, ← map_mul, hn]

theorem chartRestriction_refl (s : Finset σ) :
    chartRestriction R (Finset.Subset.refl s) = AlgHom.id R (LaurentMonomials.ProjectiveCech.ChartLocalization R s) := by
  apply AlgHom.toLinearMap_injective
  apply (LaurentBasis.ProjectiveCech.laurentBasis R s).ext
  intro a
  simp only [AlgHom.toLinearMap_apply, LaurentBasis.ProjectiveCech.laurentBasis_apply, chartRestriction_laurentMonomial,
    AlgHom.id_apply]
  rfl

theorem chartRestriction_comp {s t w : Finset σ} (hst : s ⊆ t) (htw : t ⊆ w) :
    (chartRestriction R htw).comp (chartRestriction R hst) = chartRestriction R (hst.trans htw) := by
  apply AlgHom.toLinearMap_injective
  apply (LaurentBasis.ProjectiveCech.laurentBasis R s).ext
  intro a
  simp only [AlgHom.toLinearMap_apply, AlgHom.comp_apply, LaurentBasis.ProjectiveCech.laurentBasis_apply,
    chartRestriction_laurentMonomial]
  rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.LaurentRestriction.ProjectiveCech
