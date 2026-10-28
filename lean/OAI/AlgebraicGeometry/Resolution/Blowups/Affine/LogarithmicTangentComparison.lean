import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.TangentCarrierComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.TangentCarrierBoundaryReindex
import OAI.AlgebraicGeometry.Resolution.Blowups.TangentCarrierInactiveBoundary
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.TransverseDirectionModIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ChartSupport

/-! # Logarithmic Tangent Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.LogarithmicTangentComparison.Construction

noncomputable section

/-! Logarithmic normal derivations construct full-boundary tangent comparisons through every order point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_affine_tangent_carrier_comparison_of_logarithmic_derivations
    {σ R : Type} [CommRing R] [Algebra ℂ R] [Algebra ℚ R] [Algebra.Smooth ℂ R]
    [Algebra (MvPolynomial σ ℂ) R] [Algebra.Etale (MvPolynomial σ ℂ) R]
    [IsScalarTower ℂ (MvPolynomial σ ℂ) R] [Fintype σ] [DecidableEq σ]
    (J : Ideal R) (B : Finset σ) (z t : R) (n : ℕ) (p : PrimeSpectrum R)
    (hp : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ J n ≤ p.asIdeal)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ J n) (ht : t ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ J n)
    (D E : Derivation ℂ R R) (hDz : D z = 1) (hEt : E t = 1)
    (hDB : ∀ i ∈ B, D (algebraMap (MvPolynomial σ ℂ) R (MvPolynomial.X i)) ∈
      Ideal.span {algebraMap (MvPolynomial σ ℂ) R (MvPolynomial.X i)})
    (hEB : ∀ i ∈ B, E (algebraMap (MvPolynomial σ ℂ) R (MvPolynomial.X i)) ∈
      Ideal.span {algebraMap (MvPolynomial σ ℂ) R (MvPolynomial.X i)}) :
    Nonempty (TangentCarrierBoundaryReindex.Construction.TangentCarrierComparisonAt (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ J n))
      (QuotientKernel.Construction.affineQuotientKernel (Ideal.span {z})) (QuotientKernel.Construction.affineQuotientKernel (Ideal.span {t}))
      (fun i : B => QuotientKernel.Construction.affineQuotientKernel (Ideal.span {algebraMap (MvPolynomial σ ℂ) R (MvPolynomial.X i.val)})) n p) := by
  classical
  let w := fun i : σ => algebraMap (MvPolynomial σ ℂ) R (MvPolynomial.X i)
  let Bp := B.filter (fun i => w i ∈ p.asIdeal)
  have hD : ∀ i ∈ Bp, D (w i) ∈ p.asIdeal := by
    intro i hi
    obtain ⟨hiB, hi⟩ := Finset.mem_filter.mp hi
    exact ((Ideal.span_singleton_le_iff_mem p.asIdeal).mpr hi) (hDB i hiB)
  have hE : ∀ i ∈ Bp, E (w i) ∈ p.asIdeal := by
    intro i hi
    obtain ⟨hiB, hi⟩ := Finset.mem_filter.mp hi
    exact ((Ideal.span_singleton_le_iff_mem p.asIdeal).mpr hi) (hEB i hiB)
  have hDz' : D z ∉ p.asIdeal := by
    rw [hDz]
    exact fun h1 => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  have hEt' : E t ∉ p.asIdeal := by
    rw [hEt]
    exact fun h1 => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  obtain ⟨A⟩ := TangentCarrierComparison.Construction.exists_affine_tangent_carrier_comparison J Bp z t n p hp hz ht
    (Blowups.Etale.TransverseDirectionModIdeal.Construction.exists_transverse_partial_mod_ideal Bp D p.asIdeal z hD hDz')
    (Blowups.Etale.TransverseDirectionModIdeal.Construction.exists_transverse_partial_mod_ideal Bp E p.asIdeal t hE hEt')
  let F : Finset B := Finset.univ.filter (fun i => w i.val ∈ p.asIdeal)
  let e : F → Bp := fun i => ⟨i.val.val,
    Finset.mem_filter.mpr ⟨i.val.property, (Finset.mem_filter.mp i.property).2⟩⟩
  let G := fun i : B => QuotientKernel.Construction.affineQuotientKernel (Ideal.span {w i.val})
  have A' : TangentCarrierBoundaryReindex.Construction.TangentCarrierComparisonAt (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ J n))
      (QuotientKernel.Construction.affineQuotientKernel (Ideal.span {z})) (QuotientKernel.Construction.affineQuotientKernel (Ideal.span {t}))
      (fun i : F => G i.val) n p := A.reindex e
  apply A'.exists_with_inactive_boundary G F
  · rw [ComplexAffineDifferentialIdeal.Construction.smoothDifferentialIdealSheaf_affineQuotientKernel, HomogenizationTangent.Construction.relativeHomogenizedIdeal_tangent]
    change p ∈ ((QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ J n)).support : Set (Spec (.of R)))
    rw [Coefficient.ChartSupport.Construction.affineQuotientKernel_support]
    exact hp
  · intro i hi
    have hi' : w i.val ∉ p.asIdeal := by
      simpa only [F, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    change p ∉ ((QuotientKernel.Construction.affineQuotientKernel (Ideal.span {w i.val})).support : Set (Spec (.of R)))
    rw [Coefficient.ChartSupport.Construction.affineQuotientKernel_support]
    exact fun h => hi' (h (Ideal.mem_span_singleton_self _))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.LogarithmicTangentComparison.Construction
