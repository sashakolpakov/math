import OAI.AlgebraicGeometry.Resolution.Blowups.IntrinsicAffineTangentComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.TangentCarrierBoundaryReindex
import OAI.AlgebraicGeometry.Resolution.Blowups.ComplexAffineDifferentialIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.HomogenizationTangent

/-! # Tangent Carrier Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.TangentCarrierComparison.Construction

noncomputable section

/-! Actual pointed carrier comparison data are constructed from two transverse affine tangent equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_affine_tangent_carrier_comparison
    {σ R : Type} [CommRing R] [Algebra ℂ R] [Algebra ℚ R] [Algebra.Smooth ℂ R]
    [Algebra (MvPolynomial σ ℂ) R] [Algebra.Etale (MvPolynomial σ ℂ) R]
    [IsScalarTower ℂ (MvPolynomial σ ℂ) R] [Fintype σ] [DecidableEq σ]
    (J : Ideal R) (B : Finset σ) (z t : R) (n : ℕ) (p : PrimeSpectrum R)
    (hp : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ J n ≤ p.asIdeal)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ J n) (ht : t ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ J n)
    (htransz : ∃ i : σ, i ∉ B ∧ Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := ℂ) (S := R) i z ∉ p.asIdeal)
    (htranst : ∃ i : σ, i ∉ B ∧ Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := ℂ) (S := R) i t ∉ p.asIdeal) :
    Nonempty (TangentCarrierBoundaryReindex.Construction.TangentCarrierComparisonAt (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure R) (QuotientKernel.Construction.affineQuotientKernel (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal ℂ J n))
      (QuotientKernel.Construction.affineQuotientKernel (Ideal.span {z})) (QuotientKernel.Construction.affineQuotientKernel (Ideal.span {t}))
      (fun i : B => QuotientKernel.Construction.affineQuotientKernel (Ideal.span {algebraMap (MvPolynomial σ ℂ) R (MvPolynomial.X i.val)})) n p) := by
  obtain ⟨S, algS, a, b, ha, hb, haf, hbf, hJ, hH, hB, hc, q, hq, _⟩ :=
    IntrinsicAffineTangentComparison.Construction.exists_native_affine_tangent_comparison J B z t n p hp hz ht htransz htranst
  refine ⟨{ ambient := Spec S
            left := a
            right := b
            left_etale := ha
            right_etale := hb
            ground := haf.trans hbf.symm
            ideal := hJ
            carrier := hH
            boundary := fun i => hB i.val i.property
            congruence := ?_
            point := q
            point_eq := hq }⟩
  rw [ComplexAffineDifferentialIdeal.Construction.smoothDifferentialIdealSheaf_affineQuotientKernel, HomogenizationTangent.Construction.relativeHomogenizedIdeal_tangent]
  exact hc

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.TangentCarrierComparison.Construction
