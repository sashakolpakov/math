import OAI.AlgebraicGeometry.Resolution.Blowups.WeightedFamilyNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.CoefficientFamilyInterval
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.QuotientNaturality

/-! # Interval Naturality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.IntervalNaturality.Construction

noncomputable section

/-! Both bounds in coefficient induction survive étale chart refinements. -/

universe u

variable {σ k R V : Type u} [Field k] [CommRing R] [CommRing V]
  [Algebra k R] [Algebra k V] [Algebra (MvPolynomial σ k) R]
  [Algebra.Etale (MvPolynomial σ k) R] [IsScalarTower k (MvPolynomial σ k) R]
  [Fintype σ] [DecidableEq σ]

include σ in
/-- The fixed-family lower bound and intrinsic upper bound are both retained
when the chart is refined and its normal derivative is extended compatibly. -/
theorem relative_coefficient_family_interval_map {ι : Type*}
    (f : R →ₐ[k] V) (hf : f.toRingHom.Etale)
    (D : Derivation k R R) (E : Derivation k V V) (hD : ∀ x : R, E (f x) = f (D x))
    (z : R) (p : ι → R) (b : ℕ) (C : Ideal (R ⧸ Ideal.span {z}))
    (hlow : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal D z p b ≤ C)
    (hupp : C ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Ideal.span (Set.range p)) b) :
    WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal E (f z) (fun t => f (p t)) b ≤
        C.map (Relative.CoefficientBaseChange.Construction.mappedHypersurfaceQuotientMap f.toRingHom z) ∧
      C.map (Relative.CoefficientBaseChange.Construction.mappedHypersurfaceQuotientMap f.toRingHom z) ≤
        Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k (f z) (Ideal.span (Set.range (fun t => f (p t)))) b := by
  have hfamily := WeightedFamilyNaturality.Construction.weightedCoordinateDerivativeFamilyIdeal_map D E f.toRingHom hD z p b
  have hrelative : (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Ideal.span (Set.range p)) b).map
      (Relative.CoefficientBaseChange.Construction.mappedHypersurfaceQuotientMap f.toRingHom z) =
      Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k (f z) ((Ideal.span (Set.range p)).map f.toRingHom) b :=
    Blowups.Etale.QuotientNaturality.Construction.relativeCoefficientIdeal_map_aligned_etale (σ := σ) f hf z (f z) rfl (Ideal.span (Set.range p)) b
  have hp : (Ideal.span (Set.range p)).map f.toRingHom =
      Ideal.span (Set.range (fun t => f (p t))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [hp] at hrelative
  exact ⟨hfamily.symm.le.trans (Ideal.map_mono hlow), (Ideal.map_mono hupp).trans hrelative.le⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.IntervalNaturality.Construction
