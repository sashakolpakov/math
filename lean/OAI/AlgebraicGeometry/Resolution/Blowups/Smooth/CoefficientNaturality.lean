import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.IntervalNaturality

/-! # Coefficient Naturality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoefficientNaturality.Construction

noncomputable section

/-! Coordinate-independent compatibility of retained coefficient intervals with étale refinement. -/

variable (k : Type*) {R S : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [Algebra.Smooth k R]

section AlgebraMap

variable [Algebra R S] [IsScalarTower k R S] [Algebra.FormallyEtale R S]

theorem smooth_relativeCoefficientIdeal_baseChange (z : R) (J : Ideal R) (b : ℕ) :
    (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b).map (Relative.CoefficientBaseChange.Construction.mappedHypersurfaceQuotientMap (algebraMap R S) z) =
      Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k (algebraMap R S z) (J.map (algebraMap R S)) b := by
  unfold Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal
  rw [WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal_map]
  apply congrArg (WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b)
  funext j
  rw [Ideal.map_map]
  change (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val).map
      ((Ideal.Quotient.mk (Ideal.span {algebraMap R S z})).comp (algebraMap R S)) = _
  rw [← Ideal.map_map, DifferentialNaturality.Construction.smooth_iteratedRelativeDifferentialIdeal_baseChange k J j.val]

end AlgebraMap

theorem smooth_relativeCoefficientIdeal_map (f : R →ₐ[k] S) (hf : f.toRingHom.Etale)
    (z : R) (J : Ideal R) (b : ℕ) :
    (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b).map (Relative.CoefficientBaseChange.Construction.mappedHypersurfaceQuotientMap f.toRingHom z) =
      Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k (f z) (J.map f.toRingHom) b := by
  let : Algebra R S := f.toRingHom.toAlgebra
  let : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  let : Algebra.Etale R S := RingHom.etale_algebraMap.mp hf
  exact smooth_relativeCoefficientIdeal_baseChange k z J b

/-- Both ends of the retained coefficient interval survive refinement of
any smooth affine algebra, with the same fixed generating family. -/
theorem smooth_coefficient_family_interval_map {ι : Type*}
    (f : R →ₐ[k] S) (hf : f.toRingHom.Etale)
    (D : Derivation k R R) (E : Derivation k S S) (hD : ∀ x : R, E (f x) = f (D x))
    (z : R) (p : ι → R) (b : ℕ) (C : Ideal (R ⧸ Ideal.span {z}))
    (hlow : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal D z p b ≤ C)
    (hupp : C ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Ideal.span (Set.range p)) b) :
    WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal E (f z) (fun t => f (p t)) b ≤
        C.map (Relative.CoefficientBaseChange.Construction.mappedHypersurfaceQuotientMap f.toRingHom z) ∧
      C.map (Relative.CoefficientBaseChange.Construction.mappedHypersurfaceQuotientMap f.toRingHom z) ≤
        Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k (f z) (Ideal.span (Set.range (fun t => f (p t)))) b := by
  have hfamily := WeightedFamilyNaturality.Construction.weightedCoordinateDerivativeFamilyIdeal_map D E f.toRingHom hD z p b
  have hrelative := smooth_relativeCoefficientIdeal_map k f hf z (Ideal.span (Set.range p)) b
  have hp : (Ideal.span (Set.range p)).map f.toRingHom =
      Ideal.span (Set.range (fun t => f (p t))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [hp] at hrelative
  exact ⟨hfamily.symm.le.trans (Ideal.map_mono hlow), (Ideal.map_mono hupp).trans hrelative.le⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoefficientNaturality.Construction
