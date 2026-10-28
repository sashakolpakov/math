import OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CoefficientTangentIndependence
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.TangentBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.NormalQuotientDimension
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ComponentBaseChange
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Surface Tangent Independence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.SurfaceTangentIndependence.Construction

noncomputable section

/-! Fixed-level coefficient tangent centers on smooth surfaces are independent of arbitrary normal equations. -/

universe u

theorem smooth_surface_coefficient_tangent_center_independent_of_normal
    (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    {R : Type u} [CommRing R] [Algebra k R] [Algebra ℚ R] [Algebra.Smooth k R]
    (J : Ideal R) (n ℓ : ℕ) (z t : R) (D E : Derivation k R R)
    (hD : D z = 1) (hE : E t = 1)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (ht : t ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (hdim : ringKrullDim R ≤ 2) (hlevel : (n + 1).factorial ≤ ℓ + 1)
    (hboundz : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)) (ℓ + 1) = ⊤)
    (hboundt : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k t (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)) (ℓ + 1) = ⊤) :
    Coefficient.TangentNaturality.Construction.coefficientTangentCenter k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) ℓ =
      Coefficient.TangentNaturality.Construction.coefficientTangentCenter k t (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) ℓ := by
  let : Algebra.Smooth k (R ⧸ Ideal.span {z}) := DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one D z hD
  let : Algebra.Smooth k (R ⧸ Ideal.span {t}) := DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one E t hE
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let I := Coefficient.TangentNaturality.Construction.coefficientTangentCenter k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) ℓ
  let L := Coefficient.TangentNaturality.Construction.coefficientTangentCenter k t (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) ℓ
  apply Pointed.ComparisonGluing.Construction.ideal_eq_of_pointed_flat_comparisons I L
  intro q hq
  let : q.IsMaximal := hq
  obtain ⟨s, hs, d, pAlg, htor, het⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := q)
  let S := Localization.Away s
  let : Algebra (MvPolynomial (Fin d) k) S := pAlg
  let : IsScalarTower k (MvPolynomial (Fin d) k) S := htor
  let : Algebra.IsStandardEtale (MvPolynomial (Fin d) k) S := het
  let : Algebra.Etale R S := Algebra.Etale.of_isLocalizationAway s
  let f : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
  have hf : f.toRingHom.Etale := RingHom.etale_algebraMap.mpr inferInstance
  let D' := Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) D
  let E' := Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) E
  have hD' : D' (f z) = 1 := by
    change Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) D (algebraMap R S z) = 1
    rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, hD, map_one]
  have hE' : E' (f t) = 1 := by
    change Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) E (algebraMap R S t) = 1
    rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, hE, map_one]
  have hT := DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k f hf J n
  have hz' : f z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J.map f.toRingHom) n := by
    rw [← hT]
    exact Ideal.mem_map_of_mem _ hz
  have ht' : f t ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J.map f.toRingHom) n := by
    rw [← hT]
    exact Ideal.mem_map_of_mem _ ht
  let P := MvPolynomial (Fin d) k
  let ε := MvPolynomial.renameEquiv k (Equiv.ulift : ULift.{u} (Fin d) ≃ Fin d)
  let φ := (algebraMap P S).comp ε.toRingHom
  have hφ : φ.Etale := RingHom.Etale.stableUnderComposition ε.toRingHom (algebraMap P S)
    (RingHom.Etale.of_bijective ε.bijective) (RingHom.etale_algebraMap.mpr inferInstance)
  have hφk (c : k) : φ (MvPolynomial.C c) = algebraMap k S c := by
    change algebraMap P S (MvPolynomial.rename (Equiv.ulift : ULift.{u} (Fin d) ≃ Fin d) (MvPolynomial.C c)) = _
    rw [MvPolynomial.rename_C]
    exact (IsScalarTower.algebraMap_apply k P S c).symm
  let : Algebra (MvPolynomial (ULift.{u} (Fin d)) k) S := φ.toAlgebra
  let : IsScalarTower k (MvPolynomial (ULift.{u} (Fin d)) k) S :=
    IsScalarTower.of_algebraMap_eq (fun c => (hφk c).symm)
  let : Algebra.Etale (MvPolynomial (ULift.{u} (Fin d)) k) S := RingHom.etale_algebraMap.mp hφ
  have hdS : ringKrullDim S ≤ 2 := (HypersurfaceDimension.Construction.localization_ringKrullDim_le (B := S) (Submonoid.powers s)).trans hdim
  have hdz' : ringKrullDim (S ⧸ Ideal.span {f z}) ≤ 1 := NormalQuotientDimension.Construction.normal_quotient_dimension_induction D' (f z) hD' 1 hdS
  have hdt' : ringKrullDim (S ⧸ Ideal.span {f t}) ≤ 1 := NormalQuotientDimension.Construction.normal_quotient_dimension_induction E' (f t) hE' 1 hdS
  have hbz' := Coefficient.TangentBaseChange.Construction.homogenized_coefficient_bound_map_etale k f hf z J n (ℓ + 1) hboundz
  have hbt' := Coefficient.TangentBaseChange.Construction.homogenized_coefficient_bound_map_etale k f hf t J n (ℓ + 1) hboundt
  have heq := Curve.CoefficientTangentIndependence.Construction.curve_coefficient_tangent_center_independent_of_normal (k := k) (R := S) (σ := ULift.{u} (Fin d))
    (J.map f.toRingHom) n ℓ (f z) (f t) D' E' hD' hE' hz' ht' hdz' hdt' hlevel hbz' hbt'
  have hIL : I.map f.toRingHom = L.map f.toRingHom := by
    change (Coefficient.TangentNaturality.Construction.coefficientTangentCenter k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) ℓ).map f.toRingHom =
      (Coefficient.TangentNaturality.Construction.coefficientTangentCenter k t (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) ℓ).map f.toRingHom
    rw [Coefficient.TangentBaseChange.Construction.homogenized_coefficientTangentCenter_map_etale k f hf,
      Coefficient.TangentBaseChange.Construction.homogenized_coefficientTangentCenter_map_etale k f hf]
    exact heq
  obtain ⟨Q, hQ⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime s ⟨q, inferInstance⟩ hs
  exact ⟨S, inferInstance, f.toRingHom, f.toRingHom, Q.asIdeal, Q.isPrime,
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hf).1, congrArg PrimeSpectrum.asIdeal hQ, hIL, rfl⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.SurfaceTangentIndependence.Construction
