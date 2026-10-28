import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ComponentIndependence
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ComponentBaseChange
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Component Independence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ComponentIndependence.Construction

noncomputable section

/-! Independence of the component center on every smooth affine algebra, without a chosen coordinate presentation. -/

universe u

theorem smooth_coefficient_component_center_independent_of_normal
    (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
    {R : Type u} [CommRing R] [Algebra k R] [Algebra ℚ R] [Algebra.Smooth k R]
    (J : Ideal R) (n : ℕ) (z t : R) (D E : Derivation k R R)
    (hD : D z = 1) (hE : E t = 1)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (ht : t ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) :
    Coefficient.ComponentNaturality.Construction.coefficientComponentCenter k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) =
      Coefficient.ComponentNaturality.Construction.coefficientComponentCenter k t (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) := by
  let : Algebra.Smooth k (R ⧸ Ideal.span {z}) := DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one D z hD
  let : Algebra.Smooth k (R ⧸ Ideal.span {t}) := DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one E t hE
  let I := Coefficient.ComponentNaturality.Construction.coefficientComponentCenter k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)
  let L := Coefficient.ComponentNaturality.Construction.coefficientComponentCenter k t (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)
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
  have heq := Coefficient.ComponentIndependence.Construction.coefficient_component_center_independent_of_normal (k := k) (R := S) (σ := ULift.{u} (Fin d))
    (J.map f.toRingHom) n (f z) (f t) D' E' hD' hE' hz' ht'
  have hIL : I.map f.toRingHom = L.map f.toRingHom := by
    change (Coefficient.ComponentNaturality.Construction.coefficientComponentCenter k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)).map f.toRingHom =
      (Coefficient.ComponentNaturality.Construction.coefficientComponentCenter k t (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)).map f.toRingHom
    rw [Coefficient.ComponentBaseChange.Construction.homogenized_coefficientComponentCenter_map_etale k f hf,
      Coefficient.ComponentBaseChange.Construction.homogenized_coefficientComponentCenter_map_etale k f hf]
    exact heq
  obtain ⟨Q, hQ⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime s ⟨q, inferInstance⟩ hs
  exact ⟨S, inferInstance, f.toRingHom, f.toRingHom, Q.asIdeal, Q.isPrime,
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hf).1, congrArg PrimeSpectrum.asIdeal hQ, hIL, rfl⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ComponentIndependence.Construction
