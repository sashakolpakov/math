import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.BoundIndependence
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.TangentBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ComponentBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RefinementHelpers
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Coefficient Bound Independence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoefficientBoundIndependence.Construction

noncomputable section

/-! Normal-equation independence of coefficient differential bounds on every smooth affine algebra. -/

universe u

theorem smooth_coefficient_bound_of_other_normal
    (k : Type u) [Field k]
    {R : Type u} [CommRing R] [Algebra k R] [Algebra ℚ R] [Algebra.Smooth k R]
    (J : Ideal R) (n m : ℕ) (z t : R) (D E : Derivation k R R)
    (hD : D z = 1) (hE : E t = 1)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (ht : t ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)) m = ⊤) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k t (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)) m = ⊤ := by
  let : Algebra.Smooth k (R ⧸ Ideal.span {z}) := DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one D z hD
  let : Algebra.Smooth k (R ⧸ Ideal.span {t}) := DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one E t hE
  let H := Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n
  let L := Coefficient.TangentNaturality.Construction.coefficientTangentCenter k t H (n + 1) m
  by_contra hnot
  have hproper : L ≠ ⊤ := by
    intro he
    apply hnot
    have hq := Coefficient.TangentNaturality.Construction.coefficientTangentCenter_quotient k t H (n + 1) m
    change L.map (Ideal.Quotient.mk (Ideal.span {t})) = _ at hq
    rw [he, Ideal.map_top] at hq
    exact hq.symm
  obtain ⟨q, hq, hLq⟩ := Ideal.exists_le_maximal L hproper
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
  have hbz := Coefficient.TangentBaseChange.Construction.homogenized_coefficient_bound_map_etale k f hf z J n m hbound
  have hbt := Coefficient.BoundIndependence.Construction.coefficient_bound_of_other_normal (k := k) (R := S) (σ := ULift.{u} (Fin d))
    (J.map f.toRingHom) n m (f z) (f t) D' E' hD' hE' hz' ht' hbz
  have hm := Coefficient.TangentBaseChange.Construction.homogenized_coefficientTangentCenter_map_etale k f hf t J n m
  change L.map f.toRingHom = Coefficient.TangentNaturality.Construction.coefficientTangentCenter k (f t)
    (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k (J.map f.toRingHom) n) (n + 1) m at hm
  have hunit : L.map f.toRingHom = ⊤ := by
    rw [hm]
    unfold Coefficient.TangentNaturality.Construction.coefficientTangentCenter
    rw [hbt, Ideal.comap_top]
  obtain ⟨Q, hQ⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime s ⟨q, inferInstance⟩ hs
  have hle : L.map f.toRingHom ≤ Q.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    exact hLq.trans_eq (congrArg PrimeSpectrum.asIdeal hQ).symm
  rw [hunit] at hle
  exact Q.isPrime.ne_top (top_le_iff.mp hle)

theorem smooth_coefficient_bound_independent_of_normal
    (k : Type u) [Field k] {R : Type u} [CommRing R] [Algebra k R] [Algebra ℚ R] [Algebra.Smooth k R]
    (J : Ideal R) (n m : ℕ) (z t : R) (D E : Derivation k R R)
    (hD : D z = 1) (hE : E t = 1)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (ht : t ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)) m = ⊤ ↔
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k t (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)) m = ⊤ :=
  ⟨smooth_coefficient_bound_of_other_normal k J n m z t D E hD hE hz ht,
    smooth_coefficient_bound_of_other_normal k J n m t z E D hE hD ht hz⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoefficientBoundIndependence.Construction
