import OAI.AlgebraicGeometry.Resolution.Blowups.LocalCoordinatePrime
import OAI.AlgebraicGeometry.Resolution.Blowups.HypersurfaceDimension
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.Derivation
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoefficientStep
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Coordinate Local Parameter -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CoordinateLocalParameter.Construction

noncomputable section

/-! A coordinate through a closed point on a smooth curve is a local parameter. -/

universe u

theorem etale_curve_coordinate_local_maximalIdeal
    {σ k R : Type u} [Field k] [IsAlgClosed k] [CommRing R] [Finite σ] [DecidableEq σ]
    [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]
    (hd : ringKrullDim R ≤ 1) (i : σ) (q : Ideal R) [q.IsMaximal]
    (hi : algebraMap (MvPolynomial σ k) R (MvPolynomial.X i) ∈ q) :
    Ideal.span {algebraMap R (Localization.AtPrime q)
      (algebraMap (MvPolynomial σ k) R (MvPolynomial.X i))} =
        IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
  let A := Localization.AtPrime q
  let z := algebraMap (MvPolynomial σ k) R (MvPolynomial.X i)
  let z' := algebraMap R A z
  let : IsDomain A := Blowups.Etale.LocalDomain.Construction.etale_closed_localRing_isDomain (σ := σ) (K := k) q
  let : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr
    ((HypersurfaceDimension.Construction.localization_ringKrullDim_le (B := A) q.primeCompl).trans hd)
  let D := Blowups.Etale.LocalOrder.Construction.etalePolynomialCoordinateDerivation (K := k) (S := R) i
  have hD : D z = 1 := by
    exact (Blowups.Etale.CoefficientStep.Construction.etalePolynomialCoordinateDerivation_X (K := k) (S := R) i i).trans (ite_eq_left rfl)
  have hD' : Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := A) D z' = 1 := by
    rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, hD, map_one]
  have hz' : z' ≠ 0 := by
    intro h
    rw [h, map_zero] at hD'
    exact zero_ne_one hD'
  let P := Ideal.span {z'}
  let : P.IsPrime := LocalCoordinatePrime.Construction.etale_boundary_coordinate_atPrime_isPrime (K := k) i q hi
  rcases IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top (⟨P, inferInstance⟩ : PrimeSpectrum A) with h | h
  · have hP : P = ⊥ := congrArg PrimeSpectrum.asIdeal h
    have hz : z' ∈ P := Ideal.mem_span_singleton_self z'
    rw [hP] at hz
    exact False.elim (hz' ((Submodule.mem_bot A).mp hz))
  · exact congrArg PrimeSpectrum.asIdeal h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CoordinateLocalParameter.Construction
