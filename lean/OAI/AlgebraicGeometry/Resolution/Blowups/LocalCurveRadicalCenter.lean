import OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CoordinateLocalParameter
import OAI.AlgebraicGeometry.Resolution.Blowups.Curve.DifferentialCenter

/-! # Local Curve Radical Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.LocalCurveRadicalCenter.Construction

noncomputable section

/-! A nonzero reduced center in a local integral curve is the reduced closed point. -/

theorem local_curve_radical_ideal_eq_maximalIdeal
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [Ring.KrullDimLE 1 R]
    (I : Ideal R) (hr : I.IsRadical) (hzero : I ≠ ⊥) (hproper : I ≠ ⊤) :
    I = IsLocalRing.maximalIdeal R := by
  apply le_antisymm (IsLocalRing.le_maximalIdeal hproper)
  rw [← hr.radical, Ideal.radical_eq_sInf]
  apply le_sInf
  intro P hP
  rcases IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top (⟨P, hP.2⟩ : PrimeSpectrum R) with h | h
  · have hPzero : P = ⊥ := congrArg PrimeSpectrum.asIdeal h
    exact False.elim (hzero (le_bot_iff.mp (hPzero ▸ hP.1)))
  · exact (congrArg PrimeSpectrum.asIdeal h).symm.le

end

end OAI.AlgebraicGeometry.Resolution.Blowups.LocalCurveRadicalCenter.Construction
