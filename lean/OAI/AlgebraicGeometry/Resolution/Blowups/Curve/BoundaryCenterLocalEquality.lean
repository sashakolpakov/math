import OAI.AlgebraicGeometry.Resolution.Blowups.LocalCurveRadicalCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CenterPointedFrame
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.PrincipalEquations

/-! # Boundary Center Local Equality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Curve.BoundaryCenterLocalEquality.Construction

noncomputable section

/-! At a boundary point of a smooth curve, the intrinsic reduced center agrees with its boundary coordinate. -/

universe u

theorem etale_curve_center_local_eq_coordinate
    {σ k R : Type u} [Field k] [IsAlgClosed k] [CommRing R] [Algebra k R] [Algebra ℚ R]
    [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]
    [IsScalarTower k (MvPolynomial σ k) R] [Finite σ] [DecidableEq σ]
    (hd : ringKrullDim R ≤ 1) (I : Ideal R) (hI : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k I = ⊤)
    (q : Ideal R) [q.IsMaximal] (hIq : I ≤ q) (i : σ)
    (hi : algebraMap (MvPolynomial σ k) R (MvPolynomial.X i) ∈ q) :
    I.map (algebraMap R (Localization.AtPrime q)) =
      Ideal.span {algebraMap R (Localization.AtPrime q)
        (algebraMap (MvPolynomial σ k) R (MvPolynomial.X i))} := by
  let A := Localization.AtPrime q
  let : Algebra.Smooth k (MvPolynomial σ k) := ⟨inferInstance, inferInstance⟩
  let : Algebra.Smooth k R := Algebra.Smooth.comp k (MvPolynomial σ k) R
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let : IsDomain A := Blowups.Etale.LocalDomain.Construction.etale_closed_localRing_isDomain (σ := σ) (K := k) q
  let : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr
    ((HypersurfaceDimension.Construction.localization_ringKrullDim_le (B := A) q.primeCompl).trans hd)
  have hr : (I.map (algebraMap R A)).IsRadical := by
    have h := DifferentialCenter.Construction.curve_center_radical_of_first_differential_top k hd I hI
    rw [← h.radical, IsLocalization.map_radical q.primeCompl A I]
    exact Ideal.radical_isRadical _
  have hzero : I.map (algebraMap R A) ≠ ⊥ := by
    intro hz
    obtain ⟨D, z, hDz⟩ := CenterPointedFrame.Construction.exists_derivative_outside_center_prime k I q hIq hI
    have hzA : algebraMap R A z.val = 0 := by
      exact Ideal.mem_bot.mp (hz ▸ Ideal.mem_map_of_mem (algebraMap R A) z.property)
    have hDzA : algebraMap R A (D z.val) = 0 := by
      rw [← Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap (S := A), hzA, map_zero]
    exact (IsLocalization.map_units A (⟨D z.val, hDz⟩ : q.primeCompl)).ne_zero hDzA
  have hproper : I.map (algebraMap R A) ≠ ⊤ := by
    intro ht
    have hle := Ideal.map_mono (f := algebraMap R A) hIq
    rw [ht, IsLocalization.AtPrime.map_eq_maximalIdeal] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_le_iff.mp hle)
  exact (LocalCurveRadicalCenter.Construction.local_curve_radical_ideal_eq_maximalIdeal (I.map (algebraMap R A)) hr hzero hproper).trans
    (CoordinateLocalParameter.Construction.etale_curve_coordinate_local_maximalIdeal hd i q hi).symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Curve.BoundaryCenterLocalEquality.Construction
