import OAI.AlgebraicGeometry.Resolution.Blowups.LocalCurveBoundaryCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.MixedBoundaryCenterLift
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.TangentNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.Curve.IntrinsicStep

/-! # Coefficient Boundary Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CoefficientBoundaryCenter.Construction

noncomputable section

/-! A curve coefficient tangent center lifts with every transverse ambient boundary label. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem curve_coefficient_tangent_boundary_chart
    {k : Type u} [Field k] [IsAlgClosed k] (R : CommRingCat.{u})
    [Algebra k R] [Algebra ℚ R] [Algebra.Smooth k R]
    (z : R) (D : Derivation k R R) (hDz : D z = 1) (J : Ideal R) (b ℓ : ℕ)
    (hd : ringKrullDim (R ⧸ Ideal.span {z}) ≤ 1)
    {β : Type v} [Fintype β] (w : β → R)
    (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k (.of (R ⧸ Ideal.span {z}))
      (fun j => Ideal.Quotient.mk (Ideal.span {z}) (w j)))
    (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b) (ℓ + 1) = ⊤)
    (p : PrimeSpectrum R) (hp : Coefficient.TangentNaturality.Construction.coefficientTangentCenter k z J b ℓ ≤ p.asIdeal) :
    ∃ F : Finset β, Nonempty (MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R
      (Coefficient.TangentNaturality.Construction.coefficientTangentCenter k z J b ℓ) w F p) := by
  let Q := R ⧸ Ideal.span {z}
  let q : R →ₐ[k] Q := Ideal.Quotient.mkₐ k _
  let K := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b) ℓ
  have hker : RingHom.ker q.toRingHom ≤ p.asIdeal := (Ideal.comap_mono bot_le).trans hp
  let P : PrimeSpectrum Q := ⟨p.asIdeal.map q.toRingHom,
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker⟩
  have hP : PrimeSpectrum.comap q.toRingHom P = p := by
    apply PrimeSpectrum.ext
    change (p.asIdeal.map q.toRingHom).comap q.toRingHom = p.asIdeal
    rw [Ideal.comap_map_of_surjective q.toRingHom Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker]
  have hKP : K ≤ P.asIdeal := by
    change K ≤ p.asIdeal.map q.toRingHom
    rw [← Ideal.map_comap_of_surjective q.toRingHom Ideal.Quotient.mk_surjective K]
    exact Ideal.map_mono hp
  have hfirst : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k K = ⊤ :=
    (IntrinsicStep.Construction.first_iteratedRelativeDifferentialIdeal k (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b) ℓ).trans hbound
  obtain ⟨F, C⟩ := hboundary.curve_center_chart hd K hfirst P hKP
  obtain ⟨C⟩ := C
  exact ⟨F, Blowups.Quotient.MixedBoundaryCenterLift.Construction.quotient_mixed_boundary_center_chart_lifts R (.of Q) q Ideal.Quotient.mk_surjective
    z Ideal.mk_ker D hDz w K F p P hP C⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CoefficientBoundaryCenter.Construction
