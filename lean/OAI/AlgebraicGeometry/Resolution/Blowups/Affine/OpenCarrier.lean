import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.CarrierBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ChartSupport

/-! # Open Carrier -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.OpenCarrier.Construction

noncomputable section

/-! A nonempty affine restriction of an integral native carrier is integral. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem affine_open_carrier_isIntegral
    {X : Scheme.{0}} (H : X.IdealSheafData) [IsIntegral H.subscheme]
    (R : CommRingCat) (j : Spec R ⟶ X) [IsOpenImmersion j]
    (K : Ideal R) (he : H.comap j = QuotientKernel.Construction.affineQuotientKernel K)
    (p : PrimeSpectrum R) (hp : K ≤ p.asIdeal) : IsIntegral (QuotientKernel.Construction.affineQuotientKernel K).subscheme := by
  have hs := congrArg (fun I : (Spec R).IdealSheafData => (I.support : Set (Spec R))) he
  rw [Scheme.IdealSheafData.support_comap, Coefficient.ChartSupport.Construction.affineQuotientKernel_support] at hs
  change j ⁻¹' (H.support : Set X) = PrimeSpectrum.zeroLocus K at hs
  have hx : j p ∈ H.support :=
    (congrArg (fun s : Set (PrimeSpectrum R) => p ∈ s) hs).to_iff.mpr hp
  have h := IdealSheaf.CarrierBaseChange.Construction.idealSheaf_comap_subscheme_isIntegral H j p hx
  rwa [he] at h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.OpenCarrier.Construction
