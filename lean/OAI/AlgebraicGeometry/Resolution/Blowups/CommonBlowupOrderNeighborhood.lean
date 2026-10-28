import OAI.AlgebraicGeometry.Resolution.Blowups.CommonBlowupChartMaps
import OAI.AlgebraicGeometry.Resolution.Blowups.ComparisonRatioTangentOpen
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ChartOverlapCover
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialMap

/-! # Common Blowup Order Neighborhood -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.CommonBlowupOrderNeighborhood.Construction

noncomputable section

/-! The genuine common chart covers every transformed order point on the first target chart. -/

universe u

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra Blowup.Overlap.Construction.blowupOverlapBaseAlgebra

theorem commonBlowupChart_covers_transformed_order
    (k : Type u) [CommRing k] {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Algebra.Smooth k R]
    (I J : Ideal R) (a : I) (n : ℕ) (hp : J ≤ I ^ (n + 1))
    (f g : R →ₐ[k] S) (hf : f.toRingHom.Etale)
    (K : Ideal S) (hKf : I.map f.toRingHom = K)
    (b c : K) (hb : b.val = f a.val) (hc : c.val = g a.val)
    (hdiff : ∀ r : R, g r - f r ∈ (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map f.toRingHom)
    (P : PrimeSpectrum (Blowup.Charts.Construction.blowupChart K b))
    (hP : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      (ControlledTransform.Construction.blowupControlledTransform K (J.map f.toRingHom) (n + 1) b) n ≤ P.asIdeal) :
    ∃ Q : PrimeSpectrum (Blowup.ChartOverlap.Construction.blowupChartOverlap K b c),
      PrimeSpectrum.comap (Blowup.ChartOverlap.Construction.blowupChartOverlapLeft K b c) Q = P := by
  have hp' : J.map f.toRingHom ≤ K ^ (n + 1) := by
    rw [← hKf, ← Ideal.map_pow]
    exact Ideal.map_mono hp
  have hbc : c.val - b.val ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J.map f.toRingHom) n := by
    rw [hb, hc, ← Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k f hf]
    exact hdiff a.val
  exact Blowup.ChartOverlapCover.Construction.exists_blowupChartOverlap_prime K b c P
    (ComparisonRatioTangentOpen.Construction.blowupChartRatio_not_mem_transformed_order_prime k K (J.map f.toRingHom) b c n hp' hbc P hP)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.CommonBlowupOrderNeighborhood.Construction
