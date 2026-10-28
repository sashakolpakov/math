import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NormalizedFamilyTransport

/-! # Polarization Overlap Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationOverlapCriterion.StableHilbertPolarization

noncomputable section

/-! The original normalized-polarization lifting criterion on stable overlaps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (qR : Spec (.of R) ⟶ Spec (.of ℚ))
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ k, 0 < δ k)
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m)

theorem overlap_lifts_iff
    {T : Over (Spec (.of R))} [IsLocallyNoetherian T.left]
    (t : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D H)
    (u : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels)
    (hu : u ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels =
      t ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD)
    (v : T ⟶ LevelParameter.StableHilbertLevel.parameter R i k D H hH g Hm Hi N labels)
    (hv : v ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i k D H hH g Hm Hi N labels =
      t ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD) :
    (∃ a : T ⟶ PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ,
      a ≫ PolarizationParameter.StableHilbertPolarization.inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ = u) ↔
    (∃ a : T ⟶ PolarizationParameter.StableHilbertPolarization.parameter R i k D H hH g Hm Hi N labels qR d hd δ hδ,
      a ≫ PolarizationParameter.StableHilbertPolarization.inclusion R i k D H hH g Hm Hi N labels qR d hd δ hδ = v) := by
  rw [PolarizationParameter.StableHilbertPolarization.lifts_iff, PolarizationParameter.StableHilbertPolarization.lifts_iff]
  exact NormalizedFamilyTransport.StableHilbertFullLevelOriginalRecovery.enhancement_nonempty_iff
    R i D H hH hD g Hm Hi N labels j k t u hu v hv δ d

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationOverlapCriterion.StableHilbertPolarization
