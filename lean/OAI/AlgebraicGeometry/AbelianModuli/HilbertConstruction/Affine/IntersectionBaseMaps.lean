import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.AffineIntersection

/-! # Intersection Base Maps -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.IntersectionBaseMaps

noncomputable section

/-! Every affine test over a coefficient spectrum comes from an
actual coefficient algebra. Transport through the resulting Over
isomorphism removes the chosen-algebra presentation from the Hilbert
intersection comparison. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem uniqueLift_precomp_iso_iff {𝒞 : Type u} [Category.{v} 𝒞]
    {U T X M : 𝒞} (e : U ≅ T) (j : X ⟶ M) [Mono j] (x : T ⟶ M) :
    (∃! a : T ⟶ X, a ≫ j = x) ↔ (∃! a : U ⟶ X, a ≫ j = e.hom ≫ x) := by
  constructor
  · rintro ⟨a, ha, _⟩
    have H : (e.hom ≫ a) ≫ j = e.hom ≫ x := by rw [Category.assoc, ha]
    exact ⟨e.hom ≫ a, H, fun b hb => (cancel_mono j).mp (hb.trans H.symm)⟩
  · rintro ⟨a, ha, _⟩
    have H : (e.inv ≫ a) ≫ j = x := by rw [Category.assoc, ha, e.inv_hom_id_assoc]
    exact ⟨e.inv ≫ a, H, fun b hb => (cancel_mono j).mp (hb.trans H.symm)⟩

@[instance_reducible]
def affineOverCoefficientAlgebra (R C : Type u) [CommRing R] [CommRing C]
    (f : Spec (.of C) ⟶ Spec (.of R)) : Algebra R C :=
  (Spec.preimage f).hom.toAlgebra

def affineOverCoefficientIso (R C : Type u) [CommRing R] [CommRing C]
    (f : Spec (.of C) ⟶ Spec (.of R)) :
    letI := affineOverCoefficientAlgebra R C f
    Over.mk f ≅ HilbertScheme.Presentations.Relative.AffinePoints.relativeAffineScheme (.of R) C := by
  letI := affineOverCoefficientAlgebra R C f
  refine Over.isoMk (Iso.refl _) ?_
  change (𝟙 (Spec (.of C))) ≫ Spec.map (Spec.preimage f) = f
  rw [Category.id_comp, Spec.map_preimage]

variable (R C : Type u) [CommRing R] [IsNoetherianRing R] [CommRing C] [IsNoetherianRing C]
variable {n m : ℕ} (i : Fin m) (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable (D : ℕ) (P : Polynomial ℚ)
variable (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
variable (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)
variable (f : Spec (.of C) ⟶ Spec (.of R))
variable (y : Over.mk f ⟶
  Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i (j.intersection k) D (Stable.ConfigurationLocus.configurationHilbertRank D P))

include hP hD

theorem affineHilbertIntersection_left_iff :
    (∃! a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P,
      a ≫ Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P =
        y ≫ Stable.RankIntersectionMaps.stableRankIntersectionLeftMap R i j k D (Stable.ConfigurationLocus.configurationHilbertRank D P)) ↔
    (∃! a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P,
      a ≫ Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i (j.intersection k) D P = y) := by
  let := affineOverCoefficientAlgebra R C f
  let e := affineOverCoefficientIso R C f
  have : Mono (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P) := Over.mono_of_mono_left _
  have : Mono (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i (j.intersection k) D P) := Over.mono_of_mono_left _
  rw [uniqueLift_precomp_iso_iff e.symm, uniqueLift_precomp_iso_iff e.symm]
  simpa only [Category.assoc, Iso.symm_hom] using Stable.AffineIntersection.stableAffineHilbertIntersection_left_iff R i j k D P hP hD (e.inv ≫ y)

theorem affineHilbertIntersection_right_iff :
    (∃! a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D P,
      a ≫ Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i k D P =
        y ≫ Stable.RankIntersectionMaps.stableRankIntersectionRightMap R i j k D (Stable.ConfigurationLocus.configurationHilbertRank D P)) ↔
    (∃! a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P,
      a ≫ Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i (j.intersection k) D P = y) := by
  let := affineOverCoefficientAlgebra R C f
  let e := affineOverCoefficientIso R C f
  have : Mono (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i k D P) := Over.mono_of_mono_left _
  have : Mono (Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i (j.intersection k) D P) := Over.mono_of_mono_left _
  rw [uniqueLift_precomp_iso_iff e.symm, uniqueLift_precomp_iso_iff e.symm]
  simpa only [Category.assoc, Iso.symm_hom] using Stable.AffineIntersection.stableAffineHilbertIntersection_right_iff R i j k D P hP hD (e.inv ≫ y)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.IntersectionBaseMaps
