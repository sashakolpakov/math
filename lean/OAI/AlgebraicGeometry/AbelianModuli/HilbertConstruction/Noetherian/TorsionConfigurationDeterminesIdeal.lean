import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.TorsionSectionDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.EmbeddedTorsionDetection

/-! # Torsion Configuration Determines Ideal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.TorsionConfigurationDeterminesIdeal

noncomputable section

/-! Sufficiently high auxiliary torsion sections determine the exact
saturated embedded Hilbert ideal over any noetherian coefficient ring.
No section basis or torsion fiber frame is part of the hypotheses. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {g N n r : ℕ} {δ : Fin g → ℕ} [NeZero n] {P : Polynomial ℚ}

theorem noetherianEmbeddedGraph_sectionsDetectedBy_fullLevel
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of R)))
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R r))
    (e : A.abelian.scheme ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I)
    (eL : ((ProjectiveTwisting.Bundle.projectiveTwistingBundle I 1).pullback e.hom.left).sheaf ≅
      (A.graphBundle.tensorPower (2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ)).sheaf)
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N)
    (hunit : IsUnit (N : Γ(Spec (.of R), ⊤)))
    (level : A.abelian.FullLevel n) (D d : ℕ) (hd : 0 < d) (hdD : d ≤ D)
    (hlarge : Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ D < n ^ 2) :
    Section.DetectionByFamilies.SectionsDetectedBy (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d)
      (fun c => A.abelian.fullLevelGlobalSection level c ≫ e.hom.left) := by
  have : IsNoetherianRing Γ(Spec (.of R), ⊤) := isNoetherianRing_of_ringEquiv R
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm
  have ht : 0 < Graph.EmbeddingNumerics.graphSquareSectionRank g δ * d :=
    Nat.mul_pos (Graph.EmbeddingNumerics.graphSquareSectionRank_pos g δ hδ) hd
  have htlarge : Graph.EmbeddingNumerics.graphSquareSectionRank g δ ≤ Graph.EmbeddingNumerics.graphSquareSectionRank g δ * d := by
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left (Graph.EmbeddingNumerics.graphSquareSectionRank g δ) (Nat.succ_le_of_lt hd)
  have hb : EvenGraphTorsionBound.evenGraphTorsionDegree g δ (Graph.EmbeddingNumerics.graphSquareSectionRank g δ * d) < n ^ 2 :=
    (Bounded.GraphTorsionSectionDetection.evenGraphTorsionDegree_mono g δ
      (Nat.mul_le_mul_left (Graph.EmbeddingNumerics.graphSquareSectionRank g δ) (hdD.trans (Nat.le_max_right 1 D)))).trans_lt hlarge
  exact Section.DetectionByFamilies.SectionsDetectedBy.of_schemeIso (A.abelian.fullLevelGlobalSection level)
    (A.evenGraphPower_sectionsDetectedBy_fullLevel_noetherian hg hδ hN hunit
      level _ ht htlarge hb) ((Over.forget _).mapIso e) (Affine.EmbeddedTorsionDetection.embeddedGraphTwistingPowerIsoOverRing A I e eL d)

theorem saturatedHilbertIdeal_eq_of_noetherianAuxiliaryTorsionConfiguration
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of R)))
    (I J : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal R r P)
    (eI : A.abelian.scheme ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal)
    (eJ : B.abelian.scheme ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily J.ideal)
    (LI : ((ProjectiveTwisting.Bundle.projectiveTwistingBundle I.ideal 1).pullback eI.hom.left).sheaf ≅
      (A.graphBundle.tensorPower (2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ)).sheaf)
    (LJ : ((ProjectiveTwisting.Bundle.projectiveTwistingBundle J.ideal 1).pullback eJ.hom.left).sheaf ≅
      (B.graphBundle.tensorPower (2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ)).sheaf)
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N)
    (hunit : IsUnit (N : Γ(Spec (.of R), ⊤)))
    (levelA : A.abelian.FullLevel n) (levelB : B.abelian.FullLevel n)
    (D : ℕ) (hD : 0 < D) (hdegree : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} r P ≤ D)
    (hlarge : Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ D < n ^ 2)
    (hpoints : ∀ c, A.abelian.fullLevelGlobalSection levelA c ≫ eI.hom.left ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal =
      B.abelian.fullLevelGlobalSection levelB c ≫ eJ.hom.left ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J.ideal) : I = J := by
  apply Family.ConfigurationDeterminesIdeal.saturatedHilbertIdeal_eq_of_detectingFamilyConfiguration I J D hdegree
    (fun c => A.abelian.fullLevelGlobalSection levelA c ≫ eI.hom.left)
    (fun c => B.abelian.fullLevelGlobalSection levelB c ≫ eJ.hom.left)
  · exact noetherianEmbeddedGraph_sectionsDetectedBy_fullLevel A I.ideal eI LI
      hg hδ hN hunit levelA D D hD le_rfl hlarge
  · exact noetherianEmbeddedGraph_sectionsDetectedBy_fullLevel B J.ideal eJ LJ
      hg hδ hN hunit levelB D D hD le_rfl hlarge
  · intro c
    exact (Category.assoc _ _ _).trans ((hpoints c).trans (Category.assoc _ _ _).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.TorsionConfigurationDeterminesIdeal
