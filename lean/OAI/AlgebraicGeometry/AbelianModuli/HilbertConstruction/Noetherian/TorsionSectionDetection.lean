import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.FramedGraphSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DetectedByLocalCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.DetectionByFamilies

/-! # Torsion Section Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Over a noetherian affine base, sufficiently high full torsion
detects actual graph-power sections without chosen bases or frames.
Local coefficient rings provide the complete framed bases, and module
localization detects the resulting global zero section. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
variable {g N n : ℕ} {δ : Fin g → ℕ} [NeZero n]
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem PolarizationData.PolarizedAbelianWithFullLevel.evenGraphPower_sectionsDetectedBy_fullLevel_noetherian
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
    (level : A.abelian.FullLevel n) (t : ℕ) (ht : 0 < t)
    (htlarge : Graph.EmbeddingNumerics.graphSquareSectionRank g δ ≤ t)
    (hlarge : EvenGraphTorsionBound.evenGraphTorsionDegree g δ t < n ^ 2) :
    Section.DetectionByFamilies.SectionsDetectedBy (A.graphBundle.tensorPower (2 * t)) (A.abelian.fullLevelGlobalSection level) := by
  have : CompactSpace A.abelian.scheme.left :=
    QuasiCompact.compactSpace_of_compactSpace A.abelian.scheme.hom
  have : A.abelian.scheme.left.IsSeparated :=
    ⟨by rw [← terminal.comp_from A.abelian.scheme.hom]; infer_instance⟩
  intro a ha
  apply DetectedByLocalCoefficients.section_eq_zero_of_localCoefficientPullbacks A.abelian.scheme.hom
    (A.graphBundle.tensorPower (2 * t)) a
  intro p _
  let C := Localization.AtPrime p
  let q := Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap Γ(S, ⊤) C)
  let B := A.pullback q
  let π := pullback.fst A.abelian.scheme.hom q
  let L := A.graphBundle.tensorPower (2 * t)
  let H : (L.pullback π).sheaf ≅ (B.graphBundle.tensorPower (2 * t)).sheaf :=
    A.graphBundle.powerBaseChangeIso π (2 * t) ≪≫
      (TensorPower.Maps.tensorPowerFunctor B.abelian.scheme.left (2 * t)).mapIso (A.graphBundle_baseChangeIso q).symm
  have : IsNoetherianRing Γ(Spec (.of C), ⊤) := isNoetherianRing_of_ringEquiv C
    (Scheme.ΓSpecIso (.of C)).commRingCatIsoToRingEquiv.symm
  have hq : IsUnit (N : Γ(Spec (.of C), ⊤)) := by
    simpa only [map_natCast] using hunit.map q.appTop.hom
  obtain ⟨F⟩ := B.local_exists_completeFramedEvenGraphSections hN hq (level.pullback q) t ht
  have hdet := PolarizationData.PolarizedAbelianWithFullLevel.CompleteFramedEvenGraphSections.detects B hg hδ hN hq
    (level.pullback q) t ht htlarge hlarge F
  have hz : (Ample.LineBundles.pullbackSection π a ≫ H.hom :
      Line.Bundles.structureModule B.abelian.scheme.left ⟶ (B.graphBundle.tensorPower (2 * t)).sheaf) = 0 := by
    apply hdet
    intro c
    let x := A.abelian.fullLevelGlobalSection level c
    let y := B.abelian.fullLevelGlobalSection (level.pullback q) c
    have hy : y ≫ π = q ≫ x := A.abelian.fullLevelGlobalSection_pullback level q c
    have hqx : Ample.LineBundles.pullbackSection (q ≫ x) a = 0 := by
      apply (Section.DetectionByFamilies.pullbackSection_comp_eq_zero_iff q x a).mpr
      rw [ha c]
      exact (BasisPullbackSectionSurjectivity.pullbackSectionAddHom q (L.pullback x).sheaf).map_zero
    have hyp : Ample.LineBundles.pullbackSection y (Ample.LineBundles.pullbackSection π a) = 0 := by
      apply (Section.DetectionByFamilies.pullbackSection_comp_eq_zero_iff y π a).mp
      rw [hy]
      exact hqx
    rw [Power.SectionTransitions.pullbackSection_postcomp, hyp, zero_comp]
  apply (cancel_mono H.hom).mp
  simpa only [zero_comp] using hz

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
