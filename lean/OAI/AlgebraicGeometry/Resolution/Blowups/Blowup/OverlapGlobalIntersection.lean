import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ChartOverlap

/-! # Overlap Global Intersection -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.OverlapGlobalIntersection.Construction

noncomputable section

/-! Identify the explicit overlap maps with the actual intersection in the Rees blowup scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) (a b : I)

theorem blowupChartOverlap_global_commutes :
    Spec.map (CommRingCat.ofHom (ChartOverlap.Construction.blowupChartOverlapLeft I a b)) ≫
        Proj.awayι (ReesGrading.Construction.reesGrade I) (Charts.Construction.reesGenerator I a) (Charts.Construction.reesGenerator_mem I a) (by decide) =
      Spec.map (CommRingCat.ofHom (ChartOverlap.Construction.blowupChartOverlapRight I a b)) ≫
        Proj.awayι (ReesGrading.Construction.reesGrade I) (Charts.Construction.reesGenerator I b) (Charts.Construction.reesGenerator_mem I b) (by decide) := by
  unfold ChartOverlap.Construction.blowupChartOverlapLeft ChartOverlap.Construction.blowupChartOverlapRight
  rw [Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι]

/-- The explicit common localization is the actual scheme-theoretic
intersection of the two affine opens in the Rees blowup. -/
def blowupChartOverlapPullbackIso :
    Limits.pullback
      (Proj.awayι (ReesGrading.Construction.reesGrade I) (Charts.Construction.reesGenerator I a) (Charts.Construction.reesGenerator_mem I a) (by decide))
      (Proj.awayι (ReesGrading.Construction.reesGrade I) (Charts.Construction.reesGenerator I b) (Charts.Construction.reesGenerator_mem I b) (by decide)) ≅
        Spec (.of (ChartOverlap.Construction.blowupChartOverlap I a b)) :=
  Proj.pullbackAwayιIso (ReesGrading.Construction.reesGrade I) (Charts.Construction.reesGenerator_mem I a) (by decide)
    (Charts.Construction.reesGenerator_mem I b) (by decide) rfl

theorem blowupChartOverlapPullbackIso_left :
    (blowupChartOverlapPullbackIso I a b).hom ≫
        Spec.map (CommRingCat.ofHom (ChartOverlap.Construction.blowupChartOverlapLeft I a b)) = Limits.pullback.fst _ _ :=
  Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left _ _ _ _ _ _

theorem blowupChartOverlapPullbackIso_right :
    (blowupChartOverlapPullbackIso I a b).hom ≫
        Spec.map (CommRingCat.ofHom (ChartOverlap.Construction.blowupChartOverlapRight I a b)) = Limits.pullback.snd _ _ :=
  Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right _ _ _ _ _ _

theorem blowupChartOverlap_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (ChartOverlap.Construction.blowupChartOverlapLeft I a b)))
      (Spec.map (CommRingCat.ofHom (ChartOverlap.Construction.blowupChartOverlapRight I a b)))
      (Proj.awayι (ReesGrading.Construction.reesGrade I) (Charts.Construction.reesGenerator I a) (Charts.Construction.reesGenerator_mem I a) (by decide))
      (Proj.awayι (ReesGrading.Construction.reesGrade I) (Charts.Construction.reesGenerator I b) (Charts.Construction.reesGenerator_mem I b) (by decide)) := by
  apply IsPullback.of_iso_pullback ⟨blowupChartOverlap_global_commutes I a b⟩
    (blowupChartOverlapPullbackIso I a b).symm
  · rw [← blowupChartOverlapPullbackIso_left I a b, ← Category.assoc, Iso.symm_hom,
      Iso.inv_hom_id, Category.id_comp]
  · rw [← blowupChartOverlapPullbackIso_right I a b, ← Category.assoc, Iso.symm_hom,
      Iso.inv_hom_id, Category.id_comp]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.OverlapGlobalIntersection.Construction
