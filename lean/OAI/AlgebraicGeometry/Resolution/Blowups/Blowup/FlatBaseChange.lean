import OAI.AlgebraicGeometry.Resolution.Blowups.ChartFlatBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.BaseOpen
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Cover
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Flat Base Change -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.FlatBaseChange.Construction

noncomputable section

/-! Flat base change of the actual affine Rees blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

theorem reesGradedMap_generator (I : Ideal R) (φ : R →+* S) (a : I) :
    ReesMap.Construction.reesGradedMap I φ (Charts.Construction.reesGenerator I a) =
      Charts.Construction.reesGenerator (I.map φ) ⟨φ a.val, Ideal.mem_map_of_mem φ a.property⟩ :=
  ReesMap.Construction.reesRingMap_generator I φ a

/-- The explicit coefficient chart map is the restriction of the Proj map. -/
theorem affineBlowupMap_chart (I : Ideal R) (φ : R →+* S) (a : I) :
    Spec.map (CommRingCat.ofHom (ChartLift.Construction.blowupChartMap I φ a)) ≫
        Proj.awayι (ReesGrading.Construction.reesGrade I) (Charts.Construction.reesGenerator I a) (Charts.Construction.reesGenerator_mem I a) (by decide) =
      Proj.awayι (ReesGrading.Construction.reesGrade (I.map φ))
          (Charts.Construction.reesGenerator (I.map φ) ⟨φ a.val, Ideal.mem_map_of_mem φ a.property⟩)
          (Charts.Construction.reesGenerator_mem (I.map φ) _) (by decide) ≫ ReesMap.Construction.affineBlowupMap I φ := by
  have h := Proj.awayι_comp_map (ReesMap.Construction.reesGradedMap I φ) (ReesMap.Construction.reesGradedMap_irrelevant_le I φ)
    (show 0 < (1 : ℕ) by decide) (Charts.Construction.reesGenerator I a) (Charts.Construction.reesGenerator_mem I a)
  have haux (s : reesAlgebra (I.map φ)) (hs : s ∈ ReesGrading.Construction.reesGrade (I.map φ) 1)
      (he : ReesMap.Construction.reesGradedMap I φ (Charts.Construction.reesGenerator I a) = s)
      (hle : Submonoid.powers (Charts.Construction.reesGenerator I a) ≤ (Submonoid.powers s).comap (ReesMap.Construction.reesGradedMap I φ)) :
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.map (ReesMap.Construction.reesGradedMap I φ) hle)) ≫
          Proj.awayι (ReesGrading.Construction.reesGrade I) (Charts.Construction.reesGenerator I a) (Charts.Construction.reesGenerator_mem I a) (by decide) =
        Proj.awayι (ReesGrading.Construction.reesGrade (I.map φ)) s hs (by decide) ≫ ReesMap.Construction.affineBlowupMap I φ := by
    subst s
    exact h.symm
  apply haux _ _ (reesGradedMap_generator I φ a)

/-- The mapped chart is exactly the inverse image of its target chart. -/
theorem affineBlowupMap_chart_isPullback (I : Ideal R) (φ : R →+* S) (a : I) :
    IsPullback (Spec.map (CommRingCat.ofHom (ChartLift.Construction.blowupChartMap I φ a)))
      (Proj.awayι (ReesGrading.Construction.reesGrade (I.map φ))
        (Charts.Construction.reesGenerator (I.map φ) ⟨φ a.val, Ideal.mem_map_of_mem φ a.property⟩)
        (Charts.Construction.reesGenerator_mem (I.map φ) _) (by decide))
      (Proj.awayι (ReesGrading.Construction.reesGrade I) (Charts.Construction.reesGenerator I a) (Charts.Construction.reesGenerator_mem I a) (by decide))
      (ReesMap.Construction.affineBlowupMap I φ) := by
  apply IsOpenImmersion.isPullback
  · exact (affineBlowupMap_chart I φ a).symm
  · rw [Proj.opensRange_awayι, Proj.opensRange_awayι]
    exact (Proj.map_preimage_basicOpen (ReesMap.Construction.reesGradedMap I φ) (ReesMap.Construction.reesGradedMap_irrelevant_le I φ)
      (Charts.Construction.reesGenerator I a)).trans (congrArg _ (reesGradedMap_generator I φ a))

/-- Flat scalar extension commutes with the actual affine blowup scheme. -/
theorem affineBlowup_flat_isPullback [Algebra R S] [Module.Flat R S] (I : Ideal R) :
    IsPullback (ReesMap.Construction.affineBlowupMap I (algebraMap R S))
      (ReesGrading.Construction.affineBlowupToSpec (I.map (algebraMap R S))) (ReesGrading.Construction.affineBlowupToSpec I)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let 𝒰 := (Cover.Construction.affineBlowupAffineCover I).openCover
  apply Scheme.isPullback_of_openCover _ _ _ _ 𝒰
  intro a
  change I at a
  let b : I.map (algebraMap R S) := ⟨algebraMap R S a.val, Ideal.mem_map_of_mem _ a.property⟩
  let jR := Proj.awayι (ReesGrading.Construction.reesGrade I) (Charts.Construction.reesGenerator I a) (Charts.Construction.reesGenerator_mem I a) (by decide)
  let jS := Proj.awayι (ReesGrading.Construction.reesGrade (I.map (algebraMap R S)))
    (Charts.Construction.reesGenerator (I.map (algebraMap R S)) b) (Charts.Construction.reesGenerator_mem (I.map (algebraMap R S)) b)
    (by decide)
  let c := Spec.map (CommRingCat.ofHom (ChartLift.Construction.blowupChartMap I (algebraMap R S) a))
  have hchart : IsPullback c jS jR (ReesMap.Construction.affineBlowupMap I (algebraMap R S)) :=
    affineBlowupMap_chart_isPullback I (algebraMap R S) a
  have houter : IsPullback c (jS ≫ ReesGrading.Construction.affineBlowupToSpec (I.map (algebraMap R S)))
      (jR ≫ ReesGrading.Construction.affineBlowupToSpec I) (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    dsimp only [jR, jS, c]
    rw [Charts.Construction.affineBlowup_chart_structureMap, Charts.Construction.affineBlowup_chart_structureMap]
    exact ChartFlatBaseChange.Construction.blowupChart_flat_isPullback I a
  change IsPullback
    (Limits.pullback.snd (ReesMap.Construction.affineBlowupMap I (algebraMap R S)) jR)
    (Limits.pullback.fst (ReesMap.Construction.affineBlowupMap I (algebraMap R S)) jR ≫
      ReesGrading.Construction.affineBlowupToSpec (I.map (algebraMap R S)))
    (jR ≫ ReesGrading.Construction.affineBlowupToSpec I) (Spec.map (CommRingCat.ofHom (algebraMap R S)))
  apply houter.of_iso hchart.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id]
    exact hchart.flip.isoPullback_hom_snd.symm
  · simp only [Iso.refl_hom, Category.comp_id]
    exact (hchart.flip.isoPullback_hom_fst_assoc _).symm
  · simp
  · simp

/-- An étale change of base induces an étale map between the actual blowups. -/
theorem affineBlowupMap_etale [Algebra R S] [Algebra.Etale R S] (I : Ideal R) :
    Etale (ReesMap.Construction.affineBlowupMap I (algebraMap R S)) := by
  have hbase : Etale (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact (RingHom.etale_algebraMap (R := R) (S := S)).mpr inferInstance
  exact MorphismProperty.of_isPullback (P := @Etale) (affineBlowup_flat_isPullback I).flip hbase

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.FlatBaseChange.Construction
