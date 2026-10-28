import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.ProjectiveMap
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.ProductCharts

/-! # Projective Embedding -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.ProjectiveEmbedding.Construction

noncomputable section

/-! A closed embedding of the global blowup into a product with complex projective space. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {X : Scheme} {n : ℕ} {e : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n} [IsClosedImmersion e]
variable {I : X.IdealSheafData} (Q : ProjectiveMap.Construction.ProjectiveCenterEquations e I)
variable [IsIntegral X] [IsLocallyNoetherian X] (hI : I ≠ ⊥)
variable (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

/-- Pair the global coordinate map with the original blowup projection. -/
def globalBlowupProjectiveEmbedding :
    Data.Construction.globalBlowup I hI ⟶ pullback (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase Q.dimension) f :=
  pullback.lift (ProjectiveMap.Construction.globalBlowupProjectiveMap Q hI f) (Data.Construction.globalBlowupToBase I hI)
    (ProjectiveMap.Construction.globalBlowupProjectiveMap_over Q hI f)

theorem globalBlowupProjectiveEmbedding_fst :
    globalBlowupProjectiveEmbedding Q hI f ≫ pullback.fst _ _ = ProjectiveMap.Construction.globalBlowupProjectiveMap Q hI f :=
  pullback.lift_fst _ _ _

theorem globalBlowupProjectiveEmbedding_snd :
    globalBlowupProjectiveEmbedding Q hI f ≫ pullback.snd _ _ = Data.Construction.globalBlowupToBase I hI :=
  pullback.lift_snd _ _ _

omit [IsIntegral X] [IsLocallyNoetherian X] [LocallyOfFiniteType f] in
theorem projectiveCenterChartMap_over_affine (i : Fin (n + 1)) :
    ProjectiveMap.Construction.projectiveCenterChartMap Q f i ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase Q.dimension =
      ReesGrading.Construction.affineBlowupToSpec (I.ideal (ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e i)) ≫
        (ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e i).2.fromSpec ≫ f := by
  rw [ProjectiveMap.Construction.projectiveCenterChartMap, ReesProjectiveCoordinates.Construction.reesProjectiveCoordinateMap_over, Affine.ComplexNaturality.Construction.affineComplexScalars_spec]

omit [IsIntegral X] [IsLocallyNoetherian X] [LocallyOfFiniteType f] in
theorem projectiveCenterChartMap_pair_closed (i : Fin (n + 1)) :
    IsClosedImmersion (pullback.lift (ProjectiveMap.Construction.projectiveCenterChartMap Q f i)
      (ReesGrading.Construction.affineBlowupToSpec (I.ideal (ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e i)))
      (projectiveCenterChartMap_over_affine Q f i)) := by
  apply (Relative.ProductCharts.Construction.pair_isClosedImmersion_iff_of_base_eq (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase Q.dimension)
    (ProjectiveMap.Construction.projectiveCenterChartMap Q f i) (ReesGrading.Construction.affineBlowupToSpec (I.ideal (ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e i)))
    (Affine.ComplexNaturality.Construction.affineComplexScalars_spec f (ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e i))
    (ReesProjectiveCoordinates.Construction.reesProjectiveCoordinateMap_over _ (Affine.ComplexNaturality.Construction.affineComplexScalars f _) _
      (ProjectiveMap.Construction.projectiveCenterChartGenerator_span Q i))
    (projectiveCenterChartMap_over_affine Q f i)).mp
  exact ReesProjectiveCoordinates.Construction.reesProjectiveCoordinateMap_pair_isClosedImmersion _ _ _ _

/-- The global product map is a closed immersion, checked on the actual
base-change charts of its target. -/
theorem globalBlowupProjectiveEmbedding_isClosedImmersion :
    IsClosedImmersion (globalBlowupProjectiveEmbedding Q hI f) := by
  let p := Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase Q.dimension
  let U := ClosedProjectiveIdealGenerators.Construction.closedProjectiveAffineOpen e
  let j := fun i : Fin (n + 1) => Relative.ProductCharts.Construction.relativeProductChartMap p f (U i).2.fromSpec
  let : ∀ i, IsOpenImmersion (U i).2.fromSpec := fun i =>
    IsAffineOpen.isOpenImmersion_fromSpec (U i).2
  let : ∀ i, IsOpenImmersion (j i) := fun i =>
    Relative.ProductCharts.Construction.relativeProductChartMap_isOpenImmersion p f (U i).2.fromSpec
  have hrange (i : Fin (n + 1)) : (j i).opensRange = pullback.snd p f ⁻¹ᵁ (U i).1 := by
    have h := SupportedBlowupSmoothGluing.Construction.opensRange_of_open_pullback (j i) (pullback.snd p ((U i).2.fromSpec ≫ f))
      (pullback.snd p f) (U i).2.fromSpec (Relative.ProductCharts.Construction.relativeProductChart_isPullback p f (U i).2.fromSpec)
    exact h.trans (congrArg (fun V : X.Opens => pullback.snd p f ⁻¹ᵁ V)
      (U i).2.opensRange_fromSpec)
  let C : (pullback p f).OpenCover := Scheme.Cover.mkOfCovers (Fin (n + 1))
    (fun i => pullback p ((U i).2.fromSpec ≫ f)) j (by
      intro z
      have hz : pullback.snd p f z ∈ ⨆ i, (U i).1 := by
        rw [ProjectiveMap.Construction.closedProjectiveAffineOpen_iSup]
        trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
      refine ⟨i, ?_⟩
      change z ∈ (j i).opensRange
      rw [hrange]
      exact hi) (fun i => inferInstanceAs (IsOpenImmersion
        (Relative.ProductCharts.Construction.relativeProductChartMap p f (U i).2.fromSpec)))
  apply IsZariskiLocalAtTarget.of_openCover C
  intro i
  change Fin (n + 1) at i
  change IsClosedImmersion (pullback.snd (globalBlowupProjectiveEmbedding Q hI f) (j i))
  let l := pullback.lift (ProjectiveMap.Construction.projectiveCenterChartMap Q f i) (ReesGrading.Construction.affineBlowupToSpec (I.ideal (U i)))
    (projectiveCenterChartMap_over_affine Q f i)
  let : IsClosedImmersion l := projectiveCenterChartMap_pair_closed Q f i
  have hcomp : l ≫ j i = Data.Construction.globalBlowupChart I hI (U i) ≫ globalBlowupProjectiveEmbedding Q hI f := by
    apply pullback.hom_ext
    · rw [Category.assoc, Relative.ProductCharts.Construction.relativeProductChartMap_fst, pullback.lift_fst,
        Category.assoc, globalBlowupProjectiveEmbedding_fst, ProjectiveMap.Construction.globalBlowupProjectiveMap_chart]
    · rw [Category.assoc, Relative.ProductCharts.Construction.relativeProductChartMap_snd, pullback.lift_snd_assoc,
        Category.assoc, globalBlowupProjectiveEmbedding_snd, Data.Construction.globalBlowupChart_over]
  have houter : IsPullback (l ≫ pullback.snd p ((U i).2.fromSpec ≫ f))
      (Data.Construction.globalBlowupChart I hI (U i)) (U i).2.fromSpec
      (globalBlowupProjectiveEmbedding Q hI f ≫ pullback.snd p f) := by
    rw [pullback.lift_snd, globalBlowupProjectiveEmbedding_snd]
    exact (MapGluing.Construction.globalBlowup_affineSpec_isPullback I hI (U i)).flip
  have hleft := houter.of_right hcomp (Relative.ProductCharts.Construction.relativeProductChart_isPullback p f (U i).2.fromSpec).flip
  rw [← hleft.flip.isoPullback_inv_snd]
  infer_instance

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.ProjectiveEmbedding.Construction
