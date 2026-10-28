import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveTwistingFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveCoordinate.GlobalSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.SectionCoordinateValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.EqualityAndPullbackValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.PullbackSectionZero

/-! # Coordinate Section Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.CoordinateSectionPullback

noncomputable section

/-! The twisting-bundle isomorphism for a section-defined projective map
sends each pulled-back homogeneous coordinate section to the defining section. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option cleanup.letToHave false
variable {X S : Scheme.{u}} {M : X.Modules} {n : ℕ} (f : X ⟶ S)
variable (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ M))
variable (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
variable (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading Γ(S, ⊤) n)) (m : X ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
variable (hm : m ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I = SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs)

private theorem recognition_generator {Y : Scheme.{u}} {κ : Type u}
    {V : κ → Y.Opens} (D : OpenFrame.Transitions.OpenFrameTransitions V) {P : Y.Modules}
    (E : CompatibleSheaf.CompatibleSheafFrames D P) (hV : ∀ x : Y, ∃ i, x ∈ V i)
    (W : Y.Opens) (i : κ) (hi : W ≤ V i) (r : Γ(Y, W)) :
    (Sheaf.FrameRecognition.openFrameSheafRecognitionIso D E hV).hom.app W (OpenFrame.SectionGenerators.openFrameGenerator D W i hi r) =
      E.frame W i hi r := by
  rw [Sheaf.FrameRecognition.openFrameSheafRecognitionIso, CompatibleSheaf.CompatibleSheafFrames.iso_app]
  change E.frame W i hi ((OpenFrame.LocalFreeness.openFrameLocalEquiv D W i hi).symm
    (OpenFrame.LocalFreeness.openFrameLocalEquiv D W i hi r)) = _
  exact congrArg (E.frame W i hi) ((OpenFrame.LocalFreeness.openFrameLocalEquiv D W i hi).symm_apply_apply r)

theorem sectionQuotientTwistingBundleIso_coordinate (j : Fin (n + 1)) :
    Ample.LineBundles.pullbackSection m (ProjectiveCoordinate.GlobalSections.projectiveCoordinateSection I j) ≫
      (Section.ProjectiveTwistingFrames.sectionQuotientTwistingBundleIso f s hs I m hm).hom = s j := by
  let D := ProjectiveTwisting.Bundle.projectiveTwistingTransitions I 1
  let E := Section.ProjectiveTwistingFrames.sectionQuotientTwistingFrames f s hs I m hm
  let U : ULift.{u} (Fin (n + 1)) → (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Opens :=
    fun i => ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i.down}
  let V := fun i => m ⁻¹ᵁ U i
  have hV : ∀ x : X, ∃ i, x ∈ V i :=
    PulledBackFrameTransitions.OpenFrameTransitions.pullback_cover m (ProjectiveTwisting.Bundle.projectiveTwistingCover I)
  apply Section.EqualityAndPullbackValues.moduleSection_eq_of_cover M V hV
  intro i
  let r := Coordinate.RatioSections.coordinateRatioSection I {i.down} i.down j (Finset.mem_singleton_self i.down)
  let c := OpenFrame.PullbackSheafMap.openFramePullbackComparison D m
  let e := Sheaf.FrameRecognition.openFrameSheafRecognitionIso (D.pullback m) E hV
  have hc : c.app (V i)
      ((Ample.LineBundles.pullbackSection m (ProjectiveCoordinate.GlobalSections.projectiveCoordinateSection I j)).app (V i) (1 : Γ(X, V i))) =
      OpenFrame.SectionGenerators.openFrameGenerator (D.pullback m) (V i) i le_rfl (m.app (U i) r) := by
    have h := OpenFrame.PullbackSectionZero.openFramePullbackSection_app_of_tuple D m (ProjectiveCoordinate.GlobalSections.projectiveCoordinateSection I j) i
    have htuple : OpenFrame.CoefficientSections.openFrameGlobalTupleMap D
        (Global.Sections.moduleSectionHomEquiv (ProjectiveTwisting.Bundle.projectiveTwistingBundle I 1).sheaf (ProjectiveCoordinate.GlobalSections.projectiveCoordinateSection I j)) i = r :=
      congrFun (ProjectiveCoordinate.GlobalSections.projectiveCoordinateSection_tuple I j) i
    exact h.trans (congrArg (fun t : Γ(Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I), U i) =>
      OpenFrame.SectionGenerators.openFrameGenerator (D.pullback m) (V i) i le_rfl (m.app (U i) t)) htuple)
  have he := recognition_generator (D.pullback m) E hV (V i) i le_rfl (m.app (U i) r)
  have hsi : V i ≤ Ample.LineBundles.sectionNonvanishing (s i.down) :=
    (Section.QuotientCoordinatePullback.sectionQuotient_coordinate_preimage f s hs I m hm i.down).le
  have hr : m.app (U i) r = Section.ComponentRatios.sectionComponentRatio (s i.down) (s j) (V i) hsi := by
    have h := Section.QuotientCoordinatePullback.sectionQuotient_coordinate_pullback f s hs I m hm i.down j (V i) le_rfl hsi
    change X.presheaf.map (𝟙 (.op (V i))) (m.app (U i) r) = _ at h
    simpa only [X.presheaf.map_id, CommRingCat.id_apply] using h
  change e.hom.app (V i) (c.app (V i)
    ((Ample.LineBundles.pullbackSection m (ProjectiveCoordinate.GlobalSections.projectiveCoordinateSection I j)).app (V i) (1 : Γ(X, V i)))) = _
  rw [hc, he, hr]
  exact (Section.LocalLinearFrames.sectionLocalFrameEquiv (s i.down) (V i) hsi).apply_symm_apply _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.CoordinateSectionPullback
