import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.MorphismOpenFrame
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.CoordinateProjectivePoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.CoordinatesOver
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.CoefficientNaturality

/-! # Scalar Coordinate Coverage -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ScalarCoordinateCoverage.StableHilbertCoverage

noncomputable section

/-! Normalized scalar coordinates of the original relative projective
point agree with the actual affine projective coordinate map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

private theorem sectionAbsoluteMorphism_of_frame
    {X S : Scheme.{u}} {M : X.Modules} {n : ℕ}
    (f : X ⟶ S) (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ M))
    (hs : ∀ x : X, ∃ k, x ∈ Ample.LineBundles.sectionNonvanishing (s k))
    (i : Fin (n + 1)) [IsIso (s i)] :
    SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs =
      ProjectiveChart.Evaluation.projectiveChartMap f.appTop.hom (fun k => Frame.Coordinates.frameCoordinate (s i) (s k)) i
        (Frame.Coordinates.frameCoordinate_self (s i)) := by
  apply (cancel_epi X.topIso.hom).mp
  change (⊤ : X.Opens).ι ≫ SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs =
    (⊤ : X.Opens).ι ≫ ProjectiveChart.Evaluation.projectiveChartMap _ _ _ _
  rw [Section.MorphismOpenFrame.sectionAbsoluteMorphism_on_open_frame f s hs (⊤ : X.Opens) i,
    ProjectiveChart.Naturality.projectiveChartMap_comp]
  exact Framed.ProjectiveMaps.projectiveChartMap_congr_coefficients rfl
    (funext fun k => Scalar.BaseChange.frameCoordinate_baseChange (⊤ : X.Opens).ι (s i) (s k)) i _ _

theorem scalarCoordinate_absolute_normalized
    {S : Scheme.{u}} {n : ℕ} (v : Fin (n + 1) → Γ(S, ⊤))
    (hv : ∀ x : S, ∃ k, x ∈ S.basicOpen (v k))
    (i : Fin (n + 1)) (hi : v i = 1) :
    SectionsProjectiveMorphism.sectionAbsoluteMorphism (𝟙 S) (Family.SectionProjectiveCoordinates.scalarCoordinateSections v)
        (Family.SectionProjectiveCoordinates.scalarCoordinateSections_cover v hv) =
      ProjectiveChart.Evaluation.projectiveChartMap (RingHom.id Γ(S, ⊤)) v i hi := by
  have hsi : Family.SectionProjectiveCoordinates.scalarCoordinateSections v i = 𝟙 (Line.Bundles.structureModule S) := by
    change (Global.Sections.structureModuleEndRingEquiv S).symm (v i) = _
    rw [hi]
    exact (Global.Sections.structureModuleEndRingEquiv S).symm.map_one
  let : IsIso (Family.SectionProjectiveCoordinates.scalarCoordinateSections v i) := hsi.symm ▸ inferInstance
  have hc : (fun k => Frame.Coordinates.frameCoordinate (Family.SectionProjectiveCoordinates.scalarCoordinateSections v i)
      (Family.SectionProjectiveCoordinates.scalarCoordinateSections v k)) = v := by
    funext k
    change Frame.Coordinates.structureModuleEndValue S (Family.SectionProjectiveCoordinates.scalarCoordinateSections v k ≫
      inv (Family.SectionProjectiveCoordinates.scalarCoordinateSections v i)) = v k
    simp only [hsi, IsIso.inv_id, Category.comp_id]
    exact (Global.Sections.structureModuleEndRingEquiv S).apply_symm_apply (v k)
  exact (sectionAbsoluteMorphism_of_frame (𝟙 S) (Family.SectionProjectiveCoordinates.scalarCoordinateSections v)
    (Family.SectionProjectiveCoordinates.scalarCoordinateSections_cover v hv) i).trans
      (Framed.ProjectiveMaps.projectiveChartMap_congr_coefficients rfl hc i _ _)

theorem scalarCoordinateProjectivePoint_affine
    (C : Type u) [CommRing C] {n : ℕ}
    (v : Fin (n + 1) → Γ(Spec (.of C), ⊤))
    (hv : ∀ x : Spec (.of C), ∃ k, x ∈ (Spec (.of C)).basicOpen (v k))
    (i : Fin (n + 1)) (hi : v i = 1) :
    (Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint v hv).left =
      AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of C) C
        (fun k => (Scheme.ΓSpecIso (.of C)).hom (v k)) i
        ((congrArg (Scheme.ΓSpecIso (.of C)).hom hi).trans (map_one _)) ≫
          AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of C))) n := by
  let S := Spec (.of C)
  let c := (Scheme.ΓSpecIso (.of C)).inv.hom
  let d := (Scheme.ΓSpecIso (.of C)).hom.hom
  let w := fun k => d (v k)
  have hw : w i = 1 := (congrArg d hi).trans d.map_one
  have hd : c.comp d = RingHom.id Γ(S, ⊤) := by
    exact congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso (.of C)).hom_inv_id
  have hc : (fun k => c (w k)) = v := by
    funext k
    exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of C)).hom_inv_id (v k)
  have hchart : AffineProjective.Charts.affineProjectiveChartMap (𝟙 S) n ≫
      RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection S n =
      Projective.CoefficientFunctoriality.polynomialProjectiveMap (Scheme.ΓSpecIso (.of C)).hom n := by
    simpa only [RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection, AffineProjective.Charts.affinePointCoefficients,
      Scheme.Hom.id_appTop, Category.id_comp] using
      AffineProjective.Charts.affineProjectiveChartMap_fst (𝟙 S) n
  have hpoint : (Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint v hv).left ≫
      RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection S n =
      SectionsProjectiveMorphism.sectionAbsoluteMorphism (𝟙 S) (Family.SectionProjectiveCoordinates.scalarCoordinateSections v)
        (Family.SectionProjectiveCoordinates.scalarCoordinateSections_cover v hv) :=
    Section.ProjectiveBaseChange.sectionProjectiveMorphism_coefficientProjection (𝟙 S) (Family.SectionProjectiveCoordinates.scalarCoordinateSections v)
      (Family.SectionProjectiveCoordinates.scalarCoordinateSections_cover v hv)
  have hglobal : AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of C) C w i hw ≫
      Projective.CoefficientFunctoriality.polynomialProjectiveMap (Scheme.ΓSpecIso (.of C)).hom n =
      ProjectiveChart.Evaluation.projectiveChartMap (RingHom.id Γ(S, ⊤)) v i hi := by
    rw [AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap_global]
    exact (ProjectiveChart.CoefficientNaturality.projectiveChartMap_coefficientMap d c (fun k => c (w k)) i
      ((congrArg c hw).trans c.map_one)).trans
        (Framed.ProjectiveMaps.projectiveChartMap_congr_coefficients hd hc i _ _)
  apply (RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection_isPullback S n).hom_ext
  · exact hpoint.trans ((scalarCoordinate_absolute_normalized v hv i hi).trans
      (hglobal.symm.trans ((congrArg
        (fun a => AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of C) C w i hw ≫ a) hchart.symm).trans
          (Category.assoc _ _ _).symm)))
  · change (Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint v hv).left ≫
        (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom =
      (AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of C) C w i hw ≫
        AffineProjective.Charts.affineProjectiveChartMap (𝟙 S) n) ≫ (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom
    rw [(Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint v hv).w, Category.assoc,
      AffineProjective.Charts.affineProjectiveChartMap_over, Category.comp_id, AffineProjective.CoordinatesOver.affineProjectiveCoordinateMap_over]
    exact (Spec.map_id (.of C)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ScalarCoordinateCoverage.StableHilbertCoverage
