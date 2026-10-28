import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.SectionProjectiveCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SectionBaseChange

/-! # Coordinate Projective Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.CoordinateProjectiveBaseChange

noncomputable section

/-! Projective points given by global scalar coordinates commute with
arbitrary base change, through the native relative projective section. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {S T : Scheme.{u}} {n : ℕ}

theorem scalarCoordinateSections_pullback (f : T ⟶ S)
    (v : Fin (n + 1) → Γ(S, ⊤)) (i : Fin (n + 1)) :
    Ample.LineBundles.pullbackSection f (Family.SectionProjectiveCoordinates.scalarCoordinateSections v i) ≫ (Line.Bundles.structureModulePullbackIso f).hom =
      Family.SectionProjectiveCoordinates.scalarCoordinateSections (fun k => f.appTop (v k)) i := by
  apply (Global.Sections.structureModuleEndRingEquiv T).injective
  change Frame.Coordinates.structureModuleEndValue T
      (Ample.LineBundles.pullbackSection f (Family.SectionProjectiveCoordinates.scalarCoordinateSections v i) ≫ (Line.Bundles.structureModulePullbackIso f).hom) =
    Frame.Coordinates.structureModuleEndValue T (Family.SectionProjectiveCoordinates.scalarCoordinateSections (fun k => f.appTop (v k)) i)
  calc
    _ = f.appTop (Frame.Coordinates.structureModuleEndValue S (Family.SectionProjectiveCoordinates.scalarCoordinateSections v i)) := by
      simpa only [Ample.LineBundles.pullbackSection, Category.assoc] using
        BaseChange.structureModuleEndValue_baseChange f (Family.SectionProjectiveCoordinates.scalarCoordinateSections v i)
    _ = f.appTop (v i) := congrArg f.appTop ((Global.Sections.structureModuleEndRingEquiv S).apply_symm_apply (v i))
    _ = _ := ((Global.Sections.structureModuleEndRingEquiv T).apply_symm_apply (f.appTop (v i))).symm

theorem scalarCoordinateProjectivePoint_baseChange (f : T ⟶ S)
    (v : Fin (n + 1) → Γ(S, ⊤))
    (hv : ∀ x : S, ∃ i, x ∈ S.basicOpen (v i))
    (hw : ∀ x : T, ∃ i, x ∈ T.basicOpen (f.appTop (v i))) :
    Projective.SectionBaseChange.projectiveSectionBaseChange (Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint v hv) f =
      Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint (fun i => f.appTop (v i)) hw := by
  let s := Family.SectionProjectiveCoordinates.scalarCoordinateSections v
  let hs := Family.SectionProjectiveCoordinates.scalarCoordinateSections_cover v hv
  let t := fun i => Ample.LineBundles.pullbackSection f (s i)
  let ht := Section.ChartArbitraryPullback.lineBundleSections_pullback_covers f (Line.Bundles.LineBundle.trivial S) s hs
  let e := Line.Bundles.structureModulePullbackIso f
  let he := Section.ProjectiveTargetIso.sections_compIso_covers e t ht
  have hsections : (fun i => t i ≫ e.hom) = Family.SectionProjectiveCoordinates.scalarCoordinateSections (fun i => f.appTop (v i)) :=
    funext (scalarCoordinateSections_pullback f v)
  have hp : SectionsProjectiveMorphism.sectionProjectiveMorphism (𝟙 T) t ht =
      Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint (fun i => f.appTop (v i)) hw :=
    (Section.ProjectiveTargetIso.sectionProjectiveMorphism_targetIso (𝟙 T) e t ht he).trans
      (Section.ProjectiveTargetIso.sectionProjectiveMorphism_congr (𝟙 T) hsections he (Family.SectionProjectiveCoordinates.scalarCoordinateSections_cover _ hw))
  have hb := Section.ProjectiveBaseChange.sectionProjectiveMorphism_baseChange f f (𝟙 S) (𝟙 T)
    ((Category.comp_id f).trans (Category.id_comp f).symm) (Line.Bundles.LineBundle.trivial S) s hs ht
  apply Projective.SectionBaseChange.projectiveSections_eq_of_baseMap f
  exact (Projective.SectionBaseChange.projectiveSectionBaseChange_baseMap (Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint v hv) f).trans
    (hb.trans (congrArg (fun z : Over.mk (𝟙 T) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver T n =>
      z.left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n) hp))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.CoordinateProjectiveBaseChange
