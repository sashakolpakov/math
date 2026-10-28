import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.FramedSectionEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveTargetIso

/-! # Section Projective Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.SectionProjectiveCoordinates

noncomputable section

/-! The image of an actual family section in a section-defined
projective embedding is the projective point of its evaluated coordinates. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S X : Scheme.{u}} {n : ℕ}

def scalarCoordinateSections (v : Fin (n + 1) → Γ(S, ⊤)) :
    Fin (n + 1) → End (Line.Bundles.structureModule S) :=
  fun i => (Global.Sections.structureModuleEndRingEquiv S).symm (v i)

theorem scalarCoordinateSections_cover (v : Fin (n + 1) → Γ(S, ⊤))
    (hv : ∀ x : S, ∃ i, x ∈ S.basicOpen (v i)) :
    ∀ x : S, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (scalarCoordinateSections v i) := by
  intro x
  obtain ⟨i, hi⟩ := hv x
  refine ⟨i, ?_⟩
  rw [Scalar.Nonvanishing.sectionNonvanishing_scalar]
  change x ∈ S.basicOpen (Global.Sections.structureModuleEndRingEquiv S ((Global.Sections.structureModuleEndRingEquiv S).symm (v i)))
  rwa [RingEquiv.apply_symm_apply]

def scalarCoordinateProjectivePoint (v : Fin (n + 1) → Γ(S, ⊤))
    (hv : ∀ x : S, ∃ i, x ∈ S.basicOpen (v i)) :
    Over.mk (𝟙 S) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n :=
  SectionsProjectiveMorphism.sectionProjectiveMorphism (𝟙 S) (scalarCoordinateSections v) (scalarCoordinateSections_cover v hv)

theorem sectionProjectiveMorphism_along_familySection
    (p : X ⟶ S) (L : Line.Bundles.LineBundle X)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hs : ∀ z : X, ∃ i, z ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (x : S ⟶ X) (hx : x ≫ p = 𝟙 S)
    (ht : ∀ z : S, ∃ i, z ∈ Ample.LineBundles.sectionNonvanishing (Ample.LineBundles.pullbackSection x (s i))) :
    Over.homMk x hx ≫ SectionsProjectiveMorphism.sectionProjectiveMorphism p s hs =
      SectionsProjectiveMorphism.sectionProjectiveMorphism (𝟙 S) (fun i => Ample.LineBundles.pullbackSection x (s i)) ht := by
  apply Over.OverMorphism.ext
  apply (RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection_isPullback S n).hom_ext
  · change (x ≫ (SectionsProjectiveMorphism.sectionProjectiveMorphism p s hs).left) ≫ _ = _
    rw [Category.assoc, Section.ProjectiveBaseChange.sectionProjectiveMorphism_coefficientProjection,
      Section.ProjectiveBaseChange.sectionProjectiveMorphism_coefficientProjection]
    simpa only [hx] using Section.ChartArbitraryPullback.sectionAbsoluteMorphism_pullback_source p x L s hs ht
  · change (x ≫ (SectionsProjectiveMorphism.sectionProjectiveMorphism p s hs).left) ≫
        (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom =
      (SectionsProjectiveMorphism.sectionProjectiveMorphism (𝟙 S) (fun i => Ample.LineBundles.pullbackSection x (s i)) ht).left ≫
        (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => x ≫ k) (SectionsProjectiveMorphism.sectionProjectiveMorphism p s hs).w).trans
        (hx.trans (SectionsProjectiveMorphism.sectionProjectiveMorphism (𝟙 S) (fun i => Ample.LineBundles.pullbackSection x (s i)) ht).w.symm))

theorem familySectionCoordinates_cover (L : Line.Bundles.LineBundle X)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hs : ∀ z : X, ∃ i, z ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (x : S ⟶ X) (e : (L.pullback x).sheaf ≅ Line.Bundles.structureModule S) :
    ∀ z : S, ∃ i, z ∈ S.basicOpen (FramedSectionEvaluation.familyFramedSectionValue L x e (s i)) := by
  intro z
  obtain ⟨i, hi⟩ := hs (x z)
  refine ⟨i, ?_⟩
  rw [FramedSectionEvaluation.familyFramedSectionValue_nonvanishing]
  exact hi

theorem familySection_projectivePoint (p : X ⟶ S) (L : Line.Bundles.LineBundle X)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hs : ∀ z : X, ∃ i, z ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (x : S ⟶ X) (hx : x ≫ p = 𝟙 S) (e : (L.pullback x).sheaf ≅ Line.Bundles.structureModule S) :
    Over.homMk x hx ≫ SectionsProjectiveMorphism.sectionProjectiveMorphism p s hs =
      scalarCoordinateProjectivePoint (fun i => FramedSectionEvaluation.familyFramedSectionValue L x e (s i))
        (familySectionCoordinates_cover L s hs x e) := by
  let t := fun i => Ample.LineBundles.pullbackSection x (s i)
  let ht := Section.ChartArbitraryPullback.lineBundleSections_pullback_covers x L s hs
  rw [sectionProjectiveMorphism_along_familySection p L s hs x hx ht]
  let he := Section.ProjectiveTargetIso.sections_compIso_covers e t ht
  change SectionsProjectiveMorphism.sectionProjectiveMorphism (𝟙 S) t ht = _
  rw [Section.ProjectiveTargetIso.sectionProjectiveMorphism_targetIso (𝟙 S) e t ht he]
  apply Section.ProjectiveTargetIso.sectionProjectiveMorphism_congr
  funext i
  exact (Global.Sections.structureModuleEndRingEquiv S).symm_apply_apply (Ample.LineBundles.pullbackSection x (s i) ≫ e.hom) |>.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.SectionProjectiveCoordinates
