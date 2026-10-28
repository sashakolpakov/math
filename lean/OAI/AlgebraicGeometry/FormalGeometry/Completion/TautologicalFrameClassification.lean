import OAI.AlgebraicGeometry.FormalGeometry.Completion.ComposedSectionAssociativity
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.SchemeUniversalTrivialization

/-! # Tautological Frame Classification -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! Pulling back the actual universal frame along an affine test map
recovers precisely that map under the frame-scheme classification. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u
variable {X S : Scheme.{u}} [IsAffine S] {π : X ⟶ S} [IsProper π] {L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X}
  (D : Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation π L.sheaf)

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.tautologicalFrame_composite_value {Z : Scheme.{u}} (k : Z ⟶ D.frameFamily) :
    AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback (k ≫ D.frameFamilyToOriginal)).obj L.sheaf)
      (Frame.SchemeNaturality.Construction.compositeLineFrameIso D.frameFamilyToOriginal k L.sheaf D.tautologicalFrame).hom =
    ((Scheme.Modules.pullbackCongr (Category.assoc k
      (pullback.fst (pullback.snd π D.scheme.hom) D.frameOpen.ι) (pullback.fst π D.scheme.hom))).hom.app L.sheaf).app ⊤
      (GlobalSectionComposition.Construction.globalSectionCompositePullback (pullback.fst π D.scheme.hom)
        (k ≫ pullback.fst (pullback.snd π D.scheme.hom) D.frameOpen.ι) L.sheaf D.universalSection) := by
  have hm := ComposedSectionAssociativity.Construction.pullbackComposedSection_assoc (pullback.fst π D.scheme.hom)
    (pullback.fst (pullback.snd π D.scheme.hom) D.frameOpen.ι) k L.sheaf D.universalSectionHom
  change (Frame.SchemeNaturality.Construction.compositeLineFrameIso D.frameFamilyToOriginal k L.sheaf D.tautologicalFrame).hom =
    (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (k ≫ pullback.fst (pullback.snd π D.scheme.hom) D.frameOpen.ι) D.universalSectionHom ≫
      (Scheme.Modules.pullbackComp (k ≫ pullback.fst (pullback.snd π D.scheme.hom) D.frameOpen.ι)
        (pullback.fst π D.scheme.hom)).hom.app L.sheaf) ≫
      (Scheme.Modules.pullbackCongr (Category.assoc k
        (pullback.fst (pullback.snd π D.scheme.hom) D.frameOpen.ι) (pullback.fst π D.scheme.hom))).hom.app L.sheaf at hm
  have hv := congrArg
    (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback (k ≫ D.frameFamilyToOriginal)).obj L.sheaf)) hm
  change AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback (k ≫ D.frameFamilyToOriginal)).obj L.sheaf)
      (Frame.SchemeNaturality.Construction.compositeLineFrameIso D.frameFamilyToOriginal k L.sheaf D.tautologicalFrame).hom =
    ((Scheme.Modules.pullbackCongr (Category.assoc k
      (pullback.fst (pullback.snd π D.scheme.hom) D.frameOpen.ι) (pullback.fst π D.scheme.hom))).hom.app L.sheaf).app ⊤
      (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv _ (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection
        (k ≫ pullback.fst (pullback.snd π D.scheme.hom) D.frameOpen.ι) D.universalSectionHom ≫
          (Scheme.Modules.pullbackComp (k ≫ pullback.fst (pullback.snd π D.scheme.hom) D.frameOpen.ι)
            (pullback.fst π D.scheme.hom)).hom.app L.sheaf)) at hv
  rw [GlobalSectionHomPullback.Construction.moduleSectionHomEquiv_composite] at hv
  have hu := D.universalSectionHom_value
  change AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback (pullback.fst π D.scheme.hom)).obj L.sheaf)
    D.universalSectionHom = D.universalSection at hu
  exact hv.trans (congrArg
    (fun z : Γ((Scheme.Modules.pullback (pullback.fst π D.scheme.hom)).obj L.sheaf, ⊤) =>
      ((Scheme.Modules.pullbackCongr (Category.assoc k
        (pullback.fst (pullback.snd π D.scheme.hom) D.frameOpen.ι) (pullback.fst π D.scheme.hom))).hom.app L.sheaf).app ⊤
        (GlobalSectionComposition.Construction.globalSectionCompositePullback (pullback.fst π D.scheme.hom)
          (k ≫ pullback.fst (pullback.snd π D.scheme.hom) D.frameOpen.ι) L.sheaf z)) hu)

theorem Geometric.SectionAlgebra.Construction.GeometricSectionAlgebraRepresentation.tautologicalFrame_pullback_classifies {Z T : Scheme.{u}} [IsAffine T]
    (k : Z ⟶ D.frameFamily) (τ : Z ⟶ T) (t : T ⟶ D.frameSchemeOverBase.left)
    (hk : k ≫ D.frameFamilyProjection = τ ≫ t)
    (ho : IsPullback (k ≫ D.frameFamilyToOriginal) τ π (t ≫ D.frameSchemeOverBase.hom)) :
    D.lineBundleTrivializationPointEquiv (k ≫ D.frameFamilyToOriginal) τ (t ≫ D.frameSchemeOverBase.hom) ho
      (Frame.SchemeNaturality.Construction.compositeLineFrameIso D.frameFamilyToOriginal k L.sheaf D.tautologicalFrame) =
      (Over.homMk t rfl : Over.mk (t ≫ D.frameSchemeOverBase.hom) ⟶ D.frameSchemeOverBase) := by
  let j := pullback.fst (pullback.snd π D.scheme.hom) D.frameOpen.ι
  let d := k ≫ j
  have hd : d ≫ pullback.fst π D.scheme.hom = k ≫ D.frameFamilyToOriginal := Category.assoc k j _
  have hg : (t ≫ D.frameOpen.ι) ≫ D.scheme.hom = t ≫ D.frameSchemeOverBase.hom := Category.assoc t _ _
  have hp₀ : IsPullback (d ≫ pullback.fst π D.scheme.hom) τ π ((t ≫ D.frameOpen.ι) ≫ D.scheme.hom) := by
    rw [hd, hg]
    exact ho
  have hp₁ : IsPullback (k ≫ D.frameFamilyToOriginal) τ π ((t ≫ D.frameOpen.ι) ≫ D.scheme.hom) := by
    rw [hg]
    exact ho
  have hj : d ≫ pullback.snd π D.scheme.hom = τ ≫ (t ≫ D.frameOpen.ι) := by
    change (k ≫ j) ≫ pullback.snd π D.scheme.hom = _
    rw [Category.assoc, show j ≫ pullback.snd π D.scheme.hom =
      D.frameFamilyProjection ≫ D.frameOpen.ι from pullback.condition,
      ← Category.assoc, hk, Category.assoc]
  let v := GlobalSectionComposition.Construction.globalSectionCompositePullback (pullback.fst π D.scheme.hom) d L.sheaf D.universalSection
  let v' := ((Scheme.Modules.pullbackCongr hd).hom.app L.sheaf).app ⊤ v
  have hc := D.universalSection_pullback_classifies d τ (t ≫ D.frameOpen.ι) hj hp₀
  have ht := D.sectionPointEquiv_top_congr (d ≫ pullback.fst π D.scheme.hom)
    (k ≫ D.frameFamilyToOriginal) hd τ ((t ≫ D.frameOpen.ι) ≫ D.scheme.hom) hp₀ hp₁ v
  have hb := D.sectionPointEquiv_base_congr_left (k ≫ D.frameFamilyToOriginal) τ
    ((t ≫ D.frameOpen.ι) ≫ D.scheme.hom) (t ≫ D.frameSchemeOverBase.hom) hg hp₁ ho v'
  have : Mono (OpenFamilyPoints.Construction.openFamilyInclusion D.scheme D.frameOpen) :=
    inferInstanceAs (Mono (Over.homMk D.frameOpen.ι rfl : OpenFamilyPoints.Construction.openFamily D.scheme D.frameOpen ⟶ D.scheme))
  apply (cancel_mono (OpenFamilyPoints.Construction.openFamilyInclusion D.scheme D.frameOpen)).mp
  rw [D.lineBundleTrivializationPointEquiv_inclusion]
  apply Over.OverMorphism.ext
  have hv := congrArg (fun z => (D.sectionPointEquiv (k ≫ D.frameFamilyToOriginal) τ
    (t ≫ D.frameSchemeOverBase.hom) ho z).left) (D.tautologicalFrame_composite_value k)
  exact hv.trans (hb.trans ((congrArg Over.Hom.left ht).trans (congrArg Over.Hom.left hc)))

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion
