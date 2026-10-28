import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationTensorTwisting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresentationSectionData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.GlobalSectionExt
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.LevelFrameParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.ZeroNormalizedBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.BundleTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.SectionCompletenessBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.SectionCompletenessIdentity

/-! # Zero Graph Power Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroGraphPowerSections

noncomputable section

/-! A scalar-coordinate zero mark trivializes the embedding line at
the identity. Consequently its zero-normalized graph-power comparison
gives an actual graph-power section system. Geometric completeness
supplies a complete basis on every Noetherian affine test. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

private theorem geometricallyComplete_id_fiber
    {S X : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) {r : ℕ}
    (s : Fin r → (Line.Bundles.structureModule X ⟶ M))
    (hs : ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily f M s (𝟙 S))
    (K : Type u) [Field K] (q : Spec (.of K) ⟶ S) :
    Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination
      (pullback.snd f q).appTop.hom
      ((Scheme.Modules.pullback (pullback.fst f q)).obj M)
      (fun i => Ample.LineBundles.pullbackSection (pullback.fst f q) (s i))) := by
  have h := hs K q
  change Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination
    (pullback.snd f (q ≫ 𝟙 S)).appTop.hom
    ((Scheme.Modules.pullback (pullback.fst f (q ≫ 𝟙 S))).obj M)
    (fun i => Ample.LineBundles.pullbackSection (pullback.fst f (q ≫ 𝟙 S)) (s i))) at h
  rw [Category.comp_id] at h
  exact h

namespace ProjectivePresentation
variable {S : Scheme.{u}} {X : Over S} (P : Projective.ProjectivePresentations.ProjectivePresentation X)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation.ampleLine_scalarSectionIso
    (x : Over.mk (𝟙 S) ⟶ X) (v : Fin (P.dimension + 1) → Γ(S, ⊤))
    (hv : ∀ z : S, ∃ i, z ∈ S.basicOpen (v i))
    (hx : x ≫ P.embedding = Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint v hv) :
    (P.ampleLineBundle.pullback x.left).sheaf ≅ Line.Bundles.structureModule S :=
  (Scheme.Modules.pullbackComp x.left P.embedding.left).app
      (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S P.dimension).sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hx)).app
      (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S P.dimension).sheaf ≪≫
    RelativeProjective.TwistingBundle.sectionProjectiveTwistingBundleIso (𝟙 S) (Family.SectionProjectiveCoordinates.scalarCoordinateSections v)
      (Family.SectionProjectiveCoordinates.scalarCoordinateSections_cover v hv)

end ProjectivePresentation

namespace PolarizedAbelianWithFullLevel
variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
variable (P : Projective.ProjectivePresentations.ProjectivePresentation A.abelian.scheme)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.rawGraphPowerIso_of_scalarZero (d : ℕ)
    (h : (A.abelian.zeroNormalizedBundle P.ampleLineBundle).sheaf ≅
      (A.graphBundle.tensorPower d).sheaf)
    (v : Fin (P.dimension + 1) → Γ(S, ⊤))
    (hv : ∀ z : S, ∃ i, z ∈ S.basicOpen (v i))
    (hz : Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 S)) A.abelian A.level P 1 =
      Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint v hv) :
    P.ampleLineBundle.sheaf ≅ (A.graphBundle.tensorPower d).sheaf := by
  have hz' : η[A.abelian.scheme] ≫ P.embedding = Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint v hv := by
    apply Over.OverMorphism.ext
    have he := congrArg Over.Hom.left hz
    change A.abelian.fullLevelGlobalSection A.level 1 ≫ P.embedding.left =
      (Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint v hv).left at he
    rw [Abelian.Schemes.AbelianScheme.fullLevelGlobalSection_one] at he
    exact he
  let z := P.ampleLine_scalarSectionIso η[A.abelian.scheme] v hv hz'
  exact (Line.Bundles.LineBundle.sectionNormalized_fixedIso A.abelian.scheme.hom
    η[A.abelian.scheme].left P.ampleLineBundle ⟨z⟩).symm ≪≫ h

end PolarizedAbelianWithFullLevel

namespace ProjectivePresentation.SectionData
variable {S T : Scheme.{u}} {X : Over S} [IsProper X.hom] [Flat X.hom]
variable {P : Projective.ProjectivePresentations.ProjectivePresentation X} {L : Line.Bundles.LineBundle X.left}

/-- This uses all geometric fibers, so nilpotents on the affine test
are retained by the proper-flat universal section criterion. -/
def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation.SectionData.completeBaseChangeOfGeometric (D : P.SectionData L)
    (h : ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily X.hom L.sheaf D.sections (𝟙 S))
    [IsAffine T] [IsLocallyNoetherian T] (f : T ⟶ S) :
    (D.baseChange f).CompleteData := by
  have : IsNoetherianRing Γ(T, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top T⟩
  let Y := (Over.pullback f).obj X
  let M := L.pullback (pullback.fst X.hom f)
  let E := D.baseChange f
  have : IsProper Y.hom := inferInstanceAs (IsProper (pullback.snd X.hom f))
  have : Flat Y.hom := inferInstanceAs (Flat (pullback.snd X.hom f))
  have hf : ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily X.hom L.sheaf D.sections f := by
    intro K _ a
    exact geometricallyComplete_id_fiber X.hom L.sheaf D.sections h K (a ≫ f)
  have hg : ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily Y.hom M.sheaf E.sections (𝟙 T) := by
    apply (Universal.SectionCompletenessBaseChange.geometricallyCompleteSectionFamily_baseChange_iff X L.sheaf f D.sections (𝟙 T)).mpr
    simpa only [Category.id_comp] using hf
  have hu : Universal.SectionCompletenessOpen.UniversallyCompleteSectionFamily Y.hom M.sheaf E.sections (𝟙 T) :=
    (ProperFlat.SectionFiberCriterion.properFlat_universalSectionCompleteness_iff_geometric Y.hom M E.sections (𝟙 T)).mpr hg
  have hb : Function.Bijective
      (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination Y.hom.appTop.hom M.sheaf E.sections) :=
    Universal.SectionCompletenessIdentity.universallyCompleteSectionFamily_id_bijective Y M.sheaf E.sections hu
  exact ⟨Coefficient.SectionFrameCriterion.coefficientSectionBasisOfBijective Y.hom.appTop.hom M.sheaf E.sections hb,
    (Coefficient.SectionFrameCriterion.coefficientSectionBasisOfBijective_family Y.hom.appTop.hom M.sheaf E.sections hb).symm⟩

end ProjectivePresentation.SectionData

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroGraphPowerSections
