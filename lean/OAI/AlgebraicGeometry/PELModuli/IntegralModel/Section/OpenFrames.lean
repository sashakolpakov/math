import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.SectionRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.PullbackCoherence
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OverScalarRestriction

/-! # Open Frames -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.OpenFrames

noncomputable section

/-! Canonical native open frames supplied by generating sections. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace PolarizationEmbedding

open OAI.AlgebraicGeometry.SheafCohomology.Projective.OverScalarRestriction
universe u
variable {X : Scheme.{u}} {M : X.Modules}

theorem restrictSection_isIso_of_le (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)
    (U : X.Opens) (hU : U ≤ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) : IsIso (AbelianModuli.HilbertConstruction.Section.SectionRestriction.restrictSection U.ι s) := by
  apply (AbelianModuli.HilbertConstruction.Section.Frames.isIso_iff_sectionNonvanishing_eq_top _).mpr
  rw [AbelianModuli.HilbertConstruction.Section.SectionRestriction.sectionNonvanishing_restrictSection]
  exact top_unique (fun x _ => hU x.property)

theorem sectionOver_isIso_of_le (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)
    (U : X.Opens) (hU : U ≤ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) : IsIso (s.over U) := by
  let := restrictSection_isIso_of_le s U hU
  have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map s) :=
    (isIso_comp_left_iff (Scheme.Modules.restrictUnitIso U.ι).inv _).mp
      (inferInstanceAs (IsIso (AbelianModuli.HilbertConstruction.Section.SectionRestriction.restrictSection U.ι s)))
  apply (isIso_iff_of_reflects_iso (s.over U) (Scheme.Modules.overEquiv U).functor).mp
  have he := (Scheme.Modules.overFunctorEquiv U).hom.naturality s
  have ht : (Scheme.Modules.overEquiv U).functor.map (s.over U) =
      ((Scheme.Modules.overFunctorEquiv U).app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).hom ≫
        (Scheme.Modules.restrictFunctor U.ι).map s ≫
          ((Scheme.Modules.overFunctorEquiv U).app M).inv := by
    apply (cancel_mono ((Scheme.Modules.overFunctorEquiv U).app M).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact he
  rw [ht]
  infer_instance

def sectionOverFrame (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)
    (U : X.Opens) (hU : U ≤ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) :
    M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U) := by
  let := sectionOver_isIso_of_le s U hU
  exact (asIso (s.over U)).symm

def sectionOpenFrame (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)
    (U : X.Opens) (hU : U ≤ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) :
    M.restrict U.ι ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme :=
  SheafCohomology.Projective.FrameSections.restrictTrivializationOfOverIso M U (sectionOverFrame s U hU)

theorem sectionOpenFrame_inv (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)
    (U : X.Opens) (hU : U ≤ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) :
    (sectionOpenFrame s U hU).inv = AbelianModuli.HilbertConstruction.Section.SectionRestriction.restrictSection U.ι s := by
  apply Scheme.Modules.hom_ext
  intro V
  ext x
  change s.app (U.ι ''ᵁ V) x = s.app (U.ι ''ᵁ V) ((U.ι.appIso V).inv x)
  rw [Scheme.Opens.ι_appIso]
  rfl

theorem sectionOverFrame_restrict (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)
    {U V : X.Opens} (hVU : V ≤ U) (hU : U ≤ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) :
    SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U
      (sectionOverFrame s U hU) (Over.mk (homOfLE hVU)) =
        sectionOverFrame s V (hVU.trans hU) := by
  apply Iso.ext
  apply (cancel_epi (sectionOverFrame s V (hVU.trans hU)).inv).mp
  rw [Iso.inv_hom_id]
  change (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U
    (sectionOverFrame s U hU) (Over.mk (homOfLE hVU))).inv ≫ _ = _
  exact Iso.inv_hom_id _

theorem sectionOpenFrame_restrict (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)
    {U V : X.Opens} (hVU : V ≤ U) (hU : U ≤ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) :
    SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hVU (sectionOpenFrame s U hU) =
      sectionOpenFrame s V (hVU.trans hU) := by
  unfold SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization sectionOpenFrame
  rw [SheafCohomology.Projective.OpenFrames.overTrivializationOfRestrictTrivializationOfOverIso, sectionOverFrame_restrict]

theorem nativeSectionRatio (s t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)
    (U : X.Opens) (hU : U ≤ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) :
    letI := restrictSection_isIso_of_le s U hU
    AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AbelianModuli.HilbertConstruction.Section.SectionRestriction.restrictSection U.ι s) (AbelianModuli.HilbertConstruction.Section.SectionRestriction.restrictSection U.ι t) =
      (X.homOfLE hU).appTop (AbelianModuli.HilbertConstruction.Section.Frames.sectionRatio s t) := by
  let := restrictSection_isIso_of_le s U hU
  have hp : IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection U.ι s) := by
    exact (congrArg (fun f => IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s)) (X.homOfLE_ι hU)).mp
      (inferInstanceAs (IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection ((X.homOfLE hU) ≫ (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).ι) s)))
  let := hp
  have : IsIso ((Scheme.Modules.restrictUnitIso U.ι).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map s) := restrictSection_isIso_of_le s U hU
  have : IsIso ((AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso U.ι).inv ≫ (Scheme.Modules.pullback U.ι).map s) := hp
  have he := AbelianModuli.HilbertConstruction.Frame.Comparison.frameCoordinate_functorComparison (Scheme.Modules.restrictFunctor U.ι)
    (Scheme.Modules.pullback U.ι) (Scheme.Modules.restrictFunctorIsoPullback U.ι)
    (Scheme.Modules.restrictUnitIso U.ι) (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso U.ι) s t
  have hr := AbelianModuli.HilbertConstruction.Frame.PullbackCoherence.sectionRatio_restrict s t (X.homOfLE hU)
  have hc := AbelianModuli.HilbertConstruction.Frame.PullbackCoherence.frameCoordinate_pullbackCongr (X.homOfLE_ι hU) s t
  exact he.symm.trans (hc.symm.trans hr.symm)

theorem sectionOpenFrame_transition (s t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)
    (U : X.Opens) (hs : U ≤ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) (ht : U ≤ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t) :
    (sectionOpenFrame s U hs).hom = (sectionOpenFrame t U ht).hom ≫
      SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection ((X.homOfLE hs).appTop (AbelianModuli.HilbertConstruction.Section.Frames.sectionRatio s t)) := by
  let := restrictSection_isIso_of_le s U hs
  let e := sectionOpenFrame s U hs
  let g := sectionOpenFrame t U ht
  have hi : inv (AbelianModuli.HilbertConstruction.Section.SectionRestriction.restrictSection U.ι s) = e.hom := by
    apply (cancel_epi (AbelianModuli.HilbertConstruction.Section.SectionRestriction.restrictSection U.ι s)).mp
    rw [IsIso.hom_inv_id, ← sectionOpenFrame_inv s U hs]
    exact e.inv_hom_id.symm
  have hr : AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue U.toScheme (g.inv ≫ e.hom) =
      (X.homOfLE hs).appTop (AbelianModuli.HilbertConstruction.Section.Frames.sectionRatio s t) := by
    rw [show g.inv = AbelianModuli.HilbertConstruction.Section.SectionRestriction.restrictSection U.ι t from sectionOpenFrame_inv t U ht, ← hi]
    exact nativeSectionRatio s t U hs
  have he : SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection ((X.homOfLE hs).appTop (AbelianModuli.HilbertConstruction.Section.Frames.sectionRatio s t)) =
      g.inv ≫ e.hom := by
    apply AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndValue_injective U.toScheme
    change 1 * U.toScheme.presheaf.map (𝟙 (.op ⊤))
      ((X.homOfLE hs).appTop (AbelianModuli.HilbertConstruction.Section.Frames.sectionRatio s t)) = _
    rw [U.toScheme.presheaf.map_id]
    simp only [ConcreteCategory.id_apply, one_mul]
    exact hr.symm
  change e.hom = g.hom ≫ _
  rw [he, g.hom_inv_id_assoc]

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.OpenFrames
