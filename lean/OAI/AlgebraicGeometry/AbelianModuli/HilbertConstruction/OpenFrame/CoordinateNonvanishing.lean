import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.GlobalCoordinateValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.FromSectionValue
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing

/-! # Coordinate Nonvanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.CoordinateNonvanishing

noncomputable section

/-! The nonvanishing locus of a global frame section is the basic open of its chart coordinate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : Transitions.OpenFrameTransitions U)
variable (s : Line.Bundles.structureModule X ⟶ ModuleSheaf.openFrameModuleSheaf D) (k : ι)

def openFrameChartCoordinate : Γ((U k).toScheme, ⊤) :=
  ((U k).ι.appIso ⊤).hom
    (X.presheaf.map (homOfLE (LocalSections.openInclusionImage_le (U k) ⊤)).op
      (show Γ(X, U k) from CoefficientSections.openFrameGlobalTupleMap D
        (Global.Sections.moduleSectionHomEquiv (ModuleSheaf.openFrameModuleSheaf D) s) k))

theorem openFrameChartCoordinate_eq_frameCoordinate :
    Frame.Coordinates.frameCoordinate (LocalSections.openFrameLocalSection D k) (Section.SectionRestriction.restrictSection (U k).ι s) =
      openFrameChartCoordinate D s k := by
  let V := (U k).ι ''ᵁ (⊤ : (U k).toScheme.Opens)
  let hV : V ≤ U k := LocalSections.openInclusionImage_le (U k) ⊤
  let r : Γ(X, V) := X.presheaf.map (homOfLE hV).op
    (show Γ(X, U k) from CoefficientSections.openFrameGlobalTupleMap D
      (Global.Sections.moduleSectionHomEquiv (ModuleSheaf.openFrameModuleSheaf D) s) k)
  have hc : ((U k).ι.appIso ⊤).inv (openFrameChartCoordinate D s k) = r :=
    ConcreteCategory.congr_hom ((U k).ι.appIso ⊤).hom_inv_id r
  have hs : (Section.SectionRestriction.restrictSection (U k).ι s).app ⊤ (1 : Γ((U k).toScheme, ⊤)) =
      SectionGenerators.openFrameGenerator D V k hV r :=
    (Section.SectionRestriction.restrictSection_app_one (U k).ι s ⊤).trans (GlobalCoordinateValues.openFrameSection_app_one_coordinate D s k V hV)
  have he : (LocalSections.openFrameLocalSection D k).app ⊤ (1 : Γ((U k).toScheme, ⊤)) =
      SectionGenerators.openFrameGenerator D V k hV 1 :=
    (Global.Sections.moduleSectionHomEquiv ((ModuleSheaf.openFrameModuleSheaf D).restrict (U k).ι)).apply_symm_apply _
  apply Coordinate.FromSectionValue.frameCoordinate_eq_of_value
  change (Section.SectionRestriction.restrictSection (U k).ι s).app ⊤ (1 : Γ((U k).toScheme, ⊤)) =
    ((U k).ι.appIso ⊤).inv (openFrameChartCoordinate D s k) •
      (show SectionModules.openFrameSectionModule U D V from
        (LocalSections.openFrameLocalSection D k).app ⊤ (1 : Γ((U k).toScheme, ⊤)))
  rw [hc, he]
  exact hs.trans (GeneratorNaturality.openFrameGenerator_smul_one D V k hV r).symm

theorem openFrameSection_nonvanishing_on_chart :
    (U k).ι ⁻¹ᵁ Ample.LineBundles.sectionNonvanishing s =
      (U k).toScheme.basicOpen (openFrameChartCoordinate D s k) := by
  rw [← Section.SectionRestriction.sectionNonvanishing_restrictSection,
    Scalar.Nonvanishing.sectionNonvanishing_frameCoordinate (LocalSections.openFrameLocalSection D k),
    openFrameChartCoordinate_eq_frameCoordinate]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.CoordinateNonvanishing
