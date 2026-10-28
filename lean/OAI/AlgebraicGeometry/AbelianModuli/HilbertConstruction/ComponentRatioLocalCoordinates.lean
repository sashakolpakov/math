import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ComponentRatios

/-! # Component Ratio Local Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ComponentRatioLocalCoordinates

noncomputable section

/-! On any open where a section frames the line bundle, ordinary component ratios equal the canonical pulled-back frame coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {M : X.Modules}

theorem componentRatio_localFrameCoordinate (s t : Line.Bundles.structureModule X ⟶ M)
    (U : X.Opens) (hU : U ≤ Ample.LineBundles.sectionNonvanishing s) [IsIso (Ample.LineBundles.pullbackSection U.ι s)] :
    U.topIso.hom (Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection U.ι s) (Ample.LineBundles.pullbackSection U.ι t)) =
      Section.ComponentRatios.sectionComponentRatio s t U hU := by
  let r := Section.ComponentRatios.sectionComponentRatio s t U hU
  have hc : U.topIso.hom (U.topIso.inv r) = r := ConcreteCategory.congr_hom U.topIso.inv_hom_id r
  have hv : t.app U (1 : Γ(X, U)) = U.topIso.hom (U.topIso.inv r) • s.app U (1 : Γ(X, U)) :=
    (Section.ComponentRatios.sectionComponentRatio_value s t U hU).trans
      (congrArg (fun a : Γ(X, U) => a • s.app U (1 : Γ(X, U))) hc.symm)
  exact (congrArg U.topIso.hom (Coordinate.FromSectionValue.local_frameCoordinate_eq_of_value_on_open U s t (U.topIso.inv r) hv)).trans hc

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ComponentRatioLocalCoordinates
