import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.FrameCocycles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.FromSectionValue

/-! # Component Ratios -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ComponentRatios

noncomputable section

/-! Ordinary component ratios of global sections agree with the canonical geometric section ratios and commute with restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {M : X.Modules} (s t : Line.Bundles.structureModule X ⟶ M)

def sectionComponentRatio (V : X.Opens) (hV : V ≤ Ample.LineBundles.sectionNonvanishing s) : Γ(X, V) :=
  (LocalLinearFrames.sectionLocalFrameEquiv s V hV).symm (t.app V (1 : Γ(X, V)))

theorem sectionComponentRatio_frame (V : X.Opens) (hV : V ≤ Ample.LineBundles.sectionNonvanishing s) :
    s.app V (sectionComponentRatio s t V hV) = t.app V (1 : Γ(X, V)) :=
  (LocalLinearFrames.sectionLocalFrameEquiv_apply s V hV _).symm.trans
    ((LocalLinearFrames.sectionLocalFrameEquiv s V hV).apply_symm_apply _)

theorem sectionComponentRatio_value (V : X.Opens) (hV : V ≤ Ample.LineBundles.sectionNonvanishing s) :
    t.app V (1 : Γ(X, V)) = sectionComponentRatio s t V hV • s.app V (1 : Γ(X, V)) := by
  have he := (congrArg (s.app V) (mul_one (sectionComponentRatio s t V hV))).symm.trans
    (s.app_smul (sectionComponentRatio s t V hV) (1 : Γ(X, V)))
  exact (sectionComponentRatio_frame s t V hV).symm.trans he

theorem sectionComponentRatio_restrict (V W : X.Opens) (h : W ≤ V) (hV : V ≤ Ample.LineBundles.sectionNonvanishing s) :
    X.presheaf.map (homOfLE h).op (sectionComponentRatio s t V hV) =
      sectionComponentRatio s t W (h.trans hV) := by
  apply (LocalLinearFrames.sectionLocalFrameEquiv s W (h.trans hV)).injective
  have hs := ConcreteCategory.congr_hom (s.mapPresheaf.naturality (homOfLE h).op)
    (sectionComponentRatio s t V hV)
  have ht := (M.unitHomEquiv t).property (homOfLE h).op
  exact (LocalLinearFrames.sectionLocalFrameEquiv_apply s W (h.trans hV) _).trans
    (hs.trans ((congrArg (M.presheaf.map (homOfLE h).op) (sectionComponentRatio_frame s t V hV)).trans
      (ht.trans ((LocalLinearFrames.sectionLocalFrameEquiv s W (h.trans hV)).apply_symm_apply _).symm)))

theorem sectionRatio_component :
    (Ample.LineBundles.sectionNonvanishing s).topIso.hom (Frames.sectionRatio s t) =
      sectionComponentRatio s t (Ample.LineBundles.sectionNonvanishing s) le_rfl := by
  let V := Ample.LineBundles.sectionNonvanishing s
  let r := sectionComponentRatio s t V le_rfl
  have hc : V.topIso.hom (V.topIso.inv r) = r := ConcreteCategory.congr_hom V.topIso.inv_hom_id r
  have hv : t.app V (1 : Γ(X, V)) = V.topIso.hom (V.topIso.inv r) • s.app V (1 : Γ(X, V)) :=
    (sectionComponentRatio_value s t V le_rfl).trans
      (congrArg (fun a : Γ(X, V) => a • s.app V (1 : Γ(X, V))) hc.symm)
  have he := (Frame.Coordinates.sectionRatio_eq_frameCoordinate s t).trans
    (Coordinate.FromSectionValue.local_frameCoordinate_eq_of_value_on_open V s t (V.topIso.inv r) hv)
  exact (congrArg V.topIso.hom he).trans hc

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ComponentRatios
