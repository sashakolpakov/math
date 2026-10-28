import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing

/-! # Pullback Scalars Value -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackScalarsValue.Construction.PullbackScalars

noncomputable section

/-! Scalar sections under arbitrary scheme pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing

universe u

variable {X Y : Scheme.{u}}

/-- Conjugating a pulled-back scalar through the canonical structure-module
comparison gives the usual pullback of its regular function. -/
theorem value_pullback (f : X ⟶ Y) (a : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)) :
    AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X ((AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).inv ≫
      (Scheme.Modules.pullback f).map a ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom) =
        f.appTop (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue Y a) := by
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  let b : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :=
    (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv X).symm (f.appTop (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue Y a))
  have hb : AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X b = f.appTop (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue Y a) :=
    (AbelianModuli.HilbertConstruction.Global.Sections.structureModuleEndRingEquiv X).apply_symm_apply _
  have he : ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _)
      (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom =
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have h : (Scheme.Modules.pullback f).map a ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom =
      (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom ≫ b := by
    apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    rw [he]
    change a ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map b
    apply (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pushforward f).obj
      (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X))).injective
    change f.appTop (a.app ⊤ (1 : Γ(Y, ⊤))) =
      b.app ⊤ (f.appTop (1 : Γ(Y, ⊤)))
    rw [map_one]
    exact hb.symm
  rw [h, Iso.inv_hom_id_assoc]
  exact hb

/-- Arbitrary pullback preserves the usual scalar nonvanishing open. -/
theorem nonvanishing_pullback_scalar (f : X ⟶ Y) (a : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f a) = f ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing a := by
  have h := AbelianModuli.HilbertConstruction.Ample.Powers.sectionNonvanishing_comp_iso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f a) (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f)
  rw [AbelianModuli.HilbertConstruction.Scalar.Nonvanishing.sectionNonvanishing_scalar] at h
  have hv : AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue X
      (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f a ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom) =
        f.appTop (AbelianModuli.HilbertConstruction.Frame.Coordinates.structureModuleEndValue Y a) := by
    simpa only [AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection, Category.assoc] using value_pullback f a
  rw [hv] at h
  rw [← h, AbelianModuli.HilbertConstruction.Scalar.Nonvanishing.sectionNonvanishing_scalar, f.preimage_basicOpen_top]

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackScalarsValue.Construction.PullbackScalars
