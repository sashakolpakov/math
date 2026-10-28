import OAI.AlgebraicGeometry.Picard.ThetaConstruction.CoefficientLineDescent

/-! # Noetherian Line Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.NoetherianLineModel

noncomputable section

/-! A line bundle on the original Cartesian family descends to finite
coefficients with an isomorphism on that same family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.ThetaConstruction.CoefficientLineDescent.Geometric.CoefficientLines

theorem exists_finiteType_cartesian_line_model
    (C R : Type) [CommRing C] [CommRing R] [Algebra C R] [IsNoetherianRing C]
    (X : Over (Spec (.of R))) (Y : Over (Spec (.of C))) [IsProper Y.hom]
    (q : X.left ⟶ Y.left)
    (H : IsPullback q X.hom Y.hom (Picard.ThetaConstruction.CoefficientLineDescent.Geometric.CoefficientLines.genericBase C R)) (L : Line.Bundles.LineBundle X.left) :
    ∃ (s : Finset R)
      (K : Line.Bundles.LineBundle ((Over.pullback (Picard.ThetaConstruction.CoefficientLineDescent.Geometric.CoefficientLines.stageBase C R s)).obj Y).left)
      (a : X.left ⟶ ((Over.pullback (Picard.ThetaConstruction.CoefficientLineDescent.Geometric.CoefficientLines.stageBase C R s)).obj Y).left),
      IsPullback a X.hom ((Over.pullback (Picard.ThetaConstruction.CoefficientLineDescent.Geometric.CoefficientLines.stageBase C R s)).obj Y).hom
        (Picard.ThetaConstruction.CoefficientLineDescent.Geometric.CoefficientLines.stageProjection C R s) ∧
      Nonempty ((K.pullback a).sheaf ≅ L.sheaf) := by
  let e : X ≅ (Over.pullback (Picard.ThetaConstruction.CoefficientLineDescent.Geometric.CoefficientLines.genericBase C R)).obj Y :=
    Over.isoMk H.isoPullback H.isoPullback_hom_snd
  let L' := L.pullback e.inv.left
  obtain ⟨s, K, ⟨eK⟩⟩ := Picard.ThetaConstruction.CoefficientLineDescent.Geometric.CoefficientLines.exists_line_stage C R Y L'
  let a := e.hom.left ≫ Picard.ThetaConstruction.CoefficientLineDescent.Geometric.CoefficientLines.modelProjection C R Y s
  have he : IsIso e.hom.left := (Over.forget (Spec (.of R))).map_isIso e.hom
  have hp : IsPullback e.hom.left X.hom
      ((Over.pullback (Picard.ThetaConstruction.CoefficientLineDescent.Geometric.CoefficientLines.genericBase C R)).obj Y).hom (𝟙 (Spec (.of R))) :=
    IsPullback.of_horiz_isIso ⟨e.hom.w.trans (Category.comp_id _).symm⟩
  have ha : IsPullback a X.hom ((Over.pullback (Picard.ThetaConstruction.CoefficientLineDescent.Geometric.CoefficientLines.stageBase C R s)).obj Y).hom
      (Picard.ThetaConstruction.CoefficientLineDescent.Geometric.CoefficientLines.stageProjection C R s) := by
    have h : IsPullback a X.hom ((Over.pullback (Picard.ThetaConstruction.CoefficientLineDescent.Geometric.CoefficientLines.stageBase C R s)).obj Y).hom
        (𝟙 (Spec (.of R)) ≫ Picard.ThetaConstruction.CoefficientLineDescent.Geometric.CoefficientLines.stageProjection C R s) :=
      hp.paste_horiz (Picard.ThetaConstruction.CoefficientLineDescent.Geometric.CoefficientLines.modelProjection_cartesian C R Y s)
    simpa only [Category.id_comp] using h
  refine ⟨s, K, a, ha, ⟨?_⟩⟩
  have hid : e.hom.left ≫ e.inv.left = 𝟙 X.left :=
    congrArg Over.Hom.left e.hom_inv_id
  exact (Scheme.Modules.pullbackComp e.hom.left (Picard.ThetaConstruction.CoefficientLineDescent.Geometric.CoefficientLines.modelProjection C R Y s)).symm.app K.sheaf ≪≫
    (Scheme.Modules.pullback e.hom.left).mapIso eK ≪≫
    (Scheme.Modules.pullbackComp e.hom.left e.inv.left).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr hid).app L.sheaf ≪≫
    (Scheme.Modules.pullbackId X.left).app L.sheaf

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.NoetherianLineModel
