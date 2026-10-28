import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.LineBundleEndTransfer

/-! # End Transfer Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.EndTransferBaseChange

noncomputable section

/-! Scalar transfers through frames commute with arbitrary iterated scheme pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

theorem pullbackEnd_comp_conjugation (f : X ⟶ Y) (g : Y ⟶ Z) {P : Z.Modules} (φ : End P) :
    (Scheme.Modules.pullbackComp f g).inv.app P ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map φ) ≫
        (Scheme.Modules.pullbackComp f g).hom.app P =
          (Scheme.Modules.pullback (f ≫ g)).map φ := by
  have hn : (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map φ) ≫
      (Scheme.Modules.pullbackComp f g).hom.app P =
        (Scheme.Modules.pullbackComp f g).hom.app P ≫
          (Scheme.Modules.pullback (f ≫ g)).map φ :=
    (Scheme.Modules.pullbackComp f g).hom.naturality φ
  exact (congrArg (fun a => (Scheme.Modules.pullbackComp f g).inv.app P ≫ a) hn).trans
    ((Scheme.Modules.pullbackComp f g).inv_hom_id_app_assoc P _)

theorem localLineEndTransfer_comp_arbitrary (f : X ⟶ Y) (g : Y ⟶ Z) {P : Z.Modules}
    (φ : End P) (e : Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback g).obj P) :
    (Scheme.Modules.pullbackComp f g).inv.app (Line.Bundles.structureModule Z) ≫
      (Scheme.Modules.pullback f).map (LineBundleEndTransfer.localLineEndTransfer g φ e) ≫
        (Scheme.Modules.pullbackComp f g).hom.app (Line.Bundles.structureModule Z) =
      LineBundleEndTransfer.localLineEndTransfer (f ≫ g) φ (TensorPowerValues.refinedPullbackFrame f g e) := by
  let c := (Scheme.Modules.pullbackComp f g).app P
  let b := (Scheme.Modules.pullbackComp f g).app (Line.Bundles.structureModule Z)
  let d := (Line.Bundles.structureModulePullbackIso g).symm
  have hφ : c.inv ≫ (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map φ) ≫ c.hom =
      (Scheme.Modules.pullback (f ≫ g)).map φ := pullbackEnd_comp_conjugation f g φ
  have h := Frame.EndTransfer.frameTransferEnd_transport (LineBundle.EndScalars.pulledBackFrame f e) (LineBundle.EndScalars.pulledBackFrame f d) c b
    ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map φ))
  rw [hφ, Frame.EndTransfer.frameTransferEnd_pullback] at h
  exact h.symm.trans (Frame.EndTransfer.frameTransferEnd_independent _ _ _ _ _)

theorem localLineEndTransfer_congr {f f' : X ⟶ Y} (h : f = f') {P : Y.Modules} (φ : End P)
    (e : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj P)
    (e' : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f').obj P) :
    (Scheme.Modules.pullbackCongr h).inv.app (Line.Bundles.structureModule Y) ≫
      LineBundleEndTransfer.localLineEndTransfer f φ e ≫ (Scheme.Modules.pullbackCongr h).hom.app (Line.Bundles.structureModule Y) =
        LineBundleEndTransfer.localLineEndTransfer f' φ e' := by
  subst f'
  simpa only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_inv, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp, Category.comp_id] using
    LineBundleEndTransfer.localLineEndTransfer_independent f φ e e'

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.EndTransferBaseChange
