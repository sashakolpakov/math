import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.EndTransferBaseChange

/-! # End Transfer Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.EndTransferCompatibility

noncomputable section

/-! Compatibility of a proposed scalar transfer can be transported through compositions and equal maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

theorem localLineEndTransfer_map_comp (f : X ⟶ Y) (g : Y ⟶ Z) {P : Z.Modules}
    (a : End (Line.Bundles.structureModule Z)) (φ : End P)
    (e : Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback g).obj P)
    (h : (Scheme.Modules.pullback g).map a = LineBundleEndTransfer.localLineEndTransfer g φ e) :
    (Scheme.Modules.pullback (f ≫ g)).map a =
      LineBundleEndTransfer.localLineEndTransfer (f ≫ g) φ (TensorPowerValues.refinedPullbackFrame f g e) :=
  (EndTransferBaseChange.pullbackEnd_comp_conjugation f g a).symm.trans
    ((congrArg (fun k => (Scheme.Modules.pullbackComp f g).inv.app (Line.Bundles.structureModule Z) ≫
      (Scheme.Modules.pullback f).map k ≫
        (Scheme.Modules.pullbackComp f g).hom.app (Line.Bundles.structureModule Z)) h).trans
      (EndTransferBaseChange.localLineEndTransfer_comp_arbitrary f g φ e))

theorem localLineEndTransfer_map_congr {f f' : X ⟶ Y} (h : f = f') {P : Y.Modules}
    (a : End (Line.Bundles.structureModule Y)) (φ : End P)
    (e : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj P)
    (e' : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f').obj P)
    (H : (Scheme.Modules.pullback f).map a = LineBundleEndTransfer.localLineEndTransfer f φ e) :
    (Scheme.Modules.pullback f').map a = LineBundleEndTransfer.localLineEndTransfer f' φ e' := by
  subst f'
  exact H.trans (LineBundleEndTransfer.localLineEndTransfer_independent f φ e e')

theorem localLineEndTransfer_map_of_comp (f : X ⟶ Y) (g : Y ⟶ Z) {P : Z.Modules}
    (a : End (Line.Bundles.structureModule Z)) (φ : End P)
    (e : Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback g).obj P)
    (h : (Scheme.Modules.pullback (f ≫ g)).map a =
      LineBundleEndTransfer.localLineEndTransfer (f ≫ g) φ (TensorPowerValues.refinedPullbackFrame f g e)) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map a) =
      (Scheme.Modules.pullback f).map (LineBundleEndTransfer.localLineEndTransfer g φ e) := by
  apply (cancel_epi ((Scheme.Modules.pullbackComp f g).inv.app (Line.Bundles.structureModule Z))).mp
  apply (cancel_mono ((Scheme.Modules.pullbackComp f g).hom.app (Line.Bundles.structureModule Z))).mp
  simpa only [Category.assoc] using
    (EndTransferBaseChange.pullbackEnd_comp_conjugation f g a).trans
      (h.trans (EndTransferBaseChange.localLineEndTransfer_comp_arbitrary f g φ e).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.EndTransferCompatibility
