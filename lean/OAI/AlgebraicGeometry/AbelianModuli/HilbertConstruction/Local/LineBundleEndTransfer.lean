import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.EndTransfer
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TensorPowerValues

/-! # Line Bundle End Transfer -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.LineBundleEndTransfer

noncomputable section

/-! Local transfer of a line-bundle endomorphism to the pulled-back structure module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} {M : Y.Modules}

def localLineEndTransfer (f : X ⟶ Y) (φ : End M)
    (e : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj M) :
    End ((Scheme.Modules.pullback f).obj (Line.Bundles.structureModule Y)) :=
  Frame.EndTransfer.frameTransferEnd e (Line.Bundles.structureModulePullbackIso f).symm ((Scheme.Modules.pullback f).map φ)

theorem localLineEndTransfer_independent (f : X ⟶ Y) (φ : End M)
    (e e' : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj M) :
    localLineEndTransfer f φ e = localLineEndTransfer f φ e' :=
  Frame.EndTransfer.frameTransferEnd_independent e e' _ _ _

theorem refineOpenPullbackMap_global (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] {P Q : Z.Modules} (φ : P ⟶ Q) :
    OpenPullback.Refinement.refineOpenPullbackMap f g ((Scheme.Modules.pullback g).map φ) =
      (Scheme.Modules.pullback (f ≫ g)).map φ := by
  unfold OpenPullback.Refinement.refineOpenPullbackMap
  have hn : (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map φ) ≫
      (Scheme.Modules.pullbackComp f g).hom.app Q =
        (Scheme.Modules.pullbackComp f g).hom.app P ≫
          (Scheme.Modules.pullback (f ≫ g)).map φ :=
    (Scheme.Modules.pullbackComp f g).hom.naturality φ
  exact (congrArg (fun a => (Scheme.Modules.pullbackComp f g).inv.app P ≫ a) hn).trans
    ((Scheme.Modules.pullbackComp f g).inv_hom_id_app_assoc P _)

theorem localLineEndTransfer_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] {P : Z.Modules} (φ : End P)
    (e : Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback g).obj P) :
    OpenPullback.Refinement.refineOpenPullbackMap f g (localLineEndTransfer g φ e) =
      localLineEndTransfer (f ≫ g) φ (TensorPowerValues.refinedPullbackFrame f g e) := by
  let c := (Scheme.Modules.pullbackComp f g).app P
  let b := (Scheme.Modules.pullbackComp f g).app (Line.Bundles.structureModule Z)
  let d := (Line.Bundles.structureModulePullbackIso g).symm
  have hφ : c.inv ≫ (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map φ) ≫ c.hom =
      (Scheme.Modules.pullback (f ≫ g)).map φ := refineOpenPullbackMap_global f g φ
  have h := Frame.EndTransfer.frameTransferEnd_transport (LineBundle.EndScalars.pulledBackFrame f e) (LineBundle.EndScalars.pulledBackFrame f d) c b
    ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map φ))
  rw [hφ, Frame.EndTransfer.frameTransferEnd_pullback] at h
  change b.inv ≫ (Scheme.Modules.pullback f).map (Frame.EndTransfer.frameTransferEnd e d
    ((Scheme.Modules.pullback g).map φ)) ≫ b.hom = _
  exact h.symm.trans (Frame.EndTransfer.frameTransferEnd_independent _ _ _ _ _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.LineBundleEndTransfer
