import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EndRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.EndTransferRing

/-! # End Ring -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The global scalar of a line-bundle endomorphism is an injective ring homomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

def LineBundle.EndRing.moduleFunctorEndRingHom (F : X.Modules ⥤ Y.Modules) [F.Additive] (M : X.Modules) :
    End M →+* End (F.obj M) where
  toFun := F.map
  map_one' := F.map_id M
  map_mul' φ ψ := F.map_comp ψ φ
  map_zero' := F.map_zero M M
  map_add' _ _ := F.map_add

def LineBundle.EndRing.localLineEndTransferRingHom (f : X ⟶ Y) {M : Y.Modules}
    (e : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj M) :
    End M →+* End ((Scheme.Modules.pullback f).obj (Line.Bundles.structureModule Y)) :=
  (Frame.EndTransferRing.frameTransferEndRingHom e (Line.Bundles.structureModulePullbackIso f).symm).comp
    (LineBundle.EndRing.moduleFunctorEndRingHom (Scheme.Modules.pullback f) M)

def Line.Bundles.LineBundle.endTransferRingHom (L : Line.Bundles.LineBundle X) : End L.sheaf →+* End (Line.Bundles.structureModule X) where
  toFun := L.endTransfer
  map_one' := by
    apply Module.MapCoverEquality.moduleMap_eq_of_pullback_cover (LineBundle.EndGluing.lineEndFrameCover L) (LineBundle.EndGluing.lineEndFrameCover_covers L)
    intro i
    dsimp only [LineBundle.EndGluing.lineEndFrameCover]
    rw [L.endTransfer_pullback]
    exact ((LineBundle.EndRing.localLineEndTransferRingHom i.openSet.ι i.frame).map_one).trans
      ((Scheme.Modules.pullback i.openSet.ι).map_id (Line.Bundles.structureModule X)).symm
  map_mul' φ ψ := by
    apply Module.MapCoverEquality.moduleMap_eq_of_pullback_cover (LineBundle.EndGluing.lineEndFrameCover L) (LineBundle.EndGluing.lineEndFrameCover_covers L)
    intro i
    dsimp only [LineBundle.EndGluing.lineEndFrameCover]
    have h := (LineBundle.EndRing.moduleFunctorEndRingHom (Scheme.Modules.pullback i.openSet.ι)
      (Line.Bundles.structureModule X)).map_mul (L.endTransfer φ) (L.endTransfer ψ)
    change (Scheme.Modules.pullback i.openSet.ι).map (L.endTransfer ψ ≫ L.endTransfer φ) =
      (Scheme.Modules.pullback i.openSet.ι).map (L.endTransfer ψ) ≫
        (Scheme.Modules.pullback i.openSet.ι).map (L.endTransfer φ) at h
    rw [L.endTransfer_pullback, L.endTransfer_pullback] at h
    rw [L.endTransfer_pullback]
    exact ((LineBundle.EndRing.localLineEndTransferRingHom i.openSet.ι i.frame).map_mul φ ψ).trans h.symm
  map_zero' := by
    apply Module.MapCoverEquality.moduleMap_eq_of_pullback_cover (LineBundle.EndGluing.lineEndFrameCover L) (LineBundle.EndGluing.lineEndFrameCover_covers L)
    intro i
    dsimp only [LineBundle.EndGluing.lineEndFrameCover]
    rw [L.endTransfer_pullback]
    exact ((LineBundle.EndRing.localLineEndTransferRingHom i.openSet.ι i.frame).map_zero).trans
      (LineBundle.EndRing.moduleFunctorEndRingHom (Scheme.Modules.pullback i.openSet.ι) (Line.Bundles.structureModule X)).map_zero.symm
  map_add' φ ψ := by
    apply Module.MapCoverEquality.moduleMap_eq_of_pullback_cover (LineBundle.EndGluing.lineEndFrameCover L) (LineBundle.EndGluing.lineEndFrameCover_covers L)
    intro i
    dsimp only [LineBundle.EndGluing.lineEndFrameCover]
    have h := (LineBundle.EndRing.moduleFunctorEndRingHom (Scheme.Modules.pullback i.openSet.ι)
      (Line.Bundles.structureModule X)).map_add (L.endTransfer φ) (L.endTransfer ψ)
    change (Scheme.Modules.pullback i.openSet.ι).map (L.endTransfer φ + L.endTransfer ψ) =
      (Scheme.Modules.pullback i.openSet.ι).map (L.endTransfer φ) +
        (Scheme.Modules.pullback i.openSet.ι).map (L.endTransfer ψ) at h
    rw [L.endTransfer_pullback, L.endTransfer_pullback] at h
    rw [L.endTransfer_pullback]
    exact ((LineBundle.EndRing.localLineEndTransferRingHom i.openSet.ι i.frame).map_add φ ψ).trans h.symm

def Line.Bundles.LineBundle.endScalarRingHom (L : Line.Bundles.LineBundle X) : End L.sheaf →+* Γ(X, ⊤) :=
  (Frame.Coordinates.structureModuleEndValue X).comp L.endTransferRingHom

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
