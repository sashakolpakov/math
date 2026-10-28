import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EndGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.OpenIsomorphismGluing

/-! # End Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A line-bundle endomorphism is determined by its global scalar transfer. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

theorem LineBundle.EndRecovery.pullbackModuleRestrictionMap_injective (f : X ⟶ Y) [IsOpenImmersion f]
    (M N : Y.Modules) : Function.Injective (OpenPullback.ModuleValues.pullbackModuleRestrictionMap f (M := M) (N := N)) := by
  intro φ ψ h
  unfold OpenPullback.ModuleValues.pullbackModuleRestrictionMap at h
  exact (cancel_epi ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M)).mp
    ((cancel_mono ((Scheme.Modules.restrictFunctorIsoPullback f).inv.app N)).mp
      (by simpa only [Category.assoc] using h))

theorem LineBundle.EndRecovery.pullbackModuleRestrictionMap_global (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} (φ : M ⟶ N) :
    OpenPullback.ModuleValues.pullbackModuleRestrictionMap f ((Scheme.Modules.pullback f).map φ) =
      (Scheme.Modules.restrictFunctor f).map φ := by
  unfold OpenPullback.ModuleValues.pullbackModuleRestrictionMap
  rw [← Category.assoc, ← (Scheme.Modules.restrictFunctorIsoPullback f).hom.naturality φ,
    Category.assoc, (Scheme.Modules.restrictFunctorIsoPullback f).hom_inv_id_app, Category.comp_id]

theorem LineBundle.EndRecovery.frameTransferEnd_injective {M N : X.Modules}
    (e : Line.Bundles.structureModule X ≅ M) (d : Line.Bundles.structureModule X ≅ N) :
    Function.Injective (Frame.EndTransfer.frameTransferEnd e d) := by
  intro φ ψ h
  apply LineBundle.EndScalars.framedEndScalar_injective e
  exact (cancel_epi d.inv).mp ((cancel_mono d.hom).mp
    (by simpa only [Frame.EndTransfer.frameTransferEnd, Category.assoc] using h))

theorem Line.Bundles.LineBundle.endTransfer_pullback (L : Line.Bundles.LineBundle X) (φ : End L.sheaf) (i : LineBundle.EndGluing.LineEndFrameOpen L) :
    (Scheme.Modules.pullback i.openSet.ι).map (L.endTransfer φ) =
      Local.LineBundleEndTransfer.localLineEndTransfer i.openSet.ι φ i.frame := by
  apply LineBundle.EndRecovery.pullbackModuleRestrictionMap_injective i.openSet.ι (Line.Bundles.structureModule X) (Line.Bundles.structureModule X)
  rw [LineBundle.EndRecovery.pullbackModuleRestrictionMap_global, L.endTransfer_restrict]

theorem Line.Bundles.LineBundle.endTransfer_injective (L : Line.Bundles.LineBundle X) : Function.Injective L.endTransfer := by
  intro φ ψ h
  apply Module.MapCoverEquality.moduleMap_eq_of_pullback_cover (LineBundle.EndGluing.lineEndFrameCover L) (LineBundle.EndGluing.lineEndFrameCover_covers L)
  intro i
  apply LineBundle.EndRecovery.frameTransferEnd_injective i.frame (Line.Bundles.structureModulePullbackIso i.openSet.ι).symm
  exact (L.endTransfer_pullback φ i).symm.trans
    ((congrArg ((Scheme.Modules.pullback i.openSet.ι).map) h).trans (L.endTransfer_pullback ψ i))

theorem Line.Bundles.LineBundle.endTransfer_isIso (L : Line.Bundles.LineBundle X) (φ : End L.sheaf) [IsIso φ] :
    IsIso (L.endTransfer φ) := by
  apply (LineBundle.EndGluing.lineEndTransferData L φ).glue_isIso (LineBundle.EndGluing.lineEndFrameCover_covers L)
  intro i
  change IsIso (OpenPullback.ModuleValues.pullbackModuleRestrictionMap i.openSet.ι (Local.LineBundleEndTransfer.localLineEndTransfer i.openSet.ι φ i.frame))
  unfold OpenPullback.ModuleValues.pullbackModuleRestrictionMap Local.LineBundleEndTransfer.localLineEndTransfer Frame.EndTransfer.frameTransferEnd LineBundle.EndScalars.framedEndScalar
  infer_instance

def Line.Bundles.LineBundle.endScalar (L : Line.Bundles.LineBundle X) (φ : End L.sheaf) : Γ(X, ⊤) :=
  Frame.Coordinates.structureModuleEndValue X (L.endTransfer φ)

theorem Line.Bundles.LineBundle.endScalar_injective (L : Line.Bundles.LineBundle X) : Function.Injective L.endScalar :=
  (Global.Sections.structureModuleEndValue_injective X).comp L.endTransfer_injective

theorem Line.Bundles.LineBundle.endScalar_isUnit (L : Line.Bundles.LineBundle X) (φ : End L.sheaf) [IsIso φ] : IsUnit (L.endScalar φ) :=
  Global.Sections.structureModuleEnd_isIso_iff (L.endTransfer φ) |>.mp (L.endTransfer_isIso φ)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
