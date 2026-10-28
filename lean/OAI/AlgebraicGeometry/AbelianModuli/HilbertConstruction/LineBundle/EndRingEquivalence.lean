import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EndRing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ScalarBaseChange

/-! # End Ring Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The endomorphism ring of any line bundle is the ring of global regular functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {M N : X.Modules}

theorem LineBundle.EndRingEquivalence.framedEndScalar_globalModuleScalar (e : Line.Bundles.structureModule X ≅ M) (r : Γ(X, ⊤)) :
    LineBundle.EndScalars.framedEndScalar e (Global.ModuleScalars.globalModuleScalar M r) = Global.ModuleScalars.globalModuleScalar (Line.Bundles.structureModule X) r := by
  unfold LineBundle.EndScalars.framedEndScalar
  rw [← Category.assoc, ← Global.ModuleScalars.globalModuleScalar_natural r e.hom, Category.assoc,
    e.hom_inv_id, Category.comp_id]

theorem LineBundle.EndRingEquivalence.frameTransferEnd_globalModuleScalar (e : Line.Bundles.structureModule X ≅ M)
    (d : Line.Bundles.structureModule X ≅ N) (r : Γ(X, ⊤)) :
    Frame.EndTransfer.frameTransferEnd e d (Global.ModuleScalars.globalModuleScalar M r) = Global.ModuleScalars.globalModuleScalar N r := by
  unfold Frame.EndTransfer.frameTransferEnd
  rw [LineBundle.EndRingEquivalence.framedEndScalar_globalModuleScalar, ← Category.assoc,
    ← Global.ModuleScalars.globalModuleScalar_natural r d.inv, Category.assoc, d.inv_hom_id, Category.comp_id]

theorem Line.Bundles.LineBundle.endTransfer_globalModuleScalar (L : Line.Bundles.LineBundle X) (r : Γ(X, ⊤)) :
    L.endTransfer (Global.ModuleScalars.globalModuleScalar L.sheaf r) = Global.ModuleScalars.globalModuleScalar (Line.Bundles.structureModule X) r := by
  apply Module.MapCoverEquality.moduleMap_eq_of_pullback_cover (LineBundle.EndGluing.lineEndFrameCover L) (LineBundle.EndGluing.lineEndFrameCover_covers L)
  intro i
  dsimp only [LineBundle.EndGluing.lineEndFrameCover]
  rw [L.endTransfer_pullback]
  change Frame.EndTransfer.frameTransferEnd i.frame (Line.Bundles.structureModulePullbackIso i.openSet.ι).symm
    ((Scheme.Modules.pullback i.openSet.ι).map (Global.ModuleScalars.globalModuleScalar L.sheaf r)) =
      (Scheme.Modules.pullback i.openSet.ι).map (Global.ModuleScalars.globalModuleScalar (Line.Bundles.structureModule X) r)
  rw [Global.ScalarBaseChange.globalModuleScalar_pullback, Global.ScalarBaseChange.globalModuleScalar_pullback, LineBundle.EndRingEquivalence.frameTransferEnd_globalModuleScalar]

theorem Line.Bundles.LineBundle.endScalar_globalModuleScalar (L : Line.Bundles.LineBundle X) (r : Γ(X, ⊤)) :
    L.endScalar (Global.ModuleScalars.globalModuleScalar L.sheaf r) = r := by
  rw [Line.Bundles.LineBundle.endScalar, L.endTransfer_globalModuleScalar, Global.ModuleScalars.globalModuleScalar_structure_value]

theorem Line.Bundles.LineBundle.endScalar_surjective (L : Line.Bundles.LineBundle X) : Function.Surjective L.endScalar :=
  fun r => ⟨Global.ModuleScalars.globalModuleScalar L.sheaf r, L.endScalar_globalModuleScalar r⟩

def Line.Bundles.LineBundle.endScalarRingEquiv (L : Line.Bundles.LineBundle X) : End L.sheaf ≃+* Γ(X, ⊤) :=
  RingEquiv.ofBijective L.endScalarRingHom ⟨L.endScalar_injective, L.endScalar_surjective⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
