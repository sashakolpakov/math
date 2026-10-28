import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.OpenModuleCech

/-! # Object Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.ObjectDescent.OpenModuleObjectDescent

noncomputable section

/-! Effective Zariski descent of native module-sheaf objects. Local
modules are extended by open direct image; the genuine native descent
maps give the matching-section object and its local recovery. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ModuleDescentRecovery.NativeModuleDescentRecovery

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
  (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun i => (U i).ι))

abbrev extension (i : ι) : X.Modules := (Scheme.Modules.pushforward (U i).ι).obj (D.obj i)

def restrictionRecovery (i : ι) : (extension U D i).restrict (U i).ι ≅ D.obj i :=
  (asIso (Scheme.Modules.restrictAdjunction (U i).ι).counit).app
    (show (U i).toScheme.Modules from D.obj i)

def nativeRecovery (i : ι) : (Scheme.Modules.pullback (U i).ι).obj (extension U D i) ≅ D.obj i :=
  (Scheme.Modules.restrictFunctorIsoPullback (U i).ι).symm.app (extension U D i) ≪≫
    restrictionRecovery U D i

def cech : OpenPullback.CechObjectDescent.OpenPullbackCechIsos U (extension U D) :=
  Intrinsic.OpenModuleCech.IntrinsicOpenModuleCech.cech U D (extension U D) (nativeRecovery U D)

/-- The actual glued module is the sheaf of matching sections. -/
def module : X.Modules := (cech U D).transitions.moduleSheaf

def module_recovery (i : ι) : (Scheme.Modules.pullback (U i).ι).obj (module U D) ≅ D.obj i :=
  (Scheme.Modules.restrictFunctorIsoPullback (U i).ι).symm.app (module U D) ≪≫
    (cech U D).transitions.recoveryIso i ≪≫ restrictionRecovery U D i

variable (hU : ∀ x : X, ∃ i, x ∈ U i)
  (hD : ∀ i, Picard.PoincareBundle.Line.Bundles.IsLine (D.obj i))

/-- Each given local object is retained as an actual original line. -/
def localLine (i : ι) : Line.Bundles.LineBundle (U i).toScheme := ⟨D.obj i, hD i⟩

/-- A native line descent datum is effective on every Zariski open
cover. No Noetherian or reducedness assumption is used here. -/
def lineBundle : Line.Bundles.LineBundle X :=
  (cech U D).lineBundle hU (localLine U D hD) (restrictionRecovery U D)

def lineBundle_recovery (i : ι) :
    ((OpenModuleObjectDescent.lineBundle U D hU hD).pullback (U i).ι).sheaf ≅ D.obj i :=
  (cech U D).lineBundle_recovery hU (localLine U D hD) (restrictionRecovery U D) i

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.ObjectDescent.OpenModuleObjectDescent
