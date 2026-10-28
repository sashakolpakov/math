import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import Mathlib.Topology.Sheaves.Forget
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections

/-! # Ring Module Presheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.RingModulePresheaf

noncomputable section

/-! Sections of a module sheaf form a sheaf of modules over the ring of global functions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

def globalRingModulePresheaf (M : X.Modules) :
    TopCat.Presheaf (ModuleCat Γ(X, ⊤)) X :=
  (PresheafOfModules.forgetToPresheafModuleCat (.op (⊤ : X.Opens)) isTerminalTop.op).obj M.val

def globalRingModulePresheafForgetIso (M : X.Modules) :
    globalRingModulePresheaf M ⋙ forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat ≅ M.presheaf :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro U V f; ext m; rfl)

theorem globalRingModulePresheaf_isSheaf (M : X.Modules) :
    (globalRingModulePresheaf M).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp'
    (forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat) (globalRingModulePresheaf M)).mpr
  exact (TopCat.Presheaf.isSheaf_iso_iff (globalRingModulePresheafForgetIso M)).mpr M.isSheaf

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.RingModulePresheaf
