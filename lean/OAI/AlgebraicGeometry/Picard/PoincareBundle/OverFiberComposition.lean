import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.DescentReindex
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.OrdinaryDatum
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

/-! # Over Fiber Composition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.OverFiberComposition

noncomputable section

/-!
# Explicit geometric composition formulas for fibers over a fixed base
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition

variable {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) (P : Y.left.Modules)

/-- The native composition comparison over the base is exactly the actual geometric pullback comparison. -/
theorem fiberIsoTo_eq {T : Over S} (x : T ⟶ X) (q : T ⟶ Y) (hx : x ≫ f = q) :
    PullbackFiberComposition.fiberIsoTo (Geometric.KernelLinearization.overModulePullbacks S) f P x q hx =
      (Scheme.Modules.pullbackComp x.left f.left ≪≫
        Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hx)).app P :=
  (Canonical.DescentReindex.fiberIsoTo_eq (Over.forget S) Geometric.KernelLinearization.modulePullbacks f P x q hx).trans
    (Recovered.OrdinaryDatum.Ordinary.fiberIsoTo_eq f.left P x.left q.left (congrArg Over.Hom.left hx))

/-- For a composite point the native comparison is the usual geometric composition isomorphism. -/
theorem fiberIso_eq {T : Over S} (x : T ⟶ X) :
    PullbackFiberComposition.fiberIso (Geometric.KernelLinearization.overModulePullbacks S) f P x = (Scheme.Modules.pullbackComp x.left f.left).app P := by
  have h := fiberIsoTo_eq f P x (x ≫ f) rfl
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.trans_refl] at h
  exact h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.OverFiberComposition
