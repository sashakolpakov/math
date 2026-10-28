import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AmpleClosedIs
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.PowerStability

/-! # Ample -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.Ample.Construction.AmpleFinite

noncomputable section

/-! Ample torsion line bundles force finiteness even on nonreduced disconnected proper schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem of_trivial {K : Type u} [Field K]
    (X : Over (Spec (.of K))) [IsProper X.hom]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (hL : L.IsAmple) (e : L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left) :
    IsFinite X.hom := by
  let U : X.left.Opens := ⊤
  let eU : (L.pullback U.ι).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme :=
    (Scheme.Modules.pullback U.ι).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso U.ι
  exact AmpleClosedIs.Construction.AmpleClosed.isFinite X X L hL U eU (𝟙 X) Function.injective_id
    (fun _ _ => trivial)

theorem of_torsion {K : Type u} [Field K]
    (X : Over (Spec (.of K))) [IsProper X.hom]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) (hL : L.IsAmple) (n : ℕ) (hn : 0 < n)
    (e : (L.tensorPower n).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X.left) : IsFinite X.hom :=
  of_trivial X (L.tensorPower n) (hL.tensorPower n hn) e

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.Ample.Construction.AmpleFinite
