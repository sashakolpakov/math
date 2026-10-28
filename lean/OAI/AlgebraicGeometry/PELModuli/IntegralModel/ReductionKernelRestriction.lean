import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ClosedReductionLayer
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleRestrictLimits

/-! # Reduction Kernel Restriction -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ReductionKernelRestriction

noncomputable section

/-! The actual canonical reduction kernel commutes with restriction to
an arbitrary open subset, through the original adjunction-unit square. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

def closedReductionKernelRestrictIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (M : Y.Modules) :
    (ClosedReductionLayer.closedReductionKernel f M).restrict U.ι ≅
      ClosedReductionLayer.closedReductionKernel (f ∣_ U) (M.restrict U.ι) := by
  let F := Scheme.Modules.restrictFunctor U.ι
  have : PreservesLimits F := SheafCohomology.Projective.ModuleRestrictLimits.Scheme.Modules.restrictFunctor_preservesLimits U.ι
  let A := M.restrict U.ι
  let P := (Scheme.Modules.pullback f).obj M
  have := Quotients.FiniteDescent.OpenPullbackIs.Construction.OpenPullbackSquare.openBaseChangeMap_isIso f U
  let e₁ := asIso ((Quotients.FiniteDescent.OpenPullbackIs.Construction.OpenPullbackSquare.openBaseChangeMap f U).app P)
  let e₂ := (Scheme.Modules.pushforward (f ∣_ U)).mapIso
    ((Quotients.FiniteDescent.OpenPullbackIs.Construction.OpenPullbackSquare.adjointPullbackSquare f U).app M)
  let e := e₁ ≪≫ e₂.symm
  have hn : F.map (ClosedReductionLayer.closedModuleUnit f M) ≫ e₁.hom =
      ClosedReductionLayer.closedModuleUnit (f ∣_ U) A ≫ e₂.hom :=
    Quotients.FiniteDescent.OpenPullbackIs.Construction.OpenPullbackSquare.unit_square f U M
  have hw : F.map (ClosedReductionLayer.closedModuleUnit f M) ≫ e.hom =
      (Iso.refl A).hom ≫ ClosedReductionLayer.closedModuleUnit (f ∣_ U) A := by
    change F.map (ClosedReductionLayer.closedModuleUnit f M) ≫ (e₁.hom ≫ e₂.inv) =
      𝟙 A ≫ ClosedReductionLayer.closedModuleUnit (f ∣_ U) A
    rw [← Category.assoc, hn]
    simp
  exact PreservesKernel.iso F (ClosedReductionLayer.closedModuleUnit f M) ≪≫
    kernel.mapIso (F.map (ClosedReductionLayer.closedModuleUnit f M))
      (ClosedReductionLayer.closedModuleUnit (f ∣_ U) A) (Iso.refl A) e hw

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ReductionKernelRestriction
