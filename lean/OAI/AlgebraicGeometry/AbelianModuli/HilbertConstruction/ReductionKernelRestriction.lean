import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ReductionLayer
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.RestrictionLimits

/-! # Reduction Kernel Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReductionKernelRestriction

noncomputable section

/-! The actual canonical reduction kernel commutes with restriction to
an arbitrary open subset, through the original adjunction-unit square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

def closedReductionKernelRestrictIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (M : Y.Modules) :
    (Closed.ReductionLayer.closedReductionKernel f M).restrict U.ι ≅
      Closed.ReductionLayer.closedReductionKernel (f ∣_ U) (M.restrict U.ι) := by
  let F := Scheme.Modules.restrictFunctor U.ι
  have : PreservesLimits F := Module.RestrictionLimits.moduleRestrictFunctor_preservesLimits U.ι
  let A := M.restrict U.ι
  let P := (Scheme.Modules.pullback f).obj M
  have := OpenModule.BaseChangeMate.OpenPullbackSquare.openBaseChangeMap_isIso f U
  let e₁ := asIso ((OpenModule.BaseChangeMate.OpenPullbackSquare.openBaseChangeMap f U).app P)
  let e₂ := (Scheme.Modules.pushforward (f ∣_ U)).mapIso
    ((OpenModule.PullbackSquare.OpenPullbackSquare.adjointPullbackSquare f U).app M)
  let e := e₁ ≪≫ e₂.symm
  have hn : F.map (Closed.ReductionLayer.closedModuleUnit f M) ≫ e₁.hom =
      Closed.ReductionLayer.closedModuleUnit (f ∣_ U) A ≫ e₂.hom :=
    OpenPullback.AdjunctionUnit.OpenPullbackSquare.unit_square f U M
  have hw : F.map (Closed.ReductionLayer.closedModuleUnit f M) ≫ e.hom =
      (Iso.refl A).hom ≫ Closed.ReductionLayer.closedModuleUnit (f ∣_ U) A := by
    change F.map (Closed.ReductionLayer.closedModuleUnit f M) ≫ (e₁.hom ≫ e₂.inv) =
      𝟙 A ≫ Closed.ReductionLayer.closedModuleUnit (f ∣_ U) A
    rw [← Category.assoc, hn]
    simp
  exact PreservesKernel.iso F (Closed.ReductionLayer.closedModuleUnit f M) ≪≫
    kernel.mapIso (F.map (Closed.ReductionLayer.closedModuleUnit f M))
      (Closed.ReductionLayer.closedModuleUnit (f ∣_ U) A) (Iso.refl A) e hw

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReductionKernelRestriction
