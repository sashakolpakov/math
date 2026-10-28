import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ClosedReductionLayer
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.NilpotentModuleLayer

/-! # Reduction Kernel -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.ReductionKernel

noncomputable section

/-! The actual global sections of the canonical reduction kernel on an
affine scheme agree with the kernel of scalar extension. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

def affineReductionKernelSectionsIso
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent] :
    (Quotients.FiniteDescent.AffineSectionIs.Construction.AffineSectionAdjunction.sections Y).obj (ClosedReductionLayer.closedReductionKernel f M) ≅
      ModuleCat.of Γ(Y, ⊤)
        ((ModuleCat.extendRestrictScalarsAdj f.appTop.hom).unit.app
          ((Quotients.FiniteDescent.AffineSectionIs.Construction.AffineSectionAdjunction.sections Y).obj M)).hom.ker := by
  let F := SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op ⊤)
  have : F.Additive := by
    dsimp [F, SheafOfModules.evaluation]
    infer_instance
  have : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  let A := F.obj M
  let P := (Scheme.Modules.pullback f).obj M
  let G := ModuleCat.restrictScalars f.appTop.hom
  let adj := ModuleCat.extendRestrictScalarsAdj f.appTop.hom
  let e₁ := (Quotients.FiniteDescent.AffineSectionIs.Construction.AffineSectionAdjunction.pushforwardIso f).app P
  let e₂ := G.mapIso (Quotients.FiniteDescent.AffineGeometric.Construction.AffineGeometricSections.iso f M)
  let e := e₁ ≪≫ e₂.symm
  have hn : adj.unit.app A ≫ e₂.hom = F.map (ClosedReductionLayer.closedModuleUnit f M) ≫ e₁.hom := by
    exact Quotients.FiniteDescent.AffineGeometric.Construction.AffineGeometricSections.normalization f M
  have hw : F.map (ClosedReductionLayer.closedModuleUnit f M) ≫ e.hom = (Iso.refl A).hom ≫ adj.unit.app A := by
    change F.map (ClosedReductionLayer.closedModuleUnit f M) ≫ (e₁.hom ≫ e₂.inv) = 𝟙 A ≫ adj.unit.app A
    rw [← Category.assoc, ← hn]
    simp
  exact PreservesKernel.iso F (ClosedReductionLayer.closedModuleUnit f M) ≪≫
    kernel.mapIso (F.map (ClosedReductionLayer.closedModuleUnit f M)) (adj.unit.app A) (Iso.refl A) e hw ≪≫
    ModuleCat.kernelIsoKer (adj.unit.app A)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.ReductionKernel
