import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ReductionLayer
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NilpotentModuleLayer

/-! # Reduction Kernel Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ReductionKernelSections

noncomputable section

/-! The actual global sections of the canonical reduction kernel on an
affine scheme agree with the kernel of scalar extension. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

private theorem undo_iso_factor {C : Type*} [Category C]
    {A B D : C} (e : B ≅ D) (a : A ⟶ B) (b : A ⟶ D)
    (h : a ≫ e.hom = b) : b ≫ e.inv = 𝟙 A ≫ a := by
  rw [← h]
  simp

def affineReductionKernelSectionsIso
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent] :
    (SectionAdjunction.AffineSectionAdjunction.sections Y).obj (Closed.ReductionLayer.closedReductionKernel f M) ≅
      ModuleCat.of Γ(Y, ⊤)
        ((ModuleCat.extendRestrictScalarsAdj f.appTop.hom).unit.app
          ((SectionAdjunction.AffineSectionAdjunction.sections Y).obj M)).hom.ker := by
  let F : Y.Modules ⥤ ModuleCat.{u} Γ(Y, ⊤) :=
    SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op ⊤)
  have : F.Additive := by
    constructor
    intro A B a b
    apply ModuleCat.hom_ext
    ext x
    rfl
  have : PreservesFiniteLimits F :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits Y.ringCatSheaf (Opposite.op ⊤)
  have : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  let A := F.obj M
  let P := (Scheme.Modules.pullback f).obj M
  let G := ModuleCat.restrictScalars f.appTop.hom
  let adj := ModuleCat.extendRestrictScalarsAdj f.appTop.hom
  let e₁ := (SectionAdjunction.AffineSectionAdjunction.pushforwardIso f).app P
  let e₂ := G.mapIso (GeometricSections.AffineGeometricSections.iso f M)
  let e := e₁ ≪≫ e₂.symm
  have hn : adj.unit.app A ≫ e₂.hom = F.map (Closed.ReductionLayer.closedModuleUnit f M) ≫ e₁.hom := by
    exact GeometricSections.AffineGeometricSections.normalization f M
  have hw : F.map (Closed.ReductionLayer.closedModuleUnit f M) ≫ e.hom = (Iso.refl A).hom ≫ adj.unit.app A := by
    change F.map (Closed.ReductionLayer.closedModuleUnit f M) ≫ (e₁.hom ≫ e₂.inv) = 𝟙 A ≫ adj.unit.app A
    exact (Category.assoc (F.map (Closed.ReductionLayer.closedModuleUnit f M)) e₁.hom e₂.inv).symm.trans
      (undo_iso_factor e₂ (adj.unit.app A) (F.map (Closed.ReductionLayer.closedModuleUnit f M) ≫ e₁.hom) hn)
  exact PreservesKernel.iso F (Closed.ReductionLayer.closedModuleUnit f M) ≪≫
    kernel.mapIso (F.map (Closed.ReductionLayer.closedModuleUnit f M)) (adj.unit.app A) (Iso.refl A) e hw ≪≫
    ModuleCat.kernelIsoKer (adj.unit.app A)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ReductionKernelSections
