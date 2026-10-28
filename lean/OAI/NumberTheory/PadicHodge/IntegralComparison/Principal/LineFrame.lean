import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Line Frame -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.LineFrame

noncomputable section

/-! A frame of a quasicoherent line on an affine open induces one
frame on the entire principal-open presheaf. Its inverse sends a
function to that function times the restricted original generator. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (N : X.Modules) [N.IsQuasicoherent] (e : Γ(N, U) ≃ₗ[Γ(X, U)] Γ(X, U))

local instance sectionTower (r : SectionPresheaf.Index U) :
    IsScalarTower Γ(X, U) Γ(X, SectionPresheaf.openSubset U r) Γ(N, SectionPresheaf.openSubset U r) where
  smul_assoc a b m := by
    change (algebraMap Γ(X, U) Γ(X, SectionPresheaf.openSubset U r) a * b) • m =
      algebraMap Γ(X, U) Γ(X, SectionPresheaf.openSubset U r) a • (b • m)
    exact mul_smul _ _ _

def frame (r : SectionPresheaf.Index U) : Γ(N, SectionPresheaf.openSubset U r) ≃ₗ[Γ(X, SectionPresheaf.openSubset U r)]
    Γ(X, SectionPresheaf.openSubset U r) :=
  (AffinePrincipal.Sections.iso U hU r.val N).symm.trans
    ((e.baseChange Γ(X, U) Γ(X, SectionPresheaf.openSubset U r)).trans
      (TensorProduct.AlgebraTensorModule.rid Γ(X, U) Γ(X, SectionPresheaf.openSubset U r)
        Γ(X, SectionPresheaf.openSubset U r)))

theorem frame_symm (r : SectionPresheaf.Index U) (a : Γ(X, SectionPresheaf.openSubset U r)) :
    (frame U hU N e r).symm a = a • N.presheaf.map (SectionPresheaf.inclusion U r).op (e.symm 1) := by
  change AffinePrincipal.Sections.iso U hU r.val N (a ⊗ₜ[Γ(X, U)] e.symm 1) = _
  exact AffinePrincipal.Sections.iso_tmul U hU r.val N a (e.symm 1)

abbrev scalars := SectionPresheaf.rings U hU ⋙ forget₂ (CommAlgCat Γ(X, U)) (AlgCat Γ(X, U)) ⋙
  forget₂ (AlgCat Γ(X, U)) (ModuleCat Γ(X, U))

def iso : SectionPresheaf.modules U hU N ≅ scalars U hU :=
  (NatIso.ofComponents
    (fun r => ((frame U hU N e r.unop).symm.restrictScalars Γ(X, U)).toModuleIso)
    (by
      intro r s a
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (frame U hU N e s.unop).symm
          (X.presheaf.map (SectionPresheaf.arrow U hU a.unop).op x) =
        N.presheaf.map (SectionPresheaf.arrow U hU a.unop).op ((frame U hU N e r.unop).symm x)
      rw [frame_symm, frame_symm, N.map_smul]
      congr 1
      rw [← ConcreteCategory.comp_apply, ← N.presheaf.map_comp]
      rfl)).symm

theorem iso_inv (r : (SectionPresheaf.Index U)ᵒᵖ) (a : Γ(X, SectionPresheaf.openSubset U r.unop)) :
    (iso U hU N e).inv.app r a =
      a • N.presheaf.map (SectionPresheaf.inclusion U r.unop).op (e.symm 1) :=
  frame_symm U hU N e r.unop a

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.LineFrame
