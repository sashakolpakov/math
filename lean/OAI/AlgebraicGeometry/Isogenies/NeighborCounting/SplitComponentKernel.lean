import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.SpecialFiber

/-! # Split Component Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitComponentKernel.Components

noncomputable section

/-! Identify the kernel of an actual split projection with its first
factor, including the group law and its embedding in the original group. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable {S : Scheme.{u}} {A M E : Over S} [GrpObj A] [GrpObj M] [GrpObj E]
variable (e : A ≅ M ⊗ E) [IsMonHom e.hom]

def splitComponentProjection : A ⟶ E := e.hom ≫ snd M E

instance splitComponentProjection_isMonHom : IsMonHom (splitComponentProjection e) := by
  unfold splitComponentProjection
  infer_instance

def splitComponentKernelMap : Picard.PoincareBundle.Kernel.Scheme.kernelObject (splitComponentProjection e) ⟶ M :=
  Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (splitComponentProjection e) ≫ e.hom ≫ fst M E

instance splitComponentKernelMap_isMonHom : IsMonHom (splitComponentKernelMap e) := by
  unfold splitComponentKernelMap
  infer_instance

def splitComponentKernelInv : M ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject (splitComponentProjection e) :=
  (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv (splitComponentProjection e) M).symm
    ⟨lift (𝟙 M) (1 : M ⟶ E) ≫ e.inv, by
      change (lift (𝟙 M) (1 : M ⟶ E) ≫ e.inv) ≫ e.hom ≫ snd M E = 1
      rw [Category.assoc, e.inv_hom_id_assoc, lift_snd]⟩

theorem splitComponentKernelInv_inclusion :
    splitComponentKernelInv e ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (splitComponentProjection e) =
      lift (𝟙 M) (1 : M ⟶ E) ≫ e.inv :=
  congrArg Subtype.val ((Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv (splitComponentProjection e) M).apply_symm_apply _)

def splitComponentKernelIso : Picard.PoincareBundle.Kernel.Scheme.kernelObject (splitComponentProjection e) ≅ M where
  hom := splitComponentKernelMap e
  inv := splitComponentKernelInv e
  hom_inv_id := by
    apply (cancel_mono (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (splitComponentProjection e))).mp
    rw [Category.assoc, splitComponentKernelInv_inclusion, Category.id_comp]
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, Category.assoc, e.inv_hom_id, Category.comp_id]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, Category.comp_id, splitComponentKernelMap]
    · rw [Category.assoc, lift_snd, MonObj.comp_one]
      exact (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion_comp (splitComponentProjection e)).symm
  inv_hom_id := by
    rw [splitComponentKernelMap, ← Category.assoc, splitComponentKernelInv_inclusion]
    simp only [Category.assoc, e.inv_hom_id_assoc, lift_fst]

instance splitComponentKernelIso_isMonHom : IsMonHom (splitComponentKernelIso e).hom :=
  inferInstanceAs (IsMonHom (splitComponentKernelMap e))

theorem splitComponentKernelIso_inv_inclusion :
    (splitComponentKernelIso e).inv ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (splitComponentProjection e) =
      lift (𝟙 M) (1 : M ⟶ E) ≫ e.inv :=
  splitComponentKernelInv_inclusion e

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitComponentKernel.Components
