import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ComponentLift
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.RepresentedGroups

/-! # Special Fiber -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.SpecialFiber.Components

noncomputable section

/-!
The scheme-theoretic kernel of the constructed component map has exactly
the independently prescribed kernel on the special fiber. This comparison
uses pullbacks and retains all nonreduced structure.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable {S T : Scheme.{u}} (s : T ⟶ S)
variable {A E : Over S} [GrpObj A] [GrpObj E] (π : A ⟶ E) [IsMonHom π]

omit [GrpObj A] [IsMonHom π] in
theorem kernelPullback_isPullback :
    IsPullback ((Over.pullback s).map (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion π))
      (toUnit ((Over.pullback s).obj (Picard.PoincareBundle.Kernel.Scheme.kernelObject π)))
      ((Over.pullback s).map π) η[(Over.pullback s).obj E] := by
  let F := Over.pullback s
  have h := (IsPullback.of_hasPullback π η[E]).map F
  refine h.of_iso' (Iso.refl _) (Iso.refl _) (asIso (Functor.LaxMonoidal.ε F))
    (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, asIso_hom]
    apply (cancel_mono (inv (Functor.LaxMonoidal.ε F))).mp
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    exact Subsingleton.elim _ _
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, asIso_hom, Functor.obj.η_def]
    rfl

def componentKernelBaseChangeIso :
    (Over.pullback s).obj (Picard.PoincareBundle.Kernel.Scheme.kernelObject π) ≅ Picard.PoincareBundle.Kernel.Scheme.kernelObject ((Over.pullback s).map π) :=
  (kernelPullback_isPullback s π).isoPullback

omit [GrpObj A] [IsMonHom π] in
theorem componentKernelBaseChangeIso_inclusion :
    (componentKernelBaseChangeIso s π).hom ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion ((Over.pullback s).map π) =
      (Over.pullback s).map (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion π) :=
  (kernelPullback_isPullback s π).isoPullback_hom_fst

instance componentKernelBaseChangeIso_isMonHom :
    IsMonHom (componentKernelBaseChangeIso s π).hom := by
  apply AbelianScheme.FrobeniusKernel.RepresentedGroups.Construction.isMonHom_of_point_operations
  · intro X
    apply (cancel_mono (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion ((Over.pullback s).map π))).mp
    rw [Category.assoc, componentKernelBaseChangeIso_inclusion,
      MonObj.one_comp, MonObj.one_comp]
  · intro X x y
    apply (cancel_mono (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion ((Over.pullback s).map π))).mp
    rw [Category.assoc, componentKernelBaseChangeIso_inclusion,
      MonObj.mul_comp, MonObj.mul_comp, Category.assoc, Category.assoc,
      componentKernelBaseChangeIso_inclusion]

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
variable {A E : Over (Spec (.of R))} [GrpObj A] [GrpObj E]
variable [IsFinite A.hom] [IsFinite E.hom] [Etale E.hom]

/-- HenselianLifting's constructed integral projection specializes to the prescribed
projection, so its actual kernel specializes to the prescribed kernel. -/
def nativeComponentKernelSpecialIso
    (π₀ : (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj A ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj E)
    [IsMonHom π₀] :
    (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj
        (Picard.PoincareBundle.Kernel.Scheme.kernelObject (Intrinsic.ComponentLift.Components.nativeComponentMap R π₀)) ≅ Picard.PoincareBundle.Kernel.Scheme.kernelObject π₀ :=
  componentKernelBaseChangeIso _ _ ≪≫
    pullback.congrHom (Intrinsic.ComponentLift.Components.nativeComponentMap_special R π₀) rfl

theorem nativeComponentKernelSpecialIso_inclusion
    (π₀ : (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj A ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj E)
    [IsMonHom π₀] :
    (nativeComponentKernelSpecialIso R π₀).hom ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion π₀ =
      (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).map
        (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (Intrinsic.ComponentLift.Components.nativeComponentMap R π₀)) := by
  simp only [nativeComponentKernelSpecialIso, Iso.trans_hom, Category.assoc,
    Picard.PoincareBundle.Kernel.Scheme.kernelInclusion, pullback.congrHom_hom, pullback.map, pullback.lift_fst, Category.comp_id]
  exact componentKernelBaseChangeIso_inclusion _ _

instance nativeComponentKernelSpecialIso_isMonHom
    (π₀ : (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj A ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).obj E)
    [IsMonHom π₀] : IsMonHom (nativeComponentKernelSpecialIso R π₀).hom := by
  apply AbelianScheme.FrobeniusKernel.RepresentedGroups.Construction.isMonHom_of_point_operations
  · intro X
    apply (cancel_mono (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion π₀)).mp
    rw [Category.assoc, nativeComponentKernelSpecialIso_inclusion,
      MonObj.one_comp, MonObj.one_comp]
  · intro X x y
    apply (cancel_mono (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion π₀)).mp
    rw [Category.assoc, nativeComponentKernelSpecialIso_inclusion,
      MonObj.mul_comp, MonObj.mul_comp, Category.assoc, Category.assoc,
      nativeComponentKernelSpecialIso_inclusion]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.SpecialFiber.Components
