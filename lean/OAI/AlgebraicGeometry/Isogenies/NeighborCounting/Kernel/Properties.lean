import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GenericParameters
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Properties -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Properties

noncomputable section

/-!
The graph/product constructions are genuine finite flat closed subgroup
schemes whenever the supplied split factors and etale inclusions are.
These properties are proved from the morphisms; they are not encoded as
unproved properties of the resulting neighbor family.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCounts.Construction

structure FiniteFlatKernel {S : Scheme.{u}} (A : Over S) [GrpObj A]
    extends Intrinsic.Neighbors.KernelPresentation A where
  [group : GrpObj carrier]
  [isHom : IsMonHom inclusion]
  finite : IsFinite carrier.hom
  flat : Flat carrier.hom
  finitePresentation : LocallyOfFinitePresentation carrier.hom
  closed : IsClosedImmersion inclusion.left

attribute [instance] FiniteFlatKernel.group FiniteFlatKernel.isHom

theorem graphKernel_closed {S : Scheme.{u}} {A M E H : Over S}
    (b : M ⊗ E ⟶ A) (e : H ⟶ E) (χ : H ⟶ M)
    [IsSeparated M.hom] [IsClosedImmersion b.left] [IsClosedImmersion e.left] :
    IsClosedImmersion (QuotientGraphs.graphKernel b e χ).left := by
  have hp : IsSeparated (snd M E).left := by
    change IsSeparated (pullback.snd M.hom E.hom)
    infer_instance
  have hc : IsClosedImmersion ((lift χ e).left ≫ (snd M E).left) := by
    change IsClosedImmersion (lift χ e ≫ snd M E).left
    rw [lift_snd]
    infer_instance
  have : IsClosedImmersion (lift χ e).left :=
    IsClosedImmersion.of_comp (lift χ e).left (snd M E).left
  change IsClosedImmersion ((lift χ e).left ≫ b.left)
  infer_instance

theorem mixedKernel_closed {S : Scheme.{u}} {A M E H : Over S}
    (b : M ⊗ E ⟶ A) (e : H ⟶ E)
    [IsClosedImmersion b.left] [IsClosedImmersion e.left] :
    IsClosedImmersion (QuotientGraphs.mixedKernel b e).left := by
  let : MorphismProperty.IsStableUnderComposition (@IsClosedImmersion.{u}) :=
    ⟨fun f g hf hg => by
      let := hf
      let := hg
      exact IsClosedImmersion.comp f g⟩
  have hp : IsClosedImmersion (𝟙 M ⊗ₘ e).left := by
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := @IsClosedImmersion.{u})
      (show IsClosedImmersion (𝟙 M : M ⟶ M).left from by
        change IsClosedImmersion (𝟙 M.left)
        infer_instance)
      (show IsClosedImmersion e.left from inferInstance)
      (Over.w (𝟙 M)).symm (Over.w e).symm
  change IsClosedImmersion ((𝟙 M ⊗ₘ e).left ≫ b.left)
  infer_instance

def graphFiniteFlatKernel {S : Scheme.{u}} {A M E H : Over S}
    [GrpObj A] [GrpObj M] [GrpObj E] [GrpObj H]
    (b : M ⊗ E ⟶ A) (e : H ⟶ E) (χ : H ⟶ M)
    [IsMonHom b] [IsMonHom e] [IsMonHom χ]
    [IsSeparated M.hom] [IsClosedImmersion b.left] [IsClosedImmersion e.left]
    [IsFinite H.hom] [Flat H.hom] [LocallyOfFinitePresentation H.hom] :
    FiniteFlatKernel A where
  carrier := H
  inclusion := QuotientGraphs.graphKernel b e χ
  group := inferInstance
  isHom := inferInstanceAs (IsMonHom (lift χ e ≫ b))
  finite := inferInstance
  flat := inferInstance
  finitePresentation := inferInstance
  closed := graphKernel_closed b e χ

def mixedFiniteFlatKernel {S : Scheme.{u}} {A M E H : Over S}
    [GrpObj A] [GrpObj M] [GrpObj E] [GrpObj H]
    (b : M ⊗ E ⟶ A) (e : H ⟶ E)
    [IsMonHom b] [IsMonHom e]
    [IsClosedImmersion b.left] [IsClosedImmersion e.left]
    [IsFinite M.hom] [Flat M.hom] [LocallyOfFinitePresentation M.hom]
    [IsFinite H.hom] [Flat H.hom] [LocallyOfFinitePresentation H.hom] :
    FiniteFlatKernel A where
  carrier := M ⊗ H
  inclusion := QuotientGraphs.mixedKernel b e
  group := inferInstance
  isHom := inferInstanceAs (IsMonHom ((𝟙 M ⊗ₘ e) ≫ b))
  finite := by change IsFinite (pullback.fst M.hom H.hom ≫ M.hom); infer_instance
  flat := by change Flat (pullback.fst M.hom H.hom ≫ M.hom); infer_instance
  finitePresentation := by
    change LocallyOfFinitePresentation (pullback.fst M.hom H.hom ≫ M.hom)
    infer_instance
  closed := mixedKernel_closed b e

theorem subspaceKernel_is_finiteFlat
    {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {S : Scheme.{u}} {A M E : Over S} [GrpObj A] [GrpObj M] [GrpObj E]
    (H : Submodule F V → Over S) [∀ U, GrpObj (H U)]
    (b : M ⊗ E ⟶ A) (e : ∀ U, H U ⟶ E)
    (χ : ∀ U : Submodule F V, (U →ₗ[F] F) → (H U ⟶ M))
    [IsMonHom b] [∀ U, IsMonHom (e U)] [∀ U l, IsMonHom (χ U l)]
    [IsClosedImmersion b.left] [∀ U, IsClosedImmersion (e U).left]
    [IsFinite M.hom] [Flat M.hom] [LocallyOfFinitePresentation M.hom]
    [∀ U, IsFinite (H U).hom] [∀ U, Flat (H U).hom]
    [∀ U, LocallyOfFinitePresentation (H U).hom]
    (L : Submodule F (V × F)) :
    ∃ K : FiniteFlatKernel A, K.toKernelPresentation = Intrinsic.Neighbors.subspaceKernel H b e χ L := by
  obtain ⟨⟨U, L | L⟩, rfl⟩ := (SubspaceCounts.Construction.allSubspacesEquiv (F := F) (V := V)).surjective L
  · rw [Intrinsic.Neighbors.subspaceKernel_equiv]
    exact ⟨graphFiniteFlatKernel b (e U) (χ U ((SubspaceCounts.Construction.disjointLiftEquiv U).symm L)), rfl⟩
  · rw [Intrinsic.Neighbors.subspaceKernel_equiv]
    exact ⟨mixedFiniteFlatKernel b (e U), rfl⟩

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Properties
