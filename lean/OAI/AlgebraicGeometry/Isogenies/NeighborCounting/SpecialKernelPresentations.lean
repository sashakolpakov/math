import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.Neighbors

/-! # Special Kernel Presentations -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! Specialize the actual graph and mixed subgroup presentations.
The conclusion identifies the carrier and inclusion map, so it can be
used for full PEL kernel comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCounts.Construction
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup Classical.propDecidable

def Intrinsic.Neighbors.KernelPresentation.pullback {S T : Scheme.{u}} {A : Over S}
    (K : Intrinsic.Neighbors.KernelPresentation A) (f : T ⟶ S) :
    Intrinsic.Neighbors.KernelPresentation ((Over.pullback f).obj A) :=
  ⟨(Over.pullback f).obj K.carrier, (Over.pullback f).map K.inclusion⟩

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]
  {S T : Scheme.{u}} {A M E : Over S} [GrpObj M]
  (H : Submodule F V → Over S) (b : M ⊗ E ⟶ A) (e : ∀ U, H U ⟶ E)
  (χ : ∀ U : Submodule F V, (U →ₗ[F] F) → (H U ⟶ M)) (f : T ⟶ S)

def SpecialKernelPresentations.specialKernelPresentation (U : Submodule F V) :
    Bool → Intrinsic.Neighbors.KernelPresentation ((Over.pullback f).obj A)
  | false => (Intrinsic.Neighbors.KernelPresentation.mk (H U) (QuotientGraphs.graphKernel b (e U) 1)).pullback f
  | true => (Intrinsic.Neighbors.KernelPresentation.mk (M ⊗ H U) (QuotientGraphs.mixedKernel b (e U))).pullback f

theorem SpecialKernelPresentations.subspaceKernel_specialPresentation
    (hχ : ∀ (U : Submodule F V) (a : U →ₗ[F] F), (Over.pullback f).map (χ U a) = 1)
    (J : Submodule F (V × F)) :
    (Intrinsic.Neighbors.subspaceKernel H b e χ J).pullback f =
      SpecialKernelPresentations.specialKernelPresentation H b e f (J.map (LinearMap.fst F V F))
        (decide (SubspaceCounts.Construction.identityLine ≤ J)) := by
  classical
  obtain ⟨⟨U, J | J⟩, rfl⟩ := (SubspaceCounts.Construction.allSubspacesEquiv (F := F) (V := V)).surjective J
  · rw [Intrinsic.Neighbors.subspaceKernel_equiv]
    change (Intrinsic.Neighbors.KernelPresentation.mk (H U)
      (QuotientGraphs.graphKernel b (e U) (χ U ((SubspaceCounts.Construction.disjointLiftEquiv U).symm J)))).pullback f =
        SpecialKernelPresentations.specialKernelPresentation H b e f (J.val.map (LinearMap.fst F V F))
          (decide (SubspaceCounts.Construction.identityLine ≤ J.val))
    rw [J.property.2, decide_eq_false (SubspaceCounts.Construction.identityLine_not_le_of_disjoint _ J.property.1)]
    exact congrArg (Intrinsic.Neighbors.KernelPresentation.mk ((Over.pullback f).obj (H U)))
      (QuotientGraphs.graphKernel_specialization f b (e U) (χ U ((SubspaceCounts.Construction.disjointLiftEquiv U).symm J))
        (hχ U ((SubspaceCounts.Construction.disjointLiftEquiv U).symm J)))
  · rw [Intrinsic.Neighbors.subspaceKernel_equiv]
    change (Intrinsic.Neighbors.KernelPresentation.mk (M ⊗ H U) (QuotientGraphs.mixedKernel b (e U))).pullback f =
      SpecialKernelPresentations.specialKernelPresentation H b e f (J.val.map (LinearMap.fst F V F))
        (decide (SubspaceCounts.Construction.identityLine ≤ J.val))
    rw [J.property.2, decide_eq_true J.property.1]
    rfl

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
