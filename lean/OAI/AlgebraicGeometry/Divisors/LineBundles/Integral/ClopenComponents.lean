import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ClosedImage
import OAI.AlgebraicGeometry.Divisors.LineBundles.FiberFundamentalCycle
import Mathlib.Topology.Connected.Clopen

/-! # Clopen Components -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ClopenComponents.BundleCycles

noncomputable section

/-! The components and their generic points in a disjoint cover by actual
integral open and closed subschemes. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme.{0}} {ι : Type} (U : ι → Scheme.{0}) [∀ k, IsIntegral (U k)]
    (i : ∀ k, U k ⟶ X) [∀ k, IsOpenImmersion (i k)] [∀ k, IsClosedImmersion (i k)]

theorem integralClopen_range_component (k : ι) : Set.range (i k) ∈ irreducibleComponents X := by
  have hir : IsIrreducible (Set.range (i k)) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (U k)).image (i k) (i k).continuous.continuousOn
  refine ⟨hir, ?_⟩
  intro W hW hsub
  obtain ⟨x, hx⟩ := hir.nonempty
  exact hW.isConnected.isPreconnected.subset_isClopen
    ⟨(i k).isClosedEmbedding.isClosed_range, (i k).isOpenEmbedding.isOpen_range⟩ ⟨x, hsub hx, hx⟩

def integralClopenComponent (k : ι) : irreducibleComponents X :=
  ⟨Set.range (i k), integralClopen_range_component U i k⟩

theorem integralClopenComponent_genericPoint (k : ι) :
    FiberFundamentalCycle.BundleCycles.componentGenericPoint X (integralClopenComponent U i k) = i k (genericPoint (U k)) := by
  have hW : (⟨Set.range (i k), (integralClopen_range_component U i k).1,
      (i k).isClosedEmbedding.isClosed_range⟩ : IrreducibleCloseds X) =
      CycleClass.Geometric.StratumClosure.integralImageClosure (i k) := by
    apply SetLike.coe_injective
    exact (i k).isClosedEmbedding.isClosed_range.closure_eq.symm
  exact (congrArg irreducibleSetEquivPoints hW).trans (ClosedImage.BundleCycles.integralClosedImage_genericPoint (i k))

variable (hcover : ∀ x : X, ∃! k, x ∈ Set.range (i k))

include hcover in
theorem integralClopenComponent_bijective : Function.Bijective (integralClopenComponent U i) := by
  constructor
  · intro k l hkl
    let x := i k (genericPoint (U k))
    have hk : x ∈ Set.range (i k) := ⟨_, rfl⟩
    have hl : x ∈ Set.range (i l) := by
      exact (congrArg (fun C : irreducibleComponents X => x ∈ C.val) hkl).mp hk
    obtain ⟨m, _, hm⟩ := hcover x
    exact (hm k hk).trans (hm l hl).symm
  · intro C
    obtain ⟨x, hx⟩ := C.property.1.nonempty
    obtain ⟨k, hk, _⟩ := hcover x
    refine ⟨k, Subtype.ext ?_⟩
    have hsub : C.val ⊆ Set.range (i k) := C.property.1.isConnected.isPreconnected.subset_isClopen
      ⟨(i k).isClosedEmbedding.isClosed_range, (i k).isOpenEmbedding.isOpen_range⟩ ⟨x, hx, hk⟩
    exact (C.property.2 (integralClopen_range_component U i k).1 hsub).antisymm hsub

def integralClopenComponentsEquiv : ι ≃ irreducibleComponents X :=
  Equiv.ofBijective (integralClopenComponent U i) (integralClopenComponent_bijective U i hcover)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ClopenComponents.BundleCycles
