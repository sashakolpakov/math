import OAI.AlgebraicGeometry.CycleClass.Geometric.SmallChainImage
import OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionBoundary
import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Small Subdivision -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSubdivision.Cycles

noncomputable section

/-!
# Actual barycentric subdivision on the small-chain complex

The signed ambient operator preserves the genuine image of small chains because
its cells have smaller geometric ranges. We restrict that actual linear map
through the injective chain inclusion. Boundary compatibility is then proved
from the already established ambient boundary identity, using injectivity.
-/

open _root_.CategoryTheory
open scoped Simplicial

variable (X : TopCat.{0}) {J : Type} (U : J → Set X)

/-- Actual barycentric subdivision preserves the actual image of small chains. -/
theorem subdivisionDegree_preserves_smallChainImage (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X n)
    (hc : c ∈ LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom) :
    SubdivisionOperator.Cycles.subdivisionDegree X n c ∈
      LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom := by
  apply (SmallChainImage.Cycles.mem_range_smallIntegralChainInclusion_iff X U n _).2
  intro t ht
  obtain ⟨s, hs, hsub⟩ := SubdivisionOperator.Cycles.support_subdivisionDegree_range X n c t ht
  have hsmall := (SmallChainImage.Cycles.mem_range_smallIntegralChainInclusion_iff X U n c).1 hc s hs
  change ∃ i, Set.range (X.toSSetObjEquiv (.op ⦋n⦌) t) ⊆ U i
  obtain ⟨i, hi⟩ := hsmall
  exact ⟨i, hsub.trans hi⟩

/-- The unique linear restriction of the actual ambient subdivision operator
to genuine small chains. -/
def smallSubdivisionDegree (n : ℕ) :
    (SmallChainImage.Cycles.integralSmallSingularChains X U).X n →ₗ[ℤ]
      (SmallChainImage.Cycles.integralSmallSingularChains X U).X n :=
  LinearMap.codRestrictOfInjective
    ((SubdivisionOperator.Cycles.subdivisionDegree X n).comp ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom)
    ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom
    (SmallChainImage.Cycles.smallIntegralChainInclusion_injective X U n)
    (fun c => subdivisionDegree_preserves_smallChainImage X U n _
      (LinearMap.mem_range_self _ c))

/-- Inclusion carries the restricted operator back to the given signed ambient operator. -/
@[simp]
theorem smallSubdivisionDegree_inclusion (n : ℕ)
    (c : (SmallChainImage.Cycles.integralSmallSingularChains X U).X n) :
    (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n (smallSubdivisionDegree X U n c) =
      SubdivisionOperator.Cycles.subdivisionDegree X n ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n c) := by
  simp [smallSubdivisionDegree]

/-- The preceding compatibility as an equality of actual linear maps. -/
theorem smallSubdivisionDegree_intertwining (n : ℕ) :
    ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom.comp (smallSubdivisionDegree X U n) =
      (SubdivisionOperator.Cycles.subdivisionDegree X n).comp ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom := by
  ext c
  exact smallSubdivisionDegree_inclusion X U n c

/-- The inclusion commutes with every actual iterate. -/
theorem smallSubdivisionDegree_iterate_inclusion (n N : ℕ)
    (c : (SmallChainImage.Cycles.integralSmallSingularChains X U).X n) :
    (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n ((smallSubdivisionDegree X U n)^[N] c) =
      (SubdivisionOperator.Cycles.subdivisionDegree X n)^[N] ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n c) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [Function.iterate_succ_apply', smallSubdivisionDegree_inclusion, ih,
        Function.iterate_succ_apply']

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Elementwise differential compatibility of the genuine small-chain inclusion. -/
theorem smallIntegralChainInclusion_d (i j : ℕ)
    (c : (SmallChainImage.Cycles.integralSmallSingularChains X U).X i) :
    (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f j ((SmallChainImage.Cycles.integralSmallSingularChains X U).d i j c) =
      (LocalHomology.Cycles.integralSingularChains X).d i j ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f i c) := by
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using!
    congrArg (fun f : (SmallChainImage.Cycles.integralSmallSingularChains X U).X i ⟶
      (LocalHomology.Cycles.integralSingularChains X).X j => f.hom c)
      ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).comm i j).symm

/-- Actual small subdivision commutes with the actual small-chain boundary. -/
theorem smallSubdivisionDegree_boundary (n : ℕ)
    (c : (SmallChainImage.Cycles.integralSmallSingularChains X U).X (n + 1)) :
    (SmallChainImage.Cycles.integralSmallSingularChains X U).d (n + 1) n
        (smallSubdivisionDegree X U (n + 1) c) =
      smallSubdivisionDegree X U n ((SmallChainImage.Cycles.integralSmallSingularChains X U).d (n + 1) n c) := by
  apply SmallChainImage.Cycles.smallIntegralChainInclusion_injective X U n
  simpa only [smallIntegralChainInclusion_d, smallSubdivisionDegree_inclusion] using
    SubdivisionBoundary.Cycles.subdivisionDegree_boundary X n ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f (n + 1) c)

/-- Boundary compatibility as the linear-map equality used in chain-map construction. -/
theorem smallSubdivisionDegree_comm (n : ℕ) :
    ((SmallChainImage.Cycles.integralSmallSingularChains X U).d (n + 1) n).hom.comp
        (smallSubdivisionDegree X U (n + 1)) =
      (smallSubdivisionDegree X U n).comp
        ((SmallChainImage.Cycles.integralSmallSingularChains X U).d (n + 1) n).hom := by
  ext c
  exact smallSubdivisionDegree_boundary X U n c

/-- The genuine signed barycentric subdivision chain map on small chains. -/
def smallSubdivisionChainMap :
    SmallChainImage.Cycles.integralSmallSingularChains X U ⟶ SmallChainImage.Cycles.integralSmallSingularChains X U :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (smallSubdivisionDegree X U n))
    (fun n => by
      apply ModuleCat.hom_ext
      exact smallSubdivisionDegree_comm X U n)

@[simp]
theorem smallSubdivisionChainMap_f (n : ℕ) :
    ((smallSubdivisionChainMap X U).f n).hom = smallSubdivisionDegree X U n := rfl

/-- Actual chain-map intertwining, in the orientation required by the
small-chain quasi-isomorphism criterion. -/
theorem smallSubdivisionChainMap_intertwining :
    SmallChainImage.Cycles.smallIntegralChainInclusion X U ≫ SubdivisionBoundary.Cycles.subdivisionChainMap X =
      smallSubdivisionChainMap X U ≫ SmallChainImage.Cycles.smallIntegralChainInclusion X U := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  exact (smallSubdivisionDegree_intertwining X U n).symm

/-- Eventual image membership formulated directly using the assembled actual
ambient subdivision chain map. -/
theorem exists_subdivisionChainMap_iterate_small_preimage
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    {n : ℕ} (c : (LocalHomology.Cycles.integralSingularChains X).X n) :
    ∃ N : ℕ, ∃ b : (SmallChainImage.Cycles.integralSmallSingularChains X U).X n,
      (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n b =
        ((SubdivisionBoundary.Cycles.subdivisionChainMap X).f n)^[N] c :=
  SmallChainImage.Cycles.exists_subdivisionDegree_iterate_smallChain_preimage X U hopen hcover c

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSubdivision.Cycles
