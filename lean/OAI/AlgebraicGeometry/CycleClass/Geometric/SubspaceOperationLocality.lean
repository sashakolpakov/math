import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeChainSupport

/-! # Subspace Operation Locality -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SubspaceOperationLocality.Cycles

noncomputable section

/-!
# Subspace-preserving operations preserve cover-small chains

For a fixed space, a linear operation that preserves the actual chain image
of every subspace preserves the actual cover-small chain image for any family
of subsets. The proof uses the free singular-simplex generators. No naturality
across spaces, openness, or covering hypothesis is needed.
-/

open _root_.CategoryTheory
open scoped Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Preservation of the actual chain image of each subspace of the fixed
ambient space, expressed using its genuine singular-chain inclusion. -/
def PreservesSubspaceChainImages {X : TopCat.{0}} {n m : ℕ}
    (F : (LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] (LocalHomology.Cycles.integralSingularChains X).X m) : Prop :=
  ∀ (A : Set X) (c : (LocalHomology.Cycles.integralSingularChains X).X n),
    c ∈ LinearMap.range ((LocalHomology.Cycles.subspaceChainInclusion X A).f n).hom →
      F c ∈ LinearMap.range ((LocalHomology.Cycles.subspaceChainInclusion X A).f m).hom

/-- An actual simplex generator with image in a subset belongs to the actual
subspace-chain image, for every integer coefficient. -/
theorem simplex_mem_subspaceChainImage (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (s : (TopCat.toSSet.obj X).obj (.op ⦋n⦌))
    (hs : Set.range (X.toSSetObjEquiv (.op ⦋n⦌) s) ⊆ A) (z : ℤ) :
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s z ∈
      LinearMap.range ((LocalHomology.Cycles.subspaceChainInclusion X A).f n).hom := by
  apply (RelativeChainSupport.Cycles.mem_subspaceChainInclusion_range_iff X A n _).2
  intro t ht
  rw [SingularChainSupport.Cycles.singularChainCoefficients_simplex_apply] at ht
  obtain ⟨rfl, _⟩ := Finsupp.single_apply_ne_zero.mp ht
  exact hs

/-- Chains supported in one family member belong to the genuine cover-small
chain image. The family need not be open or cover the space. -/
theorem subspaceChainImage_le_smallChainImage (X : TopCat.{0}) {J : Type}
    (U : J → Set X) (j : J) (n : ℕ) :
    LinearMap.range ((LocalHomology.Cycles.subspaceChainInclusion X (U j)).f n).hom ≤
      LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom := by
  intro c hc
  apply (SmallChainImage.Cycles.mem_range_smallIntegralChainInclusion_iff X U n c).2
  intro s hs
  refine ⟨j, (RelativeChainSupport.Cycles.mem_subspaceChainInclusion_range_iff X (U j) n c).1 hc s ?_⟩
  exact Finsupp.mem_support_iff.mp hs

/-- A subspace-preserving operation sends each small simplex generator into
the actual small-chain image. -/
theorem subspaceLocalOperation_smallSimplex (X : TopCat.{0}) {J : Type}
    (U : J → Set X) {n m : ℕ}
    (F : (LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] (LocalHomology.Cycles.integralSingularChains X).X m)
    (hF : PreservesSubspaceChainImages F)
    (s : (TopCat.toSSet.obj X).obj (.op ⦋n⦌))
    (hs : s ∈ (AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U).obj (.op ⦋n⦌))
    (z : ℤ) :
    F ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s z) ∈
      LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f m).hom := by
  obtain ⟨j, hj⟩ := hs
  apply subspaceChainImage_le_smallChainImage X U j m
  exact hF (U j) _ (simplex_mem_subspaceChainImage X (U j) n s hj z)

/-- Every linear operation preserving the genuine chain image of each subset
preserves the genuine cover-small chain image. This is a statement about a
single operation on a fixed space, with no naturality assumption. -/
theorem subspaceLocalOperation_preserves_smallChainImage (X : TopCat.{0})
    {J : Type} (U : J → Set X) {n m : ℕ}
    (F : (LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] (LocalHomology.Cycles.integralSingularChains X).X m)
    (hF : PreservesSubspaceChainImages F)
    {c : (LocalHomology.Cycles.integralSingularChains X).X n}
    (hc : c ∈ LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n).hom) :
    F c ∈ LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f m).hom := by
  let P := LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f m).hom
  let : Module ℤ ((LocalHomology.Cycles.integralSingularChains X).X m ⧸ P) := Submodule.Quotient.module P
  have hzero : (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n ≫ ModuleCat.ofHom F ≫
      ModuleCat.ofHom P.mkQ = 0 := by
    apply SSet.chainComplex_hom_ext
    intro s
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    have hsmall := subspaceLocalOperation_smallSimplex X U F hF s.val s.property z
    have hgen : (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n
        ((AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U : SSet).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) s z) =
        (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s.val z :=
      ConcreteCategory.congr_hom
        (SSet.ι_chainComplexMap_f
          (AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U : SSet)
          (TopCat.toSSet.obj X) (AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularInclusion X U)
          (ModuleCat.of ℤ ℤ) s) z
    change P.mkQ (F ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n
      ((AlgebraicTopology.DeRham.Comparison.SmallSingularSet.smallSingularSubcomplex X U : SSet).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) s z))) = 0
    rw [hgen, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hsmall
  obtain ⟨b, rfl⟩ := hc
  have hb := ConcreteCategory.congr_hom hzero b
  change P.mkQ (F ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f n b)) = 0 at hb
  exact (Submodule.Quotient.mk_eq_zero (p := P)).mp hb

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SubspaceOperationLocality.Cycles
