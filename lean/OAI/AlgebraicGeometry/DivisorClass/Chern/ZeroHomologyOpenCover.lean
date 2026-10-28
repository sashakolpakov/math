import OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-! # Zero Homology Open Cover -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ZeroHomologyOpenCover

noncomputable section

/-! Actual point classes from an open cover generate rational zeroth singular homology. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def rationalZeroChainClass (X : TopCat.{0}) :
    (OAI.AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).X 0 →ₗ[ℚ] (OAI.AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology 0 :=
  (OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (OAI.AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) 0).comp
    ((LinearMap.id).codRestrict (OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (OAI.AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) 0)
      (fun z => OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero (OAI.AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) z))

theorem rationalZeroChainClass_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    (z : (OAI.AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).X 0) :
    OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f 0 (rationalZeroChainClass X z) =
      rationalZeroChainClass Y ((OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) f).f 0 z) := by
  exact OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward_class f 0 ⟨z, OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero _ z⟩

theorem singularZeroSimplex_open_lift (X : TopCat.{0}) (U : Opens X)
    (s : (TopCat.toSSet.obj X) _⦋0⦌) (hs : TopCat.toSSetObj₀Equiv s ∈ U) :
    ∃ t : (TopCat.toSSet.obj (TopCat.of U)) _⦋0⦌,
      (TopCat.toSSet.map (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X (U : Set X))).app _ t = s := by
  refine ⟨TopCat.toSSetObj₀Equiv.symm ⟨TopCat.toSSetObj₀Equiv s, hs⟩, ?_⟩
  apply TopCat.toSSetObj₀Equiv.injective
  change TopCat.toSSetObj₀Equiv s = TopCat.toSSetObj₀Equiv s
  rfl

theorem rationalH0_openCover_hom_ext (X : TopCat.{0}) {I : Type*} (U : I → Opens X)
    (hU : ∀ x : X, ∃ i, x ∈ U i) {N : ModuleCat.{0} ℚ}
    {f g : (OAI.AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology 0 ⟶ N}
    (h : ∀ i, OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X (U i : Set X)) 0 ≫ f =
      OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X (U i : Set X)) 0 ≫ g) : f = g := by
  have hc : f.hom.comp (rationalZeroChainClass X) = g.hom.comp (rationalZeroChainClass X) := by
    apply OAI.AlgebraicTopology.Cohomology.Singular.ChainDual.chainFunctional_ext (TopCat.toSSet.obj X) N
    intro s
    obtain ⟨i, hi⟩ := hU (TopCat.toSSetObj₀Equiv s)
    obtain ⟨t, ht⟩ := singularZeroSimplex_open_lift X (U i) s hi
    have hp := ConcreteCategory.congr_hom (h i)
      (rationalZeroChainClass (TopCat.of (U i)) (OAI.AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℚ) (TopCat.toSSet.obj (TopCat.of (U i))) t))
    simp only [ConcreteCategory.comp_apply] at hp
    erw [rationalZeroChainClass_naturality] at hp
    change f (rationalZeroChainClass X
      ((OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℚ) (TopCat.toSSet.map (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X (U i : Set X)))).f 0
        (OAI.AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℚ) (TopCat.toSSet.obj (TopCat.of (U i))) t))) = _ at hp
    erw [OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap_simplex, ht] at hp
    exact hp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨c, rfl⟩ := OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective (OAI.AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) 0 z
  exact LinearMap.congr_fun hc c.val

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ZeroHomologyOpenCover
