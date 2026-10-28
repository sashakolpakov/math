import OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.ProductBoundary

/-! # Product Cycle -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.ProductCycle

noncomputable section

/-! The actual axis-product boundary is a cycle in its punctured support. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem axisProductPuncture_chain_injective (m n : ℕ) :
    Function.Injective (((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (ProductBoundary.axisProductPunctureInclusion m)).f n) := by
  let X := TopCat.of (ℝ × EuclideanSpace ℝ (Fin m))
  have : Mono ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ X ({0}ᶜ)).f n) :=
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_degreewiseShortExact ℚ X ({0}ᶜ) n).mono_f
  exact (ModuleCat.mono_iff_injective _).mp this

theorem axisProductBoundaryChain_cycle (m q : ℕ)
    (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).X (q + 2))
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))).X (q + 1))
    (hB : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).d (q + 2) (q + 1) B =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (EuclideanSpace ℝ (Fin m))) ({0}ᶜ)).f (q + 1) z) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (ℝ × EuclideanSpace ℝ (Fin m))))).d
      (q + 2) (q + 1) (ProductBoundary.axisProductBoundaryChain m q B z) = 0 := by
  apply axisProductPuncture_chain_injective m (q + 1)
  rw [map_zero]
  let f := (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (ProductBoundary.axisProductPunctureInclusion m)
  have hf := ConcreteCategory.congr_hom (f.comm (q + 2) (q + 1)) (ProductBoundary.axisProductBoundaryChain m q B z)
  change (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (ℝ × EuclideanSpace ℝ (Fin m)))).d
      (q + 2) (q + 1) (f.f (q + 2) (ProductBoundary.axisProductBoundaryChain m q B z)) = _ at hf
  rw [show f.f (q + 2) (ProductBoundary.axisProductBoundaryChain m q B z) = _ from
    ProductBoundary.axisProductBoundaryChain_inclusion m q B z hB] at hf
  refine hf.symm.trans ?_
  exact ConcreteCategory.congr_hom
    ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (ℝ × EuclideanSpace ℝ (Fin m)))).d_comp_d
      (q + 3) (q + 2) (q + 1)) _

def axisProductBoundaryCycle (m q : ℕ)
    (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).X (q + 2))
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))).X (q + 1))
    (hB : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).d (q + 2) (q + 1) B =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (EuclideanSpace ℝ (Fin m))) ({0}ᶜ)).f (q + 1) z) :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
      (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (ℝ × EuclideanSpace ℝ (Fin m))))) (q + 2) :=
  ⟨ProductBoundary.axisProductBoundaryChain m q B z,
    (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ _ (q + 1) _).mpr (axisProductBoundaryChain_cycle m q B z hB)⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.ProductCycle
