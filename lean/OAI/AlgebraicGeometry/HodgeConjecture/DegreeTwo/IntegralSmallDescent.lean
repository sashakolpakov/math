import OAI.AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Integral Small Descent -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntegralSmallDescent.Constructions

noncomputable section

/-! Degreewise descent through the actual integral binary-small quotient. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles

set_option backward.isDefEq.respectTransparency false

abbrev integralChainDegree (n : ℕ) :=
  HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n

variable (X : TopCat.{0}) (A B : Set X) (n : ℕ)
variable {M : ModuleCat.{0} ℤ} (f : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n ⟶ M)
variable (hA : (CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A).f n ≫ f = 0)
variable (hB : (CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X B).f n ≫ f = 0)

include hA hB in
theorem integralBinarySmallDegreeInclusion_zero :
    (CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B).f n ≫ f = 0 := by
  let F := integralChainDegree n
  change F.map (CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B) ≫ f = 0
  have : Epi (CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence X A B).g :=
    (CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence_shortExact X A B).epi_g
  let : PreservesBinaryBiproduct (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of A))
      (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of B)) F :=
    preservesBinaryBiproduct_of_preservesBiproduct F _ _
  apply (cancel_epi (F.map (CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence X A B).g)).mp
  apply (cancel_epi (F.mapBiprod
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of A)) (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of B))).inv).mp
  rw [Functor.mapBiprod_inv]
  apply biprod.hom_ext'
  · rw [biprod.inl_desc_assoc, ← F.map_comp_assoc,
      CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence_g, biprod.inl_desc, ← F.map_comp_assoc,
      CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_left]
    exact hA.trans (by simp)
  · rw [biprod.inr_desc_assoc, ← F.map_comp_assoc,
      CycleClass.Geometric.SmallMayerVietoris.Cycles.smallMayerVietorisSequence_g, biprod.inr_desc, ← F.map_comp_assoc,
      CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion_right]
    exact hB.trans (by simp)

def binaryIntegralComplementDegreeDesc : (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementChains X A B).X n ⟶ M :=
  (PreservesCokernel.iso (integralChainDegree n) (CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B)).hom ≫
    cokernel.desc ((integralChainDegree n).map (CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion X A B))
      f (integralBinarySmallDegreeInclusion_zero X A B n f hA hB)

theorem binaryIntegralComplementDegreeDesc_projection :
    (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B).f n ≫
      binaryIntegralComplementDegreeDesc X A B n f hA hB = f := by
  change (integralChainDegree n).map (CycleClass.Geometric.HomologyWithSupports.Cycles.binarySmallComplementProjection X A B) ≫ _ = _
  rw [binaryIntegralComplementDegreeDesc, ← Category.assoc,
    PreservesCokernel.π_iso_hom, cokernel.π_desc]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntegralSmallDescent.Constructions
