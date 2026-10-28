import OAI.AlgebraicTopology.Kunneth.TensorAlexanderWhitney

/-! # Tensor Arbitrary Representatives -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.TensorArbitraryRepresentatives

noncomputable section

/-!
# ChernClass: the original Künneth map on arbitrary actual cycle representatives

The proved tensor homotopy equivalence projects each cycle to its homology
class. This identifies the original Künneth image with any tensor cycle
having the displayed representatives, without imposing a new normalization.
-/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.ChainSplittingD.Construction.ChainSplitting OAI.AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology
open OAI.AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.TensorClassNormalization
open scoped TensorProduct DirectSum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {k : Type} [Field k] (C D : ChainComplex (ModuleCat.{0} k) ℕ)

theorem algebraicKunneth_of_tensor_cycle (n : ℕ) (ij : AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.DegreePairs n)
    (x : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles C ij.val.1) (y : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles D ij.val.2)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (C ⊗ D) n)
    (hz : z.val = ιTensorObj C D ij.val.1 ij.val.2 n ij.property (x.val ⊗ₜ[k] y.val)) :
    AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.algebraicKunneth C D n
      (DirectSum.lof k (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.DegreePairs n)
        (fun d => C.homology d.val.1 ⊗[k] D.homology d.val.2) ij
        (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C ij.val.1 x ⊗ₜ[k] AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass D ij.val.2 y)) =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (C ⊗ D) n z := by
  let w := AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.TensorClassNormalization.homologyTensorCycle C D n ij (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C ij.val.1 x) (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass D ij.val.2 y)
  have hc : AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.tensorHomologySplitting C D).inv n z = w := by
    apply Subtype.ext
    change (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.tensorHomologySplitting C D).inv.f n z.val =
      ιTensorObj (AlgebraicTopology.Kunneth.ChainSplittingD.Construction.ChainSplitting.homologyComplex C) (AlgebraicTopology.Kunneth.ChainSplittingD.Construction.ChainSplitting.homologyComplex D) ij.val.1 ij.val.2 n ij.property
        (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C ij.val.1 x ⊗ₜ[k] AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass D ij.val.2 y)
    rw [hz]
    have h := ConcreteCategory.congr_hom
      (AlgebraicTopology.Kunneth.CohomologyTensorNe.Construction.TensorProjections.inclusion_tensorHom C D (AlgebraicTopology.Kunneth.ChainSplittingD.Construction.ChainSplitting.projection C) (AlgebraicTopology.Kunneth.ChainSplittingD.Construction.ChainSplitting.projection D) n ij)
      (x.val ⊗ₜ[k] y.val)
    change (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.tensorHomologySplitting C D).inv.f n
      (ιTensorObj C D ij.val.1 ij.val.2 n ij.property (x.val ⊗ₜ[k] y.val)) =
      ιTensorObj (AlgebraicTopology.Kunneth.ChainSplittingD.Construction.ChainSplitting.homologyComplex C) (AlgebraicTopology.Kunneth.ChainSplittingD.Construction.ChainSplitting.homologyComplex D) ij.val.1 ij.val.2 n ij.property
        (TensorProduct.map ((AlgebraicTopology.Kunneth.ChainSplittingD.Construction.ChainSplitting.projection C).f ij.val.1).hom ((AlgebraicTopology.Kunneth.ChainSplittingD.Construction.ChainSplitting.projection D).f ij.val.2).hom
          (x.val ⊗ₜ[k] y.val)) at h
    rw [TensorProduct.map_tmul] at h
    change _ = ιTensorObj (AlgebraicTopology.Kunneth.ChainSplittingD.Construction.ChainSplitting.homologyComplex C) (AlgebraicTopology.Kunneth.ChainSplittingD.Construction.ChainSplitting.homologyComplex D) ij.val.1 ij.val.2 n ij.property
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C ij.val.1 (AlgebraicTopology.Kunneth.ChainSplittingD.Construction.ChainSplitting.cycleRetraction C ij.val.1 x.val) ⊗ₜ[k]
        AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass D ij.val.2 (AlgebraicTopology.Kunneth.ChainSplittingD.Construction.ChainSplitting.cycleRetraction D ij.val.2 y.val)) at h
    rw [AlgebraicTopology.Kunneth.ChainSplittingD.Construction.ChainSplitting.cycleRetraction_cycle, AlgebraicTopology.Kunneth.ChainSplittingD.Construction.ChainSplitting.cycleRetraction_cycle] at h
    exact h
  have hh := AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.tensorHomologySplitting C D).inv n z
  rw [hc] at hh
  calc
    _ = AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (C ⊗ D) n
        (AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.TensorClassNormalization.representativeTensorCycle C D n ij (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C ij.val.1 x) (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass D ij.val.2 y)) :=
      AlgebraicTopology.Kunneth.TensorAlexanderWhitney.Construction.TensorClassNormalization.algebraicKunneth_lof_tmul C D n ij _ _
    _ = homologyMap (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.tensorHomologySplitting C D).hom n
        (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Kunneth.ChainSplittingD.Construction.ChainSplitting.homologyComplex C ⊗ AlgebraicTopology.Kunneth.ChainSplittingD.Construction.ChainSplitting.homologyComplex D) n w) :=
      (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.tensorHomologySplitting C D).hom n w).symm
    _ = homologyMap (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.tensorHomologySplitting C D).hom n
        (homologyMap (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.tensorHomologySplitting C D).inv n (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (C ⊗ D) n z)) :=
      congrArg (homologyMap (AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.tensorHomologySplitting C D).hom n) hh.symm
    _ = AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (C ⊗ D) n z :=
      ((AlgebraicTopology.Kunneth.TensorHomologyD.Construction.TensorHomology.tensorHomologySplitting C D).toHomologyIso n).inv_hom_id_apply _

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.TensorArbitraryRepresentatives
