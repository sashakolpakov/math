import OAI.AlgebraicGeometry.DivisorClass.Chern.RightPointCrossNormalization
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.PositiveComplexSphere
import OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.FillingCycle

/-! # Right Point Projection Filling -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.RightPointProjectionFilling

noncomputable section

/-! Projection of an actual right-point cross preserves the relative
class of every filling in a contractible ambient space. Its native
boundary is unchanged in homology by the proved ordinary point homotopy. -/

open _root_.CategoryTheory _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem singularRightPointCross_projection (X Y : TopCat.{0}) (y : Y) :
    Singular.RightPointCross.singularRightPointCross ℚ X Y y ≫ (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (TopCat.prodFst (X := X) (Y := Y)) =
      Singular.RightPointCross.unitRightPointProjection ℚ X := by
  let f : TopCat.of Unit ⟶ Y := TopCat.ofHom ⟨fun _ => y, continuous_const⟩
  have h := Singular.RightPointCross.singularRightPointCross_naturality ℚ (𝟙 X) f ()
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  change _ = Singular.RightPointCross.singularRightPointCross ℚ X Y y at h
  rw [← h, Category.assoc, ← CategoryTheory.Functor.map_comp]
  rfl

theorem unitRightPointProjection_homology (X : TopCat.{0}) (n : ℕ) :
    homologyMap (Singular.RightPointCross.unitRightPointProjection ℚ X) n = 𝟙 (((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).obj X).homology n) := by
  have h := (RightPointCrossNormalization.unitRightPointProjectionHomotopy ℚ X).homologyMap_eq n
  simpa only [homologyMap_id] using h

variable (X : TopCat.{0}) (A : Set X) (n : ℕ)
variable (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).X (n + 1))
variable (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of A)) n)
variable (hB : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).d (n + 1) n B =
  (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ X A).f n z.val)

include hB in
theorem unitRightPointFilling_boundary :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).d (n + 1) n ((Singular.RightPointCross.unitRightPointProjection ℚ X).f (n + 1) B) =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ X A).f n ((Singular.RightPointCross.unitRightPointProjection ℚ (TopCat.of A)).f n z.val) := by
  have h := ConcreteCategory.congr_hom ((Singular.RightPointCross.unitRightPointProjection ℚ X).comm (n + 1) n) B
  change _ = (Singular.RightPointCross.unitRightPointProjection ℚ X).f n ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).d (n + 1) n B) at h
  rw [hB] at h
  have hn := Singular.RightPointCross.unitRightPointProjection_naturality ℚ (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A)
  exact h.trans (ConcreteCategory.congr_hom (congrArg (fun f => f.f n) hn) z.val)

def unitRightPointRelativeFillingCycle : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) (n + 1) :=
  Relative.FillingCycle.relativeFillingCycle ℚ X A n ((Singular.RightPointCross.unitRightPointProjection ℚ X).f (n + 1) B)
    (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (Singular.RightPointCross.unitRightPointProjection ℚ (TopCat.of A)) n z)
    (unitRightPointFilling_boundary X A n B z hB)

theorem unitRightPointRelativeFillingCycle_class [ContractibleSpace X] :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) (n + 1) (unitRightPointRelativeFillingCycle X A n B z hB) =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) (n + 1) (Relative.FillingCycle.relativeFillingCycle ℚ X A n B z hB) := by
  apply Rational.PositiveComplexSphere.rationalRelativeBoundary_injective X A n
  rw [Relative.FillingCycle.relativeFillingCycle_boundary]
  have h := Relative.FillingCycle.relativeFillingCycle_boundary ℚ X A n ((Singular.RightPointCross.unitRightPointProjection ℚ X).f (n + 1) B)
    (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (Singular.RightPointCross.unitRightPointProjection ℚ (TopCat.of A)) n z)
    (unitRightPointFilling_boundary X A n B z hB)
  refine h.trans ?_
  erw [← AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality (Singular.RightPointCross.unitRightPointProjection ℚ (TopCat.of A)) n z,
    unitRightPointProjection_homology]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.RightPointProjectionFilling
