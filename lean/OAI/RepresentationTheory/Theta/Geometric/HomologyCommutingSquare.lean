import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
import OAI.AlgebraicTopology.Kunneth.ProductModelsAs

/-! # Homology Commuting Square -/

namespace OAI.RepresentationTheory.Theta.Geometric.HomologyCommutingSquare

noncomputable section

/-! Actual commuting continuous maps induce commuting maps on singular homology. -/

open _root_.CategoryTheory OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality _root_.HomologicalComplex

variable {R : Type} [Field R] {X Y Z : TopCat.{0}}

theorem homologyPushforward_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (v : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).homology n) :
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := R) g n (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := R) f n v) =
      AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := R) (f ≫ g) n v := by
  have h := (congrArg (fun a => homologyMap a n)
    ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains R).map_comp f g)).trans
      (homologyMap_comp _ _ n)
  exact (ConcreteCategory.congr_hom h v).symm

theorem homologyPushforward_commuting (f : X ⟶ Y) (a : X ⟶ X) (b : Y ⟶ Y)
    (h : f ≫ b = a ≫ f) (n : ℕ) (v : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).homology n) :
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := R) b n (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := R) f n v) =
      AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := R) f n (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := R) a n v) := by
  rw [homologyPushforward_comp_apply, homologyPushforward_comp_apply, h]

end

end OAI.RepresentationTheory.Theta.Geometric.HomologyCommutingSquare
