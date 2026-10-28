import OAI.AlgebraicGeometry.ComplexMultiplication.RelativeDualAbsoluteExtension
import OAI.AlgebraicGeometry.ComplexMultiplication.RelativeNeighborhoodPullback

/-! # Relative Absolute Top Pullback -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.RelativeAbsoluteTopPullback

noncomputable section

/-! # Forgetting a support after pullback to the full open neighborhood -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory OAI.AlgebraicTopology.Singular _root_.TopologicalSpace
variable (R : Type) [CommRing R]
theorem relativeAbsoluteTopPullback (Y : TopCat.{0}) (S : Set Y) (Q : TopPair.{0})
    (f : AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (Set.univ : Set Y) S ⟶ Q)
    (g : Y ⟶ Q.fst) (he : (Opens.inclusionTopIso Y).inv ≫ f.right = g)
    (n : ℕ) (a : AlgebraicTopology.Singular.Cohomology.RelativeCohomology R Q n) :
    AlgebraicTopology.Singular.CohomologyTo.cohomologyMap R n (Opens.inclusionTopIso Y).inv
      (AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyToAbsolute R (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (Set.univ : Set Y) S)
        n (AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap R n f a)) =
    AlgebraicTopology.Singular.CohomologyTo.cohomologyMap R n g (AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyToAbsolute R Q n a) := by
  have hn := RelativeDualAbsoluteExtension.relativeToAbsolute_naturality R f n a
  have hc := AlgebraicTopology.Singular.CohomologyTo.cohomologyMap_comp R n (Opens.inclusionTopIso Y).inv f.right
  have hca := congrArg (fun k => k (AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyToAbsolute R Q n a)) hc
  have hg := congrArg (fun k => AlgebraicTopology.Singular.CohomologyTo.cohomologyMap R n k
    (AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyToAbsolute R Q n a)) he
  exact (congrArg (AlgebraicTopology.Singular.CohomologyTo.cohomologyMap R n (Opens.inclusionTopIso Y).inv) hn).trans
    (hca.symm.trans hg)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.RelativeAbsoluteTopPullback
