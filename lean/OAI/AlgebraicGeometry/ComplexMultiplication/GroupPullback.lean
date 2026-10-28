import OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalSheafComparison
import OAI.AlgebraicGeometry.ComplexMultiplication.RationalGroupEndomorphisms
import OAI.Algebra.Homology.Notation

/-! # Group Pullback -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.GroupPullback

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

/-! # The actual group-endomorphism pullback on the original rational H¹ -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint OAI.AlgebraicTopology.Singular

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] [GrpObj X] [IsCommMonObj X]

/-- Pullback along an actual algebraic group endomorphism, transported through the proved
canonical singular/constant-sheaf comparison on the original rational H¹. -/
def groupEndomorphismH1Pullback (f : GroupEndomorphismRing.GroupEndomorphism X) : Module.End ℚ H^1(X; ℚ) :=
  let e := CanonicalSheafComparison.canonicalSingularToConstantSheafLinearEquiv ℚ X 1
  e.conjAlgEquiv ℚ (AlgebraicTopology.Singular.CohomologyTo.cohomologyMap ℚ 1
    (TopCat.ofHom (ComplexPoint.Basic.Point.continuousMap (GroupEndomorphismRing.GroupEndomorphism.toHom X f))))

/-- The identity group endomorphism induces the identity on the original rational H¹. -/
lemma groupEndomorphismH1Pullback_one : groupEndomorphismH1Pullback X 1 = LinearMap.id := by
  have h : TopCat.ofHom (ComplexPoint.Basic.Point.continuousMap (GroupEndomorphismRing.GroupEndomorphism.toHom X (1 : GroupEndomorphismRing.GroupEndomorphism X))) =
      𝟙 (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) := by
    ext z
    rfl
  simp only [groupEndomorphismH1Pullback, h, AlgebraicTopology.Singular.CohomologyTo.cohomologyMap_id, ← Module.End.one_eq_id, map_one]

/-- Composition of algebraic group endomorphisms gives the expected contravariant
composition on the original rational H¹. -/
lemma groupEndomorphismH1Pullback_mul (f g : GroupEndomorphismRing.GroupEndomorphism X) :
    groupEndomorphismH1Pullback X (f * g) =
      (groupEndomorphismH1Pullback X g).comp (groupEndomorphismH1Pullback X f) := by
  let F := TopCat.ofHom (ComplexPoint.Basic.Point.continuousMap (GroupEndomorphismRing.GroupEndomorphism.toHom X f))
  let G := TopCat.ofHom (ComplexPoint.Basic.Point.continuousMap (GroupEndomorphismRing.GroupEndomorphism.toHom X g))
  have h : TopCat.ofHom (ComplexPoint.Basic.Point.continuousMap (GroupEndomorphismRing.GroupEndomorphism.toHom X (f * g))) = G ≫ F := by
    apply ConcreteCategory.hom_ext
    intro z
    change z ≫ (g.toMul.hom.hom ≫ f.toMul.hom.hom) =
      (z ≫ g.toMul.hom.hom) ≫ f.toMul.hom.hom
    exact (Category.assoc z g.toMul.hom.hom f.toMul.hom.hom).symm
  unfold groupEndomorphismH1Pullback
  rw [h, AlgebraicTopology.Singular.CohomologyTo.cohomologyMap_comp]
  exact map_mul ((CanonicalSheafComparison.canonicalSingularToConstantSheafLinearEquiv ℚ X 1).conjAlgEquiv ℚ)
    (AlgebraicTopology.Singular.CohomologyTo.cohomologyMap ℚ 1 G) (AlgebraicTopology.Singular.CohomologyTo.cohomologyMap ℚ 1 F)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.GroupPullback
