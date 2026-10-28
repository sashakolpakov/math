import OAI.AlgebraicGeometry.ComplexMultiplication.PointBettiBridge
import OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalSheafComparison
import OAI.AlgebraicGeometry.ComplexMultiplication.GroupPullback
import OAI.AlgebraicGeometry.ComplexMultiplication.AbelianGroups

/-! # Betti Bridge -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.BettiBridge

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

/-! # The original H¹ and actual algebraic pullbacks

The older scheme Betti space is identified with the unchanged constant-sheaf
cohomology used by `CM.lean`. The algebraic pullback is the actual scheme map.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint OAI.AlgebraicTopology.Singular

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

variable (R : Type) [Field R] (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

/-- The actual scheme Betti cohomology and the original constant-sheaf cohomology. -/
def schemeConstantCohomologyBridgeEquiv (n : ℕ) :
    Betti.Scheme.schemeBetti (ModuleCat.of R R) X n ≃ₗ[R] H^n(X; R) :=
  (PointBettiBridge.schemeSingularCohomologyBridgeEquiv R X n).trans
    (CanonicalSheafComparison.canonicalSingularToConstantSheafLinearEquiv R X n)

variable [GrpObj X]

/-- The original H¹ action is exactly the actual scheme Betti pullback under the comparison. -/
theorem groupEndomorphismH1Pullback_schemeBetti (f : GroupEndomorphismRing.GroupEndomorphism X)
    (c : Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X 1) :
    GroupPullback.groupEndomorphismH1Pullback X f (schemeConstantCohomologyBridgeEquiv ℚ X 1 c) =
      schemeConstantCohomologyBridgeEquiv ℚ X 1
        ((Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1
          (GroupEndomorphismRing.GroupEndomorphism.toHom X f)).hom c) := by
  simp only [GroupPullback.groupEndomorphismH1Pullback, LinearEquiv.conjAlgEquiv_apply,
    schemeConstantCohomologyBridgeEquiv, LinearEquiv.trans_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [PointBettiBridge.schemeSingularCohomologyBridgeEquiv_naturality ℚ (GroupEndomorphismRing.GroupEndomorphism.toHom X f) 1]

/-- The underlying original action agrees with conjugation of actual scheme Betti pullback. -/
theorem groupEndomorphismH1Pullback_eq_schemeBetti (f : GroupEndomorphismRing.GroupEndomorphism X) :
    GroupPullback.groupEndomorphismH1Pullback X f =
      (schemeConstantCohomologyBridgeEquiv ℚ X 1).conjAlgEquiv ℚ
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1
          (GroupEndomorphismRing.GroupEndomorphism.toHom X f)).hom := by
  apply LinearMap.ext
  intro z
  obtain ⟨c, rfl⟩ := (schemeConstantCohomologyBridgeEquiv ℚ X 1).surjective z
  simp only [LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  simp only [GroupPullback.groupEndomorphismH1Pullback, LinearEquiv.conjAlgEquiv_apply,
    schemeConstantCohomologyBridgeEquiv, LinearEquiv.trans_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [PointBettiBridge.schemeSingularCohomologyBridgeEquiv_naturality ℚ (GroupEndomorphismRing.GroupEndomorphism.toHom X f) 1]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.BettiBridge
