import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.BettiDeRhamNaturality
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DeRhamPullbackLinear
import OAI.AlgebraicGeometry.ComplexMultiplication.Hodge.Endomorphisms

/-! # Filtration Pullback -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FiltrationPullback

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

/-! # Actual algebraic group pullback preserves the original H¹ filtration

The original rational H¹ action, original tensor comparison, and original
geometric filtration are intertwined by the genuine de Rham pullback.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint
open scoped TensorProduct

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

/-- Membership exposes precisely the original tensor comparison and original F¹. -/
theorem mem_h1HodgeEndomorphismAlgebra_iff (g : Module.End ℚ H^1(X; ℚ)) :
    g ∈ Hodge.Endomorphisms.h1HodgeEndomorphismAlgebra X ↔
      ∀ z : ℂ ⊗[ℚ] H^1(X; ℚ),
        Definitions.h1Comparison X z ∈ ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltrationComplexSubmodule X 1 1 →
        Definitions.h1Comparison X (TensorProduct.map LinearMap.id g z) ∈
          ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltrationComplexSubmodule X 1 1 := Iff.rfl

variable [Foundations.ProjectiveSpaceIs.IsProjective X.hom] [GrpObj X]

/-- The unchanged original scalar-extension comparison intertwines actual group endomorphisms. -/
theorem groupEndomorphismH1Pullback_h1Comparison (f : GroupEndomorphismRing.GroupEndomorphism X)
    (z : ℂ ⊗[ℚ] H^1(X; ℚ)) :
    FilteredPullback.originalDeRhamHypercohomologyPullback (GroupEndomorphismRing.GroupEndomorphism.toHom X f) 1
        (Definitions.h1Comparison X z) =
      Definitions.h1Comparison X (TensorProduct.map LinearMap.id (GroupPullback.groupEndomorphismH1Pullback X f) z) := by
  change DeRhamPullbackLinear.originalDeRhamHypercohomologyPullbackLinear (GroupEndomorphismRing.GroupEndomorphism.toHom X f) 1
    (Definitions.h1Comparison X z) = _
  induction z using TensorProduct.inductionOn with
  | tmul c v =>
    rw [CMComparisonTo.h1Comparison_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
      CMComparisonTo.h1Comparison_tmul]
    rw [map_smul]
    exact congrArg (c • ·) (BettiDeRhamNaturality.groupEndomorphismH1Pullback_deRham X f v)
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Every actual algebraic group endomorphism preserves the unchanged original geometric F¹. -/
theorem groupEndomorphismH1Pullback_mem_h1HodgeEndomorphismAlgebra (f : GroupEndomorphismRing.GroupEndomorphism X) :
    GroupPullback.groupEndomorphismH1Pullback X f ∈ Hodge.Endomorphisms.h1HodgeEndomorphismAlgebra X := by
  apply (mem_h1HodgeEndomorphismAlgebra_iff X _).mpr
  intro z hz
  rw [← groupEndomorphismH1Pullback_h1Comparison]
  exact FilteredPullback.originalDeRhamHypercohomologyPullback_mem_hodgeFiltration
    (GroupEndomorphismRing.GroupEndomorphism.toHom X f) 1 1 hz

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FiltrationPullback
