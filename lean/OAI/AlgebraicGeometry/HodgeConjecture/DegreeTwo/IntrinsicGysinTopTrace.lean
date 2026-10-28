import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicGysinAdjunction
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicTopPushforward

/-! # Intrinsic Gysin Top Trace -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicGysinTopTrace.Constructions

noncomputable section

/-! Native Gysin in source top degree preserves the genuine fundamental trace with the target degree transported explicitly. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {d e : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
variable [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]
variable [ChartedSpace (Fin d → ℂ) M] [ChartedSpace (Fin e → ℂ) N]
variable [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M] [IsManifold 𝓘(ℂ, Fin e → ℂ) 1 N]

theorem nativeCompactCohomologyPushforward_top_trace (f : TopCat.of M ⟶ TopCat.of N)
    (t : ℕ) (ht : t+0=2*e) (h : t=2*e)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) (2*d)) :
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace e (M := N)
      (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of N)) h)
        (IntrinsicGysinAdjunction.Constructions.nativeCompactCohomologyPushforward (d := d) (e := e) f (2*d) t 0 rfl ht a)) =
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace d (M := M) a := by
  subst t
  exact ConcreteCategory.congr_hom (IntrinsicTopPushforward.Constructions.nativeTopCohomologyPushforward_trace (d := d) (e := e) f) a

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicGysinTopTrace.Constructions
