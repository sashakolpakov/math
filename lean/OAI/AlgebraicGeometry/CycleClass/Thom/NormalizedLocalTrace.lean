import OAI.AlgebraicGeometry.CycleClass.Thom.Local.ProductCoefficientOne
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalCoordinateIntegration
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairIntrinsicTrace
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactCupEvaluation
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactLeftCup

/-! # Normalized Local Trace -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizedLocalTrace

noncomputable section

/-! Exact product and normal-pair trace formulas in arbitrary complex
codimension, using the proved coefficient-one normalization. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Local.ProductCoefficientOne.Constructions
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Constructions

theorem compactExteriorTopProduct_trace_normalized (d c : ℕ)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ)) (2 * d))
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin c → ℂ)) (2 * c)) :
    HodgeConjecture.DegreeTwo.CompactProductTrace.Constructions.compactProductCoordinateTrace d c (HodgeConjecture.DegreeTwo.CompactProductTrace.Constructions.compactExteriorTopProduct d c a b) =
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace d (M := Fin d → ℂ) a * AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace c (M := Fin c → ℂ) b := by
  rw [HodgeConjecture.DegreeTwo.CompactProductTrace.Constructions.compactExteriorTopProduct_trace, Local.ProductCoefficientOne.Constructions.localProductCupCoefficient_one, mul_one]

theorem normalCoordinateSupportedCupTop_trace_normalized (c d : ℕ) (K : Compacts (Fin d → ℂ))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Fin c → ℂ) × (Fin d → ℂ)))
      (Prod.snd ⁻¹' (K : Set (Fin d → ℂ))ᶜ) (2 * d)) :
    HodgeConjecture.DegreeTwo.CompactProductTrace.Constructions.compactProductCoordinateTrace c d (HodgeConjecture.DegreeTwo.NormalCoordinateIntegration.Constructions.normalCoordinateSupportedCupTop c d K b) =
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace d (M := Fin d → ℂ) (HodgeConjecture.DegreeTwo.NormalCoordinateIntegration.Constructions.normalCoordinateTestRestriction c d K b) := by
  rw [HodgeConjecture.DegreeTwo.NormalCoordinateIntegration.Constructions.normalCoordinateSupportedCupTop_trace, Local.ProductCoefficientOne.Constructions.localProductCupCoefficient_one, mul_one]

theorem normalPairCompactGysinTop_trace_normalized
    {M N : Type} [TopologicalSpace N] {c d p : ℕ} {f : M → N} {x : M}
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin c → ℂ) f x)
    [ChartedSpace (Fin p → ℂ) N] [T2Space N] [IsManifold 𝓘(ℂ, Fin p → ℂ) 1 N]
    (hdim : c + d = p)
    (hq : ContMDiffOn 𝓘(ℂ, Fin p → ℂ)
      𝓘(ℂ, (Fin d → ℂ) × (Fin c → ℂ)) ∞ P.ambientChart P.ambientChart.source)
    (hqi : ContMDiffOn 𝓘(ℂ, (Fin d → ℂ) × (Fin c → ℂ))
      𝓘(ℂ, Fin p → ℂ) ∞ P.ambientChart.symm P.ambientChart.target)
    (a : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairTangentSpace P)) (2 * d)) :
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace p (M := P.openNeighborhood)
      (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood))
        (congrArg (fun n => 2 * n) hdim)) (HodgeConjecture.DegreeTwo.NormalPairIntrinsicTrace.Constructions.normalPairCompactGysinTop P a)) =
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace d (M := HodgeConjecture.DegreeTwo.NormalPairIntrinsicTrace.Constructions.normalPairTangentOpen P) a := by
  subst p
  simpa only [eqToHom_refl, CategoryTheory.id_apply, Local.ProductCoefficientOne.Constructions.localProductCupCoefficient_one, mul_one] using
    HodgeConjecture.DegreeTwo.NormalPairIntrinsicTrace.Constructions.normalPairCompactGysinTop_nativeTrace P hq hqi a

theorem compactCohomologyLeftCup_even_trace (d p : ℕ) {M : Type}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (Fin d → ℂ) M]
    [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]
    (n : ℕ) (h : 2 * p + n = 2 * d)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) (2 * p))
    (b : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) n) :
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace d (M := M)
      (eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M)) h)
        (HodgeConjecture.DegreeTwo.CompactLeftCup.Constructions.compactCohomologyLeftCup (TopCat.of M) (2 * p) n a b)) =
      AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation d (2 * p) n h a b := by
  rw [HodgeConjecture.DegreeTwo.CompactLeftCup.Constructions.compactCohomologyLeftCup_graded_comm]
  simp only [pow_mul, neg_one_sq, one_pow, one_smul]
  rw [HodgeConjecture.DegreeTwo.CompactCupEvaluation.Constructions.compactCohomologyDegreeCast_trans (TopCat.of M) (Nat.add_comm n (2 * p)) h (by omega)]
  exact HodgeConjecture.DegreeTwo.CompactCupTrace.Constructions.compactCohomologyRightCup_trace d n (2 * p) (by omega) a b

end Constructions

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizedLocalTrace
