import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportedProductTest
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.CompactProductTrace

/-! # Normal Coordinate Integration -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalCoordinateIntegration.Constructions

noncomputable section

/-!
# DegreeTwo: actual supported integration over a coordinate normal factor

The input is any relative test whose support is bounded in the tangential
factor; it need not be compactly supported in the ambient product. Cupping
with the actual normal class produces compact support. Its trace is the
trace of its actual zero-section restriction times the proved nonzero
local product coefficient.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

def normalCoordinateTestRestriction (c d : ℕ) (K : Compacts (Fin d → ℂ))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Fin c → ℂ) × (Fin d → ℂ)))
      (Prod.snd ⁻¹' (K : Set (Fin d → ℂ))ᶜ) (2*d)) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ)) (2*d) :=
  AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ)) K (2*d)
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (CycleClass.Geometric.NormalProductPair.Cycles.normalProductSection (Fin c → ℂ) (Fin d → ℂ) 0)
      (A := (K : Set (Fin d → ℂ))ᶜ) (B := Prod.snd ⁻¹' (K : Set (Fin d → ℂ))ᶜ)
      (fun _ hx => hx) (2*d) b)

def normalCoordinateSupportedCupTop (c d : ℕ) (K : Compacts (Fin d → ℂ))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Fin c → ℂ) × (Fin d → ℂ)))
      (Prod.snd ⁻¹' (K : Set (Fin d → ℂ))ᶜ) (2*d)) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Fin c → ℂ) × (Fin d → ℂ))) (2*(c+d)) :=
  eqToHom (congrArg (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of ((Fin c → ℂ) × (Fin d → ℂ)))) (Nat.mul_add 2 c d).symm)
    (SupportedProductTest.Constructions.compactFirstFactorSupportedCup (TopCat.of (Fin c → ℂ)) (TopCat.of (Fin d → ℂ))
      ⟨{0},isCompact_singleton⟩ K (2*c) (2*d) (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass c) b)

theorem normalCoordinateSupportedCupTop_eq_product (c d : ℕ) (K : Compacts (Fin d → ℂ))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Fin c → ℂ) × (Fin d → ℂ)))
      (Prod.snd ⁻¹' (K : Set (Fin d → ℂ))ᶜ) (2*d)) :
    normalCoordinateSupportedCupTop c d K b =
      CompactProductTrace.Constructions.compactExteriorTopProduct c d (CompactPointNormalization.Constructions.compactPointDualClass c)
        (normalCoordinateTestRestriction c d K b) := by
  unfold normalCoordinateSupportedCupTop
  rw [SupportedProductTest.Constructions.compactFirstFactorSupportedCup_eq_stage _ _ 0 (CycleClass.Geometric.NormalProductPair.Cycles.normalLinearContraction (Fin c → ℂ))]
  unfold CompactProductTrace.Constructions.compactExteriorTopProduct CompactPointNormalization.Constructions.compactPointDualClass normalCoordinateTestRestriction
  rw [CompactExteriorCup.Constructions.compactExteriorCup_stage]

theorem normalCoordinateSupportedCupTop_trace (c d : ℕ) (K : Compacts (Fin d → ℂ))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Fin c → ℂ) × (Fin d → ℂ)))
      (Prod.snd ⁻¹' (K : Set (Fin d → ℂ))ᶜ) (2*d)) :
    CompactProductTrace.Constructions.compactProductCoordinateTrace c d (normalCoordinateSupportedCupTop c d K b) =
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace d (M := Fin d → ℂ) (normalCoordinateTestRestriction c d K b) *
        LocalProductCoefficient.Constructions.localProductCupCoefficient c d := by
  rw [normalCoordinateSupportedCupTop_eq_product, CompactProductTrace.Constructions.compactExteriorTopProduct_trace]
  have hn : AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace c (M := Fin c → ℂ) (CompactPointNormalization.Constructions.compactPointDualClass c) = 1 := by
    rw [AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace_coordinate]
    exact CompactPointNormalization.Constructions.compactPointDualClass_normalization c
  rw [hn, one_mul]

theorem normalCoordinateSupportedCupTop_trace_zero_iff (c d : ℕ) (K : Compacts (Fin d → ℂ))
    (b : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Fin c → ℂ) × (Fin d → ℂ)))
      (Prod.snd ⁻¹' (K : Set (Fin d → ℂ))ᶜ) (2*d)) :
    CompactProductTrace.Constructions.compactProductCoordinateTrace c d (normalCoordinateSupportedCupTop c d K b) = 0 ↔
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace d (M := Fin d → ℂ) (normalCoordinateTestRestriction c d K b) = 0 := by
  rw [normalCoordinateSupportedCupTop_trace, mul_eq_zero]
  exact or_iff_left (LocalProductCoefficient.Constructions.localProductCupCoefficient_ne_zero c d)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalCoordinateIntegration.Constructions
