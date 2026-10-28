import OAI.RepresentationTheory.Hecke.SphericalAction
import OAI.RepresentationTheory.Hecke.SphericalActionModelInverse

/-! # Radial Comparison -/

namespace OAI.RepresentationTheory.Hecke.RadialComparison.SphericalActionIntrinsic

noncomputable section

/-! Compare the literal RadialDilation statement space with SphericalAction's native radial
functions. Both are spans of the same ball indicators. The comparison
preserves functions and intertwines the prescribed normalized dilation. -/

variable (q : ℕ) [Fact q.Prime]

def radialComparison : SphericalAction.radialInput q ≃ₗ[ℂ] SphericalActionModelInverse.Radial q :=
  LinearEquiv.refl ℂ _

theorem radialComparison_apply (b : SphericalAction.radialInput q) :
    (radialComparison q b).val = b.val := rfl

def statementDilation : Module.End ℂ (SphericalAction.radialInput q) :=
  (radialComparison q).symm.toLinearMap.comp
    ((RadialDilation.Mem.Realization.dilation q).comp (radialComparison q).toLinearMap)

theorem statementDilation_formula (b : SphericalAction.radialInput q)
    (x : Fin 3 → ℚ_[q]) :
    (statementDilation q b).val x =
      (Real.rpow (q : ℝ) (3 / 2 : ℝ) : ℂ) *
        b.val (fun i => (q : ℚ_[q])⁻¹ * x i) := rfl

theorem normalized_dilation_intertwining (b : SphericalAction.radialInput q) :
    radialComparison q (statementDilation q b) =
      AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity.dilationEquiv q (radialComparison q b) := rfl

theorem normalized_dilation_power_intertwining (M : ℕ)
    (b : SphericalAction.radialInput q) :
    radialComparison q ((statementDilation q ^ M) b) =
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Cyclicity.dilationEquiv q ^ M) (radialComparison q b) := by
  exact (AlgebraicGeometry.HodgeConjecture.CMExtraction.Radial.Dilation.dilationEquiv_pow_apply q M (radialComparison q b)).symm

end

end OAI.RepresentationTheory.Hecke.RadialComparison.SphericalActionIntrinsic
