import OAI.RepresentationTheory.Weil.UnitarySplitting.HeisenbergStability
import OAI.RepresentationTheory.Weil.UnitarySplitting.Weak
import OAI.RepresentationTheory.Weil.UnitarySplitting.FourierCovariance

/-! # Weyl -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.Weyl.Construction

noncomputable section

/-! Unitarity and adjoint identities for the actual Weyl operators. -/

open _root_.MeasureTheory
open scoped InnerProductSpace

variable {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {d : ℕ}
variable (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
variable (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)

theorem heisenbergOperator_energy (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    Local.FunctionsMetaplectic.Construction.l2Energy F d (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f := by
  change (∫ x, ‖Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f.val x‖ ^ 2 ∂ Weak.Construction.referencePositionMeasure F d) =
    ∫ x, ‖f.val x‖ ^ 2 ∂ Weak.Construction.referencePositionMeasure F d
  simp_rw [FourierCovariance.Construction.heisenbergFunction_dot, norm_mul, hu, one_mul]
  exact integral_sub_right_eq_self (fun x => ‖f.val x‖ ^ 2) (FourierCovariance.Construction.phasePosition v)

omit [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] in
theorem heisenbergOperator_composition (v w : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu w f) =
      ψ (Oscillator.Construction.standardSymplecticPairing d v w / 2) • HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (v + w) f := by
  apply Subtype.ext
  exact Heisenberg.Construction.heisenbergFunction_composition ψ v w f.val

omit [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] in
theorem heisenbergOperator_neg_cancel (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (-v) (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f) = f := by
  apply Subtype.ext
  exact Heisenberg.Construction.heisenbergFunction_neg_left_cancel ψ v f.val

theorem heisenbergOperator_inner (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f g : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    ⟪Weak.Construction.testToL2 F d (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f),
      Weak.Construction.testToL2 F d (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v g)⟫_ℂ =
        ⟪Weak.Construction.testToL2 F d f, Weak.Construction.testToL2 F d g⟫_ℂ :=
  Weak.Construction.energy_preserving_inner F d (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v).toLinearMap
    (heisenbergOperator_energy hF ψ hc hu v) f g

theorem heisenbergOperator_adjoint (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f g : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    ⟪Weak.Construction.testToL2 F d g, Weak.Construction.testToL2 F d (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f)⟫_ℂ =
      ⟪Weak.Construction.testToL2 F d (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (-v) g), Weak.Construction.testToL2 F d f⟫_ℂ := by
  have hh := heisenbergOperator_inner hF ψ hc hu (-v) g (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f)
  rw [heisenbergOperator_neg_cancel] at hh
  exact hh.symm

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.Weyl.Construction
