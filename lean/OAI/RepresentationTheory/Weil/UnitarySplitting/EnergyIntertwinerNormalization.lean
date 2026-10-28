import OAI.RepresentationTheory.Weil.UnitarySplitting.Kernel
import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraIntertwinerNormalization

/-! # Energy Intertwiner Normalization -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.EnergyIntertwinerNormalization.Construction

noncomputable section

/-! Positive energy scaling normalizes an intertwiner over any local field. -/

theorem energyIntertwiner_positive_normalization
    {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
    [MeasurableSpace F] [BorelSpace F] {d : ℕ}
    (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ) (hc : Continuous (fun t : F => ψ t))
    (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (g : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → Local.FunctionsMetaplectic.Construction.PhaseSpace F d)
    (M : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (hM : ∀ v f, M (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f) =
      HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (g v) (M f))
    (s : ℝ) (hs : 0 < s) (hMs : ∀ f, Local.FunctionsMetaplectic.Construction.l2Energy F d (M f) = s * Local.FunctionsMetaplectic.Construction.l2Energy F d f)
    (U : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (hU : ∀ v f, U (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f) =
      HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (g v) (U f))
    (hUe : ∀ f, Local.FunctionsMetaplectic.Construction.l2Energy F d (U f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f) :
    ∃ (r : ℝ) (V : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d), 0 < r ∧
      (∀ f, M f = (r : ℂ) • V f) ∧
      (∀ f, Local.FunctionsMetaplectic.Construction.l2Energy F d (V f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f) ∧
      (∀ v f, V (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f) =
        HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (g v) (V f)) := by
  let : SecondCountableTopology F := TestSpaceAnalysis.Construction.localField_secondCountable F hF
  let r := Real.sqrt s
  have hr : 0 < r := Real.sqrt_pos.mpr hs
  have hrs : r ^ 2 = s := Real.sq_sqrt hs.le
  let N : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d := (r : ℂ)⁻¹ • M
  have hNe (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) : Local.FunctionsMetaplectic.Construction.l2Energy F d (N f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f := by
    change Local.FunctionsMetaplectic.Construction.l2Energy F d ((r : ℂ)⁻¹ • M f) = _
    rw [FourierPairing.Construction.l2Energy_smul, hMs, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      inv_pow, hrs, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
  have hN (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
      N (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f) = HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (g v) (N f) := by
    change (r : ℂ)⁻¹ • M (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f) =
      HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (g v) ((r : ℂ)⁻¹ • M f)
    rw [hM, map_smul]
  let A : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d := U.symm.toLinearMap.comp N
  have hAe (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) : Local.FunctionsMetaplectic.Construction.l2Energy F d (A f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f := by
    have hh := hUe (U.symm (N f))
    rw [U.apply_symm_apply, hNe] at hh
    exact hh.symm
  have hA (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
      A (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f) = HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v (A f) := by
    apply U.injective
    change U (U.symm (N (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f))) =
      U (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v (U.symm (N f)))
    rw [U.apply_symm_apply, hU, U.apply_symm_apply, hN]
  obtain ⟨z, hz⟩ := Kernel.Construction.unitary_heisenberg_commutant_scalar hF ψ hc hu hn A hAe hA
  let V := U.trans (Oscillator.Construction.scalarOperator d z)
  have hV (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) : V f = (z : ℂ) • U f := rfl
  refine ⟨r, V, hr, ?_, ?_, ?_⟩
  · intro f
    have hh := congrArg U (hz f)
    change U (U.symm (N f)) = U ((z : ℂ) • f) at hh
    rw [U.apply_symm_apply, map_smul] at hh
    have hscale := congrArg (fun v : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d => (r : ℂ) • v) hh
    change (r : ℂ) • ((r : ℂ)⁻¹ • M f) = (r : ℂ) • ((z : ℂ) • U f) at hscale
    rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne'), one_smul] at hscale
    exact hscale
  · intro f
    rw [hV, Oscillator.Construction.l2Energy_circle_smul, hUe]
  · intro v f
    rw [hV, hV, hU, map_smul]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.EnergyIntertwinerNormalization.Construction
