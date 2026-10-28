import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraCayleyOperator
import OAI.RepresentationTheory.Weil.UnitarySplitting.DiagonalNormGaussian

/-! # Ultra Intertwiner Normalization -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.UltraIntertwinerNormalization.Construction

noncomputable section

/-! A nonzero Weyl intertwiner differs from any unitary lift by one
nonzero scalar; its phase therefore gives a positive unitary normalization. -/

variable {F : Type} [NormedField F] [CompleteSpace F] [LocallyCompactSpace F] [CharZero F]
variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
variable [IsUltrametricDist F] {d : ℕ}
variable (hF : ¬ DiscreteTopology F) (ψ : AddChar F ℂ)
variable (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
variable (hn : ∃ x : F, ψ x ≠ 1)
variable (g : Local.FunctionsMetaplectic.Construction.PhaseSpace F d → Local.FunctionsMetaplectic.Construction.PhaseSpace F d)
variable (M : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (hM0 : M ≠ 0)
variable (hM : ∀ v f, M (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f) =
  HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (g v) (M f))
variable (U : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d)
variable (hU : ∀ v f, U (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f) =
  HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (g v) (U f))

include hn hM0 hM hU in
omit [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] in
theorem ultraIntertwiner_scalar_multiple :
    ∃ z : ℂ, z ≠ 0 ∧ ∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d, M f = z • U f := by
  let A : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d := U.symm.toLinearMap.comp M
  have hA (v : Local.FunctionsMetaplectic.Construction.PhaseSpace F d) (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
      A (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f) = HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v (A f) := by
    apply U.injective
    change U (U.symm (M (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f))) =
      U (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v (U.symm (M f)))
    rw [U.apply_symm_apply, hU, U.apply_symm_apply, hM]
  obtain ⟨z, hz⟩ := UltraMultiplier.Construction.ultra_commutant_scalar hF ψ hc hn hu A (fun v f => hA v f)
  have hscalar (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) : M f = z • U f := by
    have hh := congrArg U (hz f)
    change U (U.symm (M f)) = U (z • f) at hh
    rwa [U.apply_symm_apply, map_smul] at hh
  refine ⟨z, ?_, hscalar⟩
  intro hz0
  apply hM0
  apply LinearMap.ext
  intro f
  simpa only [hz0, zero_smul, LinearMap.zero_apply] using hscalar f

include hn hM0 hM hU in
omit [SecondCountableTopology F] in
theorem ultraIntertwiner_positive_normalization
    (henergy : ∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d, Local.FunctionsMetaplectic.Construction.l2Energy F d (U f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f) :
    ∃ (r : ℝ) (V : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d), 0 < r ∧
      (∀ f, M f = (r : ℂ) • V f) ∧
      (∀ f, Local.FunctionsMetaplectic.Construction.l2Energy F d (V f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f) ∧
      (∀ v f, V (HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu v f) =
        HeisenbergStability.Construction.heisenbergOperator hF ψ hc hu (g v) (V f)) := by
  obtain ⟨z, hz0, hz⟩ := ultraIntertwiner_scalar_multiple hF ψ hc hu hn g M hM0 hM U hU
  let ζ := DiagonalNormGaussian.Construction.gaussianCircle z hz0
  let V := U.trans (Oscillator.Construction.scalarOperator d ζ)
  have hV (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) : V f = (ζ : ℂ) • U f := rfl
  refine ⟨‖z‖, V, norm_pos_iff.mpr hz0, ?_, ?_, ?_⟩
  · intro f
    rw [hz, hV, smul_smul]
    congr 1
    change z = (‖z‖ : ℂ) * (z / (‖z‖ : ℂ))
    field_simp [Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz0)]
  · intro f
    rw [hV, Oscillator.Construction.l2Energy_circle_smul, henergy]
  · intro v f
    rw [hV, hV, hU, map_smul]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.UltraIntertwinerNormalization.Construction
