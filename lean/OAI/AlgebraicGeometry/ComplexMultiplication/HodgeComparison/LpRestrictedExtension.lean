import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpLocalization

/-! # Lp Restricted Extension -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpRestrictedExtension.CM.Construction

noncomputable section

/-! Extension by zero from a restricted measure, with its actual
indicator-function formula and preserved L2 norm. -/

open _root_.MeasureTheory Set Filter

variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F] [NormedSpace ℂ F]
  (μ : Measure X) {S : Set X} (hS : MeasurableSet S)

def lpRestrictedZeroExtension : Lp F 2 (μ.restrict S) →ₗᵢ[ℂ] Lp F 2 μ :=
  (LpLocalization.CM.Construction.lpSubtypeZeroExtension μ hS).comp
    (Lp.compMeasurePreservingₗᵢ ℂ (Subtype.val : S → X)
      ⟨measurable_subtype_coe, map_comap_subtype_coe hS μ⟩)

theorem lpRestrictedZeroExtension_coe_of_ae (u : Lp F 2 (μ.restrict S)) (f : X → F)
    (hf : u =ᵐ[μ.restrict S] f) :
    lpRestrictedZeroExtension μ hS u =ᵐ[μ] S.indicator f := by
  have hsub : Lp.compMeasurePreserving (Subtype.val : S → X)
      ⟨measurable_subtype_coe, map_comap_subtype_coe hS μ⟩ u =ᵐ[μ.comap (Subtype.val : S → X)]
        fun x : S => f x.val :=
    (Lp.coeFn_compMeasurePreserving u ⟨measurable_subtype_coe, map_comap_subtype_coe hS μ⟩).trans
      ((ae_restrict_iff_subtype hS).mp hf)
  refine (LpLocalization.CM.Construction.lpSubtypeZeroExtension_coeFn μ hS _).trans
    ((LpLocalization.CM.Construction.subtypeZeroExtension_ae_eq μ hS hsub).trans ?_)
  apply Eventually.of_forall
  intro x
  by_cases hx : x ∈ S
  · rw [LpLocalization.CM.Construction.subtypeZeroExtension_apply_mem _ hx, indicator_of_mem hx]
  · rw [LpLocalization.CM.Construction.subtypeZeroExtension_apply_notMem _ hx, indicator_of_notMem hx]

theorem lpRestrictedZeroExtension_coe (u : Lp F 2 (μ.restrict S)) :
    lpRestrictedZeroExtension μ hS u =ᵐ[μ] S.indicator u :=
  lpRestrictedZeroExtension_coe_of_ae μ hS u u Filter.EventuallyEq.rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpRestrictedExtension.CM.Construction
