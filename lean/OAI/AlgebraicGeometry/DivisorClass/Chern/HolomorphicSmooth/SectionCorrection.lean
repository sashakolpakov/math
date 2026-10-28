import OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.SmoothDolbeault

/-! # Section Correction -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.SectionCorrection

noncomputable section

/-! Correct an original global smooth section to an actual holomorphic section using the constructed bounded Dolbeault primitive. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

theorem holomorphicLine_section_of_equal_dolbeault
    (a b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 0)
    (hb : HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 b = HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 a) :
    ∃ s : HolomorphicSection.Data.HolomorphicLineSection u ⊤, HolomorphicLine.Dolbeault.holomorphicLineDolbeaultInclusion u ⊤ s = a - b := by
  have hz : a - b ∈ LinearMap.ker (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0) :=
    ((HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0).map_sub a b).trans
      ((congrArg (fun z : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 => HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 a - z) hb).trans
        (sub_self _))
  exact (congrArg (fun S : Submodule ℂ (HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 0) => a - b ∈ S)
    (HolomorphicLine.Dolbeault.holomorphicLineDolbeault_zero_kernel u ⊤)).mp hz

theorem holomorphicMetricSmoothSection_correction
    (hc : h.hasBoundedSmoothDolbeaultPrimitives V) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 0) :
    ∃ s : HolomorphicSection.Data.HolomorphicLineSection u ⊤, ∃ b : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 0,
      HolomorphicLine.Dolbeault.holomorphicLineDolbeaultInclusion u ⊤ s = a - b ∧
        HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 b = HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 a ∧
        ‖Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 0 b.val‖ ≤
          ‖Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 a)‖ := by
  let result := hc (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 a) (HolomorphicLine.Dolbeault.holomorphicLineDolbeault_squared u ⊤ 0 a)
  let sectionResult := holomorphicLine_section_of_equal_dolbeault V a result.choose result.choose_spec.1
  exact ⟨sectionResult.choose, result.choose, sectionResult.choose_spec, result.choose_spec⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.SectionCorrection
