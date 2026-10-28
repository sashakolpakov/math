import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.Equations
import OAI.AlgebraicGeometry.Resolution.Blowups.OptionalBoundaryLabels
import OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.CenterPartialLabels

/-! # Partial Label Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary

noncomputable section

/-! Exact mixed transforms for partially retained labels and arbitrary unit factors. -/

universe u v t

theorem PartialLabelTransform.Construction.blowupMixedBoundaryFamily_pullbackLabels
    {R : Type u} [CommRing R] {ι : Type v} {κ : Type t}
    (I : Ideal R) (a : I) (w : κ → R) (G : Finset κ) (hw : ∀ j ∈ G, w j ∈ I)
    (r : ι → Option κ) (v u : ι → R)
    (hv : ∀ j, v j = u j * (match r j with | none => 1 | some s => w s))
    (F : Finset ι) (hF : ∀ j, j ∈ F ↔ ∃ s ∈ G, r j = some s)
    (hvI : ∀ j ∈ F, v j ∈ I) (j : Option ι) :
    Equations.Construction.blowupMixedBoundaryFamily I a F v hvI j =
      (match j with | none => 1 | some i => Blowup.Charts.Construction.blowupChartConstants I a (u i)) *
        (match OptionalBoundaryLabels.Construction.adjoinPartialBoundaryLabel r j with
          | none => 1 | some s => Equations.Construction.blowupMixedBoundaryFamily I a G w hw s) := by
  classical
  cases j with
  | none => exact (one_mul (Blowup.Charts.Construction.blowupChartConstants I a a.val)).symm
  | some j =>
      cases hrj : r j with
      | none =>
          have hj : j ∉ F := by simp only [hF j, hrj, reduceCtorEq, and_false, exists_false, not_false_eq_true]
          have hvj : v j = u j := by simpa only [hrj, mul_one] using hv j
          simp only [Equations.Construction.blowupMixedBoundaryFamily, dite_eq_right hj, OptionalBoundaryLabels.Construction.adjoinPartialBoundaryLabel,
            hrj, Option.map_none, hvj]
          exact (mul_one (Blowup.Charts.Construction.blowupChartConstants I a (u j))).symm
      | some s =>
          have hjmem : j ∈ F ↔ s ∈ G := by
            simp only [hF j, hrj, Option.some.injEq]
            constructor
            · rintro ⟨s', hs', he⟩
              exact he.symm ▸ hs'
            · intro hs
              exact ⟨s, hs, rfl⟩
          have hvj : v j = u j * w s := by simpa only [hrj] using hv j
          by_cases hs : s ∈ G
          · have hj := hjmem.mpr hs
            simp only [Equations.Construction.blowupMixedBoundaryFamily, dite_eq_left hj, OptionalBoundaryLabels.Construction.adjoinPartialBoundaryLabel,
              hrj, Option.map_some, dite_eq_left hs]
            apply (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a).left
            change Blowup.Charts.Construction.blowupChartConstants I a a.val * ExceptionalIdeal.Construction.blowupChartRatio I a ⟨v j, hvI j hj⟩ =
              Blowup.Charts.Construction.blowupChartConstants I a a.val *
                (Blowup.Charts.Construction.blowupChartConstants I a (u j) * ExceptionalIdeal.Construction.blowupChartRatio I a ⟨w s, hw s hs⟩)
            rw [ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio]
            change Blowup.Charts.Construction.blowupChartConstants I a (v j) = Blowup.Charts.Construction.blowupChartConstants I a a.val *
              (Blowup.Charts.Construction.blowupChartConstants I a (u j) * ExceptionalIdeal.Construction.blowupChartRatio I a ⟨w s, hw s hs⟩)
            rw [hvj, map_mul]
            rw [mul_left_comm (Blowup.Charts.Construction.blowupChartConstants I a a.val), ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio]
          · have hj : j ∉ F := fun h => hs (hjmem.mp h)
            simp only [Equations.Construction.blowupMixedBoundaryFamily, dite_eq_right hj, OptionalBoundaryLabels.Construction.adjoinPartialBoundaryLabel,
              hrj, Option.map_some, dite_eq_right hs, hvj, map_mul]

theorem CenterCharts.Construction.HasMixedBoundaryCenterCharts.pullbackLabels
    {k : Type u} [CommRing k] {R : CommRingCat.{u}} [Algebra k R]
    {ι : Type v} {κ : Type t} {I : Ideal R} {w : κ → R} {G : Finset κ}
    (h : CenterCharts.Construction.HasMixedBoundaryCenterCharts k R I w G)
    (r : ι → Option κ) (hr : ∀ i j s, r i = some s → r j = some s → i = j)
    (v u : ι → R) (hu : ∀ j, IsUnit (u j))
    (hv : ∀ j, v j = u j * (match r j with | none => 1 | some s => w s))
    (F : Finset ι) (hF : ∀ j, j ∈ F ↔ ∃ s ∈ G, r j = some s) :
    CenterCharts.Construction.HasMixedBoundaryCenterCharts k R I v F := by
  intro p hp
  obtain ⟨C⟩ := h p hp
  exact ⟨C.pullbackLabels r hr v u hu hv F hF⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary
