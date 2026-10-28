import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.MixedBoundaryFamily

/-! # Mixed Boundary Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Exact mixed transforms are partial relabellings of the canonical coordinate family, times units. -/

universe u v

variable {k R : Type u} {ι : Type v} [Field k] [CommRing R] [Algebra k R]
  {w : ι → R}

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.mixedBoundary_comparison (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (C : Finset M.indices) (F : Finset ι)
    (hF : ∀ j, j ∈ F ↔ ∃ s ∈ C, M.coordinate j = some s)
    (a : (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map) (j : Option ι) :
    MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily _ a F w (M.coordinateCenter_boundary_mem C F hF) j =
      (match j with | none => 1 | some l => Blowup.Charts.Construction.blowupChartConstants _ a (M.multiplier l)) *
        (match OptionalBoundaryLabels.Construction.adjoinPartialBoundaryLabel M.boundaryCoordinate j with
          | none => 1 | some s => M.mixedCoordinateFamily C a s) := by
  classical
  let : Algebra (MvPolynomial M.indices k) R := M.map.toAlgebra
  let I := (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map
  cases j with
  | none => exact (one_mul (Blowup.Charts.Construction.blowupChartConstants I a a.val)).symm
  | some j =>
      cases hc : M.boundaryCoordinate j with
      | none =>
          have hcoord : M.coordinate j = none := by
            rw [← M.boundaryCoordinate_map j, hc]
            rfl
          have hjF : j ∉ F := by
            intro hj
            obtain ⟨s, _, hs⟩ := (hF j).mp hj
            rw [hcoord] at hs
            cases hs
          simp only [MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily, dite_eq_right hjF, OptionalBoundaryLabels.Construction.adjoinPartialBoundaryLabel, hc, Option.map_none]
          rw [M.equation j, hcoord, mul_one]
          exact (mul_one (Blowup.Charts.Construction.blowupChartConstants I a (M.multiplier j))).symm
      | some s =>
          have hcoord : M.coordinate j = some s.val := by
            rw [← M.boundaryCoordinate_map j, hc]
            rfl
          have hjF : j ∈ F ↔ s.val ∈ C := by
            constructor
            · intro hj
              obtain ⟨t, ht, hjt⟩ := (hF j).mp hj
              have hts : t = s.val := Option.some.inj (hjt.symm.trans hcoord)
              exact hts ▸ ht
            · intro hs
              exact (hF j).mpr ⟨s.val, hs, hcoord⟩
          by_cases hs : s.val ∈ C
          · have hj : j ∈ F := hjF.mpr hs
            simp only [MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily, dite_eq_left hj, OptionalBoundaryLabels.Construction.adjoinPartialBoundaryLabel, hc,
              Option.map_some, Etale.BoundaryModel.Construction.EtaleBoundaryModel.mixedCoordinateFamily, Mixed.CoordinateBoundaryFamily.Construction.mixedCoordinateBoundaryFamily]
            change ExceptionalIdeal.Construction.blowupChartRatio I a ⟨w j, M.coordinateCenter_boundary_mem C F hF j hj⟩ =
              Blowup.Charts.Construction.blowupChartConstants I a (M.multiplier j) *
                (if h : s.val ∈ C then ExceptionalIdeal.Construction.blowupChartRatio I a (Etale.CoefficientStep.Construction.etaleCoordinateElement C ⟨s.val, h⟩)
                  else Blowup.Charts.Construction.blowupChartConstants I a (M.map (MvPolynomial.X s.val)))
            rw [dite_eq_left hs]
            let x : I := Etale.CoefficientStep.Construction.etaleCoordinateElement (K := k) (S := R) C ⟨s.val, hs⟩
            have he : (⟨w j, M.coordinateCenter_boundary_mem C F hF j hj⟩ : I) =
                ⟨M.multiplier j * x.val, I.mul_mem_left (M.multiplier j) x.property⟩ := by
              apply Subtype.ext
              change w j = M.multiplier j * x.val
              rw [M.equation j, hcoord]
              rfl
            rw [he]
            exact MixedBoundary.Equations.Construction.blowupChartRatio_mul_left I a x (M.multiplier j)
          · have hj : j ∉ F := fun hj => hs (hjF.mp hj)
            simp only [MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily, dite_eq_right hj, OptionalBoundaryLabels.Construction.adjoinPartialBoundaryLabel, hc,
              Option.map_some, Etale.BoundaryModel.Construction.EtaleBoundaryModel.mixedCoordinateFamily, Mixed.CoordinateBoundaryFamily.Construction.mixedCoordinateBoundaryFamily]
            change Blowup.Charts.Construction.blowupChartConstants I a (w j) = Blowup.Charts.Construction.blowupChartConstants I a (M.multiplier j) *
              (if h : s.val ∈ C then ExceptionalIdeal.Construction.blowupChartRatio I a (Etale.CoefficientStep.Construction.etaleCoordinateElement C ⟨s.val, h⟩)
                else Blowup.Charts.Construction.blowupChartConstants I a (M.map (MvPolynomial.X s.val)))
            rw [dite_eq_right hs, M.equation j, hcoord, map_mul]

end

end OAI.AlgebraicGeometry.Resolution.Blowups
