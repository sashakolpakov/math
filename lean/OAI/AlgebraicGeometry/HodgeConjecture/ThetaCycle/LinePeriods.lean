import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.LineGraphs
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SquareRoot

/-! # Line Periods -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.LinePeriods.CM

noncomputable section

/-! Construction of the full concrete HeckeCycles line-period object, including
its actual rational coordinates, prescribed graph, and holomorphic half determinant. -/

open scoped Classical _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}
  (d : Fin 2 → Gal(K/ℚ) → Bool)
  (P : Lagrangians.CM.LagrangianPair K B places (fun i j => d i (places.representative j)))
  (i : Fin 2) (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
  (ha : C.a = P.a i) (hδ : C.delta = P.delta)

def extendedLineSiegel (z : HeckeCycles.GeometricSource.CM.BallChart) : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (HeckeCycles.GeometricSource.CM.Positions K places) :=
  if hz : z ∈ B.domain then SiegelFrames.CM.lineSiegelAt K d P i C ha hδ ⟨z, hz⟩
  else SiegelFrames.CM.lineSiegelAt K d P i C ha hδ ⟨0, by
    change Complex.normSq 0 + Complex.normSq 0 < -(B.b : ℂ).re
    simpa only [Complex.normSq_zero, zero_add] using neg_pos.mpr B.negative⟩

theorem extended_line_siegel_eq (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    extendedLineSiegel K d P i C ha hδ z = SiegelFrames.CM.lineSiegelAt K d P i C ha hδ ⟨z, hz⟩ := by
  simp only [extendedLineSiegel, dite_eq_left hz]

theorem extended_line_siegel_holomorphic :
    DifferentiableOn ℂ (fun z => (extendedLineSiegel K d P i C ha hδ z).matrix) B.domain := by
  have hm := SiegelFrames.CM.period_frames_holomorphic K C (d i)
  have hinv := MatrixCalculus.CM.matrix_inverse_holomorphic _ hm.2 (LineGraphs.CM.lower_period_det_ne_zero K d P i C ha hδ)
  exact (MatrixCalculus.CM.matrix_product_holomorphic _ _ hm.1 hinv).congr (fun z hz => by
    rw [extended_line_siegel_eq K d P i C ha hδ z hz]
    rfl)

include ha hδ in
theorem exists_line_period_for_coordinates :
    ∃ L : HeckeCycles.GeometricSource.CM.LinePeriod K B places (d i), L.coordinates = C := by
  let g : HeckeCycles.GeometricSource.CM.BallChart → ℂ := fun z => ((SiegelFrames.CM.lowerPeriodFrame K C (d i) z)⁻¹).det
  have hg : DifferentiableOn ℂ g B.domain :=
    MatrixCalculus.CM.matrix_determinant_holomorphic _ (MatrixCalculus.CM.matrix_inverse_holomorphic _
      (SiegelFrames.CM.period_frames_holomorphic K C (d i)).2 (LineGraphs.CM.lower_period_det_ne_zero K d P i C ha hδ))
  have hgn : ∀ z ∈ B.domain, g z ≠ 0 := by
    intro z hz
    change ((SiegelFrames.CM.lowerPeriodFrame K C (d i) z)⁻¹).det ≠ 0
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact inv_ne_zero (LineGraphs.CM.lower_period_det_ne_zero K d P i C ha hδ z hz)
  obtain ⟨h, hh, hs⟩ := SquareRoot.CM.ball_holomorphic_square_root B g hg hgn
  refine ⟨{
    coordinates := C
    period := extendedLineSiegel K d P i C ha hδ
    holomorphic := extended_line_siegel_holomorphic K d P i C ha hδ
    graph_prescribed := ?_
    halfDet := h
    halfDet_holomorphic := hh
    halfDet_square := ?_
  }, rfl⟩
  · intro z hz w
    rw [extended_line_siegel_eq K d P i C ha hδ z hz]
    exact LineGraphs.CM.line_siegel_prescribed K d P i C ha hδ ⟨z, hz⟩ w
  · intro z hz
    rw [extended_line_siegel_eq K d P i C ha hδ z hz,
      LineGraphs.CM.adapted_graph_det K d P i C ha hδ]
    exact hs z hz

omit C ha hδ in
theorem exists_line_period :
    ∃ L : HeckeCycles.GeometricSource.CM.LinePeriod K B places (d i),
      L.coordinates.a = P.a i ∧ L.coordinates.delta = P.delta := by
  obtain ⟨C, ha, hδ⟩ := Symplectic.CM.exists_symplectic_coordinates K B places (P.a i) P.delta
    (P.a_sign i).1 (P.a_sign i).2.1 P.delta_ne_zero P.delta_imaginary
  obtain ⟨L, hL⟩ := exists_line_period_for_coordinates K d P i C ha hδ
  exact ⟨L, by rw [hL]; exact ha, by rw [hL]; exact hδ⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.LinePeriods.CM
