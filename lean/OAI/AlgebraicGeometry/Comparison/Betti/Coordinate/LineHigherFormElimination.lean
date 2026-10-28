import OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.LineContractionPrimitive
import OAI.AlgebraicGeometry.Comparison.Betti.Open.DolbeaultCorrection

/-! # Line Higher Form Elimination -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.LineHigherFormElimination.Dolbeault

noncomputable section

/-! Global elimination of the last antiholomorphic coefficient of an
actual higher-degree closed pure form on an ordinary or punctured line product. -/

open _root_.TopologicalSpace Set
open scoped ContDiff

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedSpace ℂ P] [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]

theorem exists_coordinateLine_higherForm_coefficient_elimination (S : Opens P) (ε : Bool)
    (n p q : ℕ) (hn : n + 1 = p + q)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ContractionCauchyPrimitive.Dolbeault.productOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε)) (n + 2))
    (ha : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 2) a = 0)
    (hpure : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) a) :
    ∃ u : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ContractionCauchyPrimitive.Dolbeault.productOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε)) (n + 1), DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p q u ∧
      let b := Open.DolbeaultCorrection.correctOpenDolbeaultForm (n + 1) a u
      DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 2) b = 0 ∧ DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) b ∧
        Open.AntiholomorphicContraction.Dolbeault.openAntiContraction (ContractionCauchyPrimitive.Dolbeault.productOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε)) (n + 1) (0, 1) b = 0 ∧
        (∀ v : P, Open.AntiholomorphicContraction.Dolbeault.openAntiContraction (ContractionCauchyPrimitive.Dolbeault.productOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε)) (n + 1) (v, 0) a = 0 →
          Open.AntiholomorphicContraction.Dolbeault.openAntiContraction (ContractionCauchyPrimitive.Dolbeault.productOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε)) (n + 1) (v, 0) b = 0) := by
  let G := LineContractionPrimitive.Dolbeault.coordinateLineContractionPrimitive S ε (n + 1) a
  have hG : ContDiffOn ℝ ∞ G (ContractionCauchyPrimitive.Dolbeault.productOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε) : Set (P × ℂ)) :=
    (LineContractionPrimitive.Dolbeault.coordinateLineContractionPrimitive_smooth S ε (n + 1) a)
  let u := Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ofRaw (ContractionCauchyPrimitive.Dolbeault.productOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε)) G hG
  have hup : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p q u := by
    intro y z v
    exact LineContractionPrimitive.Dolbeault.coordinateLineContractionPrimitive_pure S ε (n + 1) p q hn a hpure y y.property.1 z v
  have hulast : Open.AntiholomorphicContraction.Dolbeault.openAntiContraction (ContractionCauchyPrimitive.Dolbeault.productOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε)) n (0, 1) u = 0 := by
    apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
    intro y
    rw [Open.AntiholomorphicContraction.Dolbeault.openAntiContraction_apply]
    exact LineContractionPrimitive.Dolbeault.coordinateLineContractionPrimitive_last_kernel S ε n a y y.property.1
  refine ⟨u, hup, Open.DolbeaultCorrection.correctOpenDolbeaultForm_closed (n + 1) p q hn a ha u hup,
    Open.DolbeaultCorrection.correctOpenDolbeaultForm_pure (n + 1) p q hn a hpure u hup, ?_, ?_⟩
  · apply Open.DolbeaultCorrection.correctOpenDolbeaultForm_contraction_zero n (0, 1) a u hulast
    intro y
    rw [show u = Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ofRaw (ContractionCauchyPrimitive.Dolbeault.productOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε)) G hG from rfl,
      Closed.FormAntiholomorphicDirections.Dolbeault.vectorAntiDerivative_ofRaw]
    have he := LineContractionPrimitive.Dolbeault.coordinateLineContractionPrimitive_last_derivative S ε (n + 1) a y y.property
    refine he.trans ?_
    change AntiholomorphicContraction.Dolbeault.antiContraction (n + 1) (0, 1) (a.extension y) = AntiholomorphicContraction.Dolbeault.antiContraction (n + 1) (0, 1) (a y)
    rw [a.extension_apply y]
  · intro v hv
    have huv : Open.AntiholomorphicContraction.Dolbeault.openAntiContraction (ContractionCauchyPrimitive.Dolbeault.productOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε)) n (v, 0) u = 0 := by
      apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
      intro y
      rw [Open.AntiholomorphicContraction.Dolbeault.openAntiContraction_apply]
      exact LineContractionPrimitive.Dolbeault.coordinateLineContractionPrimitive_kernel S ε n a (v, 0) hv y y.property.1
    apply Open.DolbeaultCorrection.correctOpenDolbeaultForm_contraction_zero n (v, 0) a u huv
    intro y
    rw [show u = Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ofRaw (ContractionCauchyPrimitive.Dolbeault.productOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε)) G hG from rfl,
      Closed.FormAntiholomorphicDirections.Dolbeault.vectorAntiDerivative_ofRaw]
    have he := LineContractionPrimitive.Dolbeault.coordinateLineContractionPrimitive_preserves_direction S ε (n + 1) a ha v hv y y.property
    refine he.trans ?_
    have hz := congrArg (fun b : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ContractionCauchyPrimitive.Dolbeault.productOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε)) (n + 1) => b y) hv
    simpa only [Open.AntiholomorphicContraction.Dolbeault.openAntiContraction_apply, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.zero_apply] using hz.symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.LineHigherFormElimination.Dolbeault
