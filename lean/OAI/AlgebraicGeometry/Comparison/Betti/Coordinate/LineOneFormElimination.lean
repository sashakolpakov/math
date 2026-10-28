import OAI.AlgebraicGeometry.Comparison.Betti.PuncturedParametricDbar
import OAI.AlgebraicGeometry.DivisorClass.Chern.OneFormCauchyElimination

/-! # Line One Form Elimination -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.LineOneFormElimination.Dolbeault

noncomputable section

section

/-! A global scalar coefficient primitive on ordinary or punctured
coordinate lines, preserving all previously vanishing coefficients. -/

open _root_.TopologicalSpace _root_.Complex Set
open scoped ContDiff

open OAI.AlgebraicGeometry.DivisorClass.Chern.OneFormCauchyElimination

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedSpace ℂ P] [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]

theorem exists_coordinateLine_oneForm_coefficient_primitive (S : Opens P) (ε : Bool)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (DivisorClass.Chern.OneFormCauchyElimination.complexProductOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε)) 1)
    (ha : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD 1 a = 0) :
    ∃ G : P × ℂ → ℂ, ContDiffOn ℝ ∞ G ((S : Set P) ×ˢ (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε : Set ℂ)) ∧
      (∀ p ∈ S, ∀ w ∈ PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε,
        DivisorClass.Chern.AntiOneFormCoordinates.antilinearScalarDerivative G (p, w) (0, 1) = DivisorClass.Chern.OneFormCauchyElimination.oneFormLastCoefficient a p w) ∧
      (∀ v : P, (∀ q : DivisorClass.Chern.OneFormCauchyElimination.complexProductOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε),
        DivisorClass.Chern.AntiOneFormCoordinates.oneFormLinear (a q) (v, 0) = 0) →
        ∀ q ∈ (S : Set P) ×ˢ (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε : Set ℂ), DivisorClass.Chern.AntiOneFormCoordinates.antilinearScalarDerivative G q (v, 0) = 0) := by
  let g := Function.uncurry (DivisorClass.Chern.OneFormCauchyElimination.oneFormLastCoefficient a)
  have hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε : Set ℂ)) := DivisorClass.Chern.OneFormCauchyElimination.oneFormLastCoefficient_smooth a
  let G := PuncturedParametricDbar.Dolbeault.coordinateLineCauchyCandidate S ε g hg
  have hG : ContDiffOn ℝ ∞ G ((S : Set P) ×ˢ (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε : Set ℂ)) :=
    PuncturedParametricDbar.Dolbeault.coordinateLineCauchyCandidate_smooth S ε g hg
  refine ⟨G, hG, ?_, ?_⟩
  · intro p hp w hw
    have hd : DifferentiableAt ℝ G (p, w) :=
      (hG.contDiffAt ((S.isOpen.prod (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε).isOpen).mem_nhds
        (show (p, w) ∈ (S : Set P) ×ˢ (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε : Set ℂ) from ⟨hp, hw⟩))).differentiableAt (by simp)
    rw [← DivisorClass.Chern.ProductDolbeaultDerivatives.complexDbar_product_slice hd]
    exact PuncturedParametricDbar.Dolbeault.coordinateLineCauchyCandidate_dbar S ε g hg hp hw
  · intro v hv q hq
    apply (DivisorClass.Chern.ProductDolbeaultDerivatives.antilinearScalarDerivative_eq_zero_iff G q (v, 0)).mpr
    have h := PuncturedParametricDbar.Dolbeault.coordinateLineCauchyCandidate_preserves_direction S ε g hg q hq v
      (fun w hw => ?_)
    · simpa only [Prod.smul_mk, smul_eq_mul, mul_zero] using h
    · have hz := DivisorClass.Chern.DolbeaultOneFormCorrection.closed_oneForm_zero_coefficient_derivative a ha (v, 0) hv
        ⟨(q.1, w), ⟨hq.1, hw⟩⟩ (0, 1)
      have hi := (DivisorClass.Chern.ProductDolbeaultDerivatives.antilinearScalarDerivative_eq_zero_iff g (q.1, w) (v, 0)).mp hz
      simpa only [Prod.smul_mk, smul_eq_mul, mul_zero] using hi

end

/-! Global correction of a closed pure one-form on an ordinary or
punctured coordinate-line product, keeping the original domain. -/

open _root_.TopologicalSpace Set
open scoped ContDiff

open OAI.AlgebraicGeometry.DivisorClass.Chern.OneFormCauchyElimination

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedSpace ℂ P] [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]

theorem exists_coordinateLine_oneForm_coefficient_elimination (S : Opens P) (ε : Bool)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (DivisorClass.Chern.OneFormCauchyElimination.complexProductOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε)) 1)
    (ha : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD 1 a = 0) (hpure : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree 0 1 a) :
    ∃ g : P × ℂ → ℂ,
    ∃ hg : ContDiffOn ℝ ∞ g (DivisorClass.Chern.OneFormCauchyElimination.complexProductOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε) : Set (P × ℂ)),
      let b := DivisorClass.Chern.DolbeaultOneFormCorrection.correctDolbeaultOneForm a g hg
      DivisorClass.Chern.DolbeaultOpen.openDolbeaultD 1 b = 0 ∧ DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree 0 1 b ∧
        (∀ q : DivisorClass.Chern.OneFormCauchyElimination.complexProductOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε), DivisorClass.Chern.AntiOneFormCoordinates.oneFormLinear (b q) (0, 1) = 0) ∧
        (∀ v : P, (∀ q : DivisorClass.Chern.OneFormCauchyElimination.complexProductOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε),
          DivisorClass.Chern.AntiOneFormCoordinates.oneFormLinear (a q) (v, 0) = 0) →
          ∀ q : DivisorClass.Chern.OneFormCauchyElimination.complexProductOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε), DivisorClass.Chern.AntiOneFormCoordinates.oneFormLinear (b q) (v, 0) = 0) := by
  obtain ⟨G, hGs, he, hpres⟩ := exists_coordinateLine_oneForm_coefficient_primitive S ε a ha
  have hg : ContDiffOn ℝ ∞ G (DivisorClass.Chern.OneFormCauchyElimination.complexProductOpen S (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen ε) : Set (P × ℂ)) := hGs
  refine ⟨G, hg, DivisorClass.Chern.DolbeaultOneFormCorrection.correctDolbeaultOneForm_closed a ha hg,
    DivisorClass.Chern.DolbeaultOneFormCorrection.correctDolbeaultOneForm_pure a hpure hg, ?_, ?_⟩
  · apply DivisorClass.Chern.DolbeaultOneFormCorrection.correctDolbeaultOneForm_coefficient_zero a hg (0, 1)
    intro q
    refine (he q.val.1 q.property.1 q.val.2 q.property.2).trans ?_
    change DivisorClass.Chern.AntiOneFormCoordinates.oneFormLinear (a.extension q) (0, 1) = DivisorClass.Chern.AntiOneFormCoordinates.oneFormLinear (a q) (0, 1)
    rw [a.extension_apply q]
  · intro v hv q
    rw [DivisorClass.Chern.DolbeaultOneFormCorrection.correctDolbeaultOneForm_coefficient, hv q, hpres v hv q q.property, sub_self]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.LineOneFormElimination.Dolbeault
