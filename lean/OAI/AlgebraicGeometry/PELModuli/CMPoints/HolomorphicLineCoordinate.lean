import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NegativeLine
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-! # Holomorphic Line Coordinate -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicLineCoordinate

noncomputable section

/-! A holomorphic vector in a normalized line determines its ball
coordinate holomorphically wherever the vector is nonzero. -/

open Set

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NegativeLine

theorem last_ne_zero_of_mem_normalized_line (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (v : Geometry.ComplexBall.PrescribedSignsB.Vec)
    (hv : v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z}) (hne : v ≠ 0) : v 2 ≠ 0 := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
  simpa [Geometry.ComplexBall.PrescribedSignsB.lineVector] using (smul_ne_zero_iff.mp hne).1

theorem coordinate_eq_of_mem_normalized_line (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (v : Geometry.ComplexBall.PrescribedSignsB.Vec)
    (hv : v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z}) (hne : v 2 ≠ 0) :
    AbelianModuli.ReferenceFamily.NegativeLine.negativeLineCoordinate v = z := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
  have ha : a ≠ 0 := by simpa [Geometry.ComplexBall.PrescribedSignsB.lineVector] using hne
  ext i
  fin_cases i <;> simp [AbelianModuli.ReferenceFamily.NegativeLine.negativeLineCoordinate, Geometry.ComplexBall.PrescribedSignsB.lineVector, ha]

theorem exists_holomorphic_normalized_line_coordinate
    {S : Type} [NormedAddCommGroup S] [NormedSpace ℂ S]
    (U : Set S) (hU : IsOpen U) (w : S → Geometry.ComplexBall.PrescribedSignsB.Vec)
    (hw : DifferentiableOn ℂ w U) (q₀ : S) (hq₀ : q₀ ∈ U)
    (hcentral : w q₀ ≠ 0)
    (hline : ∀ q ∈ U, ∃ z : Geometry.ComplexBall.PrescribedSignsB.BallChart, w q ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z}) :
    ∃ (O : Set S) (period : S → Geometry.ComplexBall.PrescribedSignsB.BallChart), IsOpen O ∧ q₀ ∈ O ∧ O ⊆ U ∧
      DifferentiableOn ℂ period O ∧ ∀ q ∈ O, ∀ z : Geometry.ComplexBall.PrescribedSignsB.BallChart,
        w q ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z} → period q = z := by
  have hlast : w q₀ 2 ≠ 0 := by
    obtain ⟨z, hz⟩ := hline q₀ hq₀
    exact last_ne_zero_of_mem_normalized_line z (w q₀) hz hcentral
  let O := U ∩ {q | w q 2 ≠ 0}
  have hO : IsOpen O :=
    ((differentiableOn_pi.mp hw 2).continuousOn).isOpen_inter_preimage hU
      isOpen_compl_singleton
  let period := fun q => AbelianModuli.ReferenceFamily.NegativeLine.negativeLineCoordinate (w q)
  refine ⟨O, period, hO, ⟨hq₀, hlast⟩, inter_subset_left, ?_, ?_⟩
  · apply differentiableOn_pi.mpr
    intro i
    change DifferentiableOn ℂ (fun q => w q i.castSucc / w q 2) O
    simp only [div_eq_mul_inv]
    exact ((differentiableOn_pi.mp hw i.castSucc).mono (show O ⊆ U from inter_subset_left)).mul
      (((differentiableOn_pi.mp hw 2).mono (show O ⊆ U from inter_subset_left)).inv
        (fun q hq => hq.2))
  · intro q hq z hz
    exact coordinate_eq_of_mem_normalized_line z (w q) hz hq.2

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicLineCoordinate
