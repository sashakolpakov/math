import OAI.AlgebraicGeometry.Comparison.Betti.PuncturedCauchy
import OAI.AlgebraicGeometry.Comparison.Betti.ParameterLinePullbackDerivative

/-! # Punctured Directions -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.PuncturedDirections.Dolbeault

noncomputable section

/-! The two whole-line input pieces preserve the holomorphic parameter
directions of the original family on the punctured line. -/

open _root_.TopologicalSpace Set _root_.Complex
open scoped ContDiff _root_.Topology

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

theorem puncturedCauchyOuterInput_preserves_direction (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ)))
    (q : P × ℂ) (hq : q.1 ∈ S) (v : P)
    (hv : ∀ w : ℂ, w ≠ 0 → fderiv ℝ g (q.1, w) (I • v, 0) = I • fderiv ℝ g (q.1, w) (v, 0)) :
    fderiv ℝ (PuncturedCauchy.Dolbeault.puncturedCauchyOuterInput g) q (I • v, 0) =
      I • fderiv ℝ (PuncturedCauchy.Dolbeault.puncturedCauchyOuterInput g) q (v, 0) := by
  by_cases hz : q.2 = 0
  · have hq0 : q = (q.1, 0) := Prod.ext rfl hz
    rw [hq0, PuncturedCauchy.Dolbeault.puncturedCauchyOuterInput_fderiv_zero]
    simp only [zero_apply, smul_zero]
  · have hf := ((PuncturedCauchy.Dolbeault.puncturedCauchyOuterInput_smooth S hg).contDiffAt
      ((S.isOpen.prod isOpen_univ).mem_nhds (show q ∈ (S : Set P) ×ˢ univ from ⟨hq, mem_univ _⟩))).differentiableAt (by simp)
    have hgp := (hg.contDiffAt ((S.isOpen.prod PuncturedCauchy.Dolbeault.puncturedComplexOpen.isOpen).mem_nhds ⟨hq, hz⟩)).differentiableAt (by simp)
    exact ParameterLinePullbackDerivative.Dolbeault.parameter_direction_line_weight (a := fun z => 1 - (PuncturedCauchy.Dolbeault.puncturedCauchyBump z : ℂ))
      (φ := id) hf hgp v (hv q.2 hz)

theorem puncturedCauchyInnerInput_preserves_direction (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ)))
    (q : P × ℂ) (hq : q.1 ∈ S) (v : P)
    (hv : ∀ w : ℂ, w ≠ 0 → fderiv ℝ g (q.1, w) (I • v, 0) = I • fderiv ℝ g (q.1, w) (v, 0)) :
    fderiv ℝ (PuncturedCauchy.Dolbeault.puncturedCauchyInnerInput g) q (I • v, 0) =
      I • fderiv ℝ (PuncturedCauchy.Dolbeault.puncturedCauchyInnerInput g) q (v, 0) := by
  by_cases hz : q.2 = 0
  · have hq0 : q = (q.1, 0) := Prod.ext rfl hz
    rw [hq0, PuncturedCauchy.Dolbeault.puncturedCauchyInnerInput_fderiv_zero]
    simp only [zero_apply, smul_zero]
  · let b : P × ℂ → F := fun y => (PuncturedCauchy.Dolbeault.puncturedCauchyBump y.2 : ℂ) • g y
    have hgp := hg.contDiffAt ((S.isOpen.prod PuncturedCauchy.Dolbeault.puncturedComplexOpen.isOpen).mem_nhds
      (show (q.1, q.2⁻¹) ∈ (S : Set P) ×ˢ (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ) from ⟨hq, inv_ne_zero hz⟩))
    have hχ : ContDiffAt ℝ ∞ (fun y : P × ℂ => (PuncturedCauchy.Dolbeault.puncturedCauchyBump y.2 : ℂ)) (q.1, q.2⁻¹) :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp _ (PuncturedCauchy.Dolbeault.puncturedCauchyBump.contDiff.contDiffAt.comp _ contDiffAt_snd)
    have hb : DifferentiableAt ℝ b (q.1, q.2⁻¹) := (hχ.smul hgp).differentiableAt (by simp)
    have hdir : fderiv ℝ b (q.1, q.2⁻¹) (I • v, 0) = I • fderiv ℝ b (q.1, q.2⁻¹) (v, 0) :=
      ParameterLinePullbackDerivative.Dolbeault.parameter_direction_line_weight (a := fun z => (PuncturedCauchy.Dolbeault.puncturedCauchyBump z : ℂ)) (φ := id)
        hb (hgp.differentiableAt (by simp)) v (hv q.2⁻¹ (inv_ne_zero hz))
    have hf := ((PuncturedCauchy.Dolbeault.puncturedCauchyInnerInput_smooth S hg).contDiffAt
      ((S.isOpen.prod isOpen_univ).mem_nhds (show q ∈ (S : Set P) ×ˢ univ from ⟨hq, mem_univ _⟩))).differentiableAt (by simp)
    exact ParameterLinePullbackDerivative.Dolbeault.parameter_direction_line_weight (g := b) (a := PuncturedCauchy.Dolbeault.complexInversionJacobian)
      (φ := Inv.inv) hf hb v hdir

end

end OAI.AlgebraicGeometry.Comparison.Betti.PuncturedDirections.Dolbeault
