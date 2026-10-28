import OAI.AlgebraicGeometry.Comparison.Betti.AnnularCauchyFormula
import OAI.AlgebraicGeometry.Comparison.Betti.InvertedCauchyCircle

/-! # Laurent Splitting -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.LaurentSplitting.Dolbeault

noncomputable section

/-! Actual global Laurent splitting on the punctured line into an entire
part and an entire function of the inverse coordinate, normalized at infinity. -/

open _root_.Complex Set _root_.Metric Filter
open scoped _root_.Topology

def negativeLaurentPart (f : ℂ → ℂ) (u : ℂ) : ℂ := by
  classical
  exact if u = 0 then 0 else f u⁻¹ - AnnularCauchyFormula.Dolbeault.positiveLaurentPart f u⁻¹

theorem negativeLaurentPart_zero (f : ℂ → ℂ) : negativeLaurentPart f 0 = 0 := by
  simp [negativeLaurentPart]

theorem negativeLaurentPart_eq_inverted {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ)) {u : ℂ} (hu : ‖u‖ < 1) :
    negativeLaurentPart f u = InvertedCauchyCircle.Dolbeault.invertedUnitCauchyTransform f u := by
  by_cases hu0 : u = 0
  · subst u
    rw [negativeLaurentPart_zero, InvertedCauchyCircle.Dolbeault.invertedUnitCauchyTransform_zero]
  · have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    have hinv : 1 < ‖u⁻¹‖ := by
      rw [norm_inv, ← one_div]
      exact (lt_div_iff₀ hpos).mpr (by simpa only [one_mul] using hu)
    have h := AnnularCauchyFormula.Dolbeault.annularCauchyFormula hf (by norm_num : 0 < (1 : ℝ)) hinv (lt_add_one ‖u⁻¹‖)
    change AnnularCauchyFormula.Dolbeault.positiveLaurentPart f u⁻¹ - CauchyAnnulusInvariance.Dolbeault.cauchyCircleTransform f 1 u⁻¹ = f u⁻¹ at h
    rw [negativeLaurentPart, ite_eq_right hu0, InvertedCauchyCircle.Dolbeault.invertedUnitCauchyTransform_eq f hu0]
    linear_combination -h

theorem negativeLaurentPart_differentiableAt_ne_zero {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ)) {u : ℂ} (hu : u ≠ 0) :
    DifferentiableAt ℂ (negativeLaurentPart f) u := by
  have hInv : DifferentiableAt ℂ (fun v : ℂ => v⁻¹) u := differentiableAt_inv hu
  have hf' := hf.differentiableAt (PuncturedCauchy.Dolbeault.puncturedComplexOpen.isOpen.mem_nhds (inv_ne_zero hu))
  have hg : DifferentiableAt ℂ (fun v => f v⁻¹ - AnnularCauchyFormula.Dolbeault.positiveLaurentPart f v⁻¹) u :=
    (hf'.comp u hInv).sub ((AnnularCauchyFormula.Dolbeault.positiveLaurentPart_entire hf u⁻¹).comp u hInv)
  apply hg.congr_of_eventuallyEq
  filter_upwards [isOpen_ne.mem_nhds hu] with v hv
  simp only [negativeLaurentPart, ite_eq_right hv]

theorem negativeLaurentPart_entire {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ)) :
    Differentiable ℂ (negativeLaurentPart f) := by
  intro u
  by_cases hu : u = 0
  · subst u
    have hd := InvertedCauchyCircle.Dolbeault.invertedUnitCauchyTransform_holomorphic
      (AnnularCauchyFormula.Dolbeault.punctured_holomorphic_continuousOn_sphere hf (by norm_num : 0 < (1 : ℝ)))
      (u := 0) (by simp)
    apply hd.congr_of_eventuallyEq
    filter_upwards [ball_mem_nhds (0 : ℂ) (by norm_num : 0 < (1 : ℝ))] with v hv
    exact negativeLaurentPart_eq_inverted hf (by simpa only [mem_ball, dist_zero_right] using hv)
  · exact negativeLaurentPart_differentiableAt_ne_zero hf hu

theorem holomorphicLaurentSplitting_identity (f : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    AnnularCauchyFormula.Dolbeault.positiveLaurentPart f z + negativeLaurentPart f z⁻¹ = f z := by
  simp only [negativeLaurentPart, ite_eq_right (inv_ne_zero hz), inv_inv]
  ring

theorem exists_holomorphicLaurentSplitting {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (PuncturedCauchy.Dolbeault.puncturedComplexOpen : Set ℂ)) :
    ∃ a b : ℂ → ℂ, Differentiable ℂ a ∧ Differentiable ℂ b ∧ b 0 = 0 ∧
      ∀ z ≠ 0, f z = a z + b z⁻¹ :=
  ⟨AnnularCauchyFormula.Dolbeault.positiveLaurentPart f, negativeLaurentPart f, AnnularCauchyFormula.Dolbeault.positiveLaurentPart_entire hf,
    negativeLaurentPart_entire hf, negativeLaurentPart_zero f,
    fun _ hz => (holomorphicLaurentSplitting_identity f hz).symm⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.LaurentSplitting.Dolbeault
