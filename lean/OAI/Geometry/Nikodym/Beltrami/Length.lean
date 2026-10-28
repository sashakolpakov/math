import OAI.Geometry.Nikodym.Beltrami.Geodesic

noncomputable section
namespace OAI.Geometry.Nikodym

open Set _root_.MeasureTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Riemannian speed for the actual model metric. -/
def beltramiSpeed (κ : ℝ) (x v : E) : ℝ := Real.sqrt (beltramiMetric κ x v v)

theorem beltramiSpeed_small_bounds {κ : ℝ} {x : E}
    (hx : |κ| * ‖x‖^2 ≤ 1/2) (v : E) :
    (1/4) * ‖v‖ ≤ beltramiSpeed κ x v ∧ beltramiSpeed κ x v ≤ 3 * ‖v‖ := by
  obtain ⟨hl,hu⟩ := beltramiMetric_small_bounds hx v
  have hg : 0 ≤ beltramiMetric κ x v v := le_trans (by positivity) hl
  have hs := Real.sq_sqrt hg
  have hn := Real.sqrt_nonneg (beltramiMetric κ x v v)
  have hv := norm_nonneg v
  unfold beltramiSpeed
  constructor <;> nlinarith

/-- Extended Riemannian length. An explicit velocity is convenient for
curves whose differentiability is asserted only on the parameter interval. -/
def beltramiPathLength (κ : ℝ) (γ v : ℝ → E) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Icc a b, ENNReal.ofReal (beltramiSpeed κ (γ t) (v t))

theorem beltramiPathLength_small_bounds {κ a b : ℝ} {γ v : ℝ → E}
    (hsmall : ∀ t ∈ Icc a b, |κ| * ‖γ t‖^2 ≤ 1/2) :
    (1/4 : ℝ≥0∞) * (∫⁻ t in Icc a b, ‖v t‖ₑ) ≤ beltramiPathLength κ γ v a b ∧
      beltramiPathLength κ γ v a b ≤ 3 * (∫⁻ t in Icc a b, ‖v t‖ₑ) := by
  constructor
  · rw [← lintegral_const_mul' _ _ (by norm_num : (1/4 : ℝ≥0∞) ≠ ⊤)]
    apply setLIntegral_mono' measurableSet_Icc
    intro t ht
    have h := ENNReal.ofReal_le_ofReal (beltramiSpeed_small_bounds (hsmall t ht) (v t)).1
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/4),
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4),ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat,ofReal_norm] using h
  · rw [← lintegral_const_mul' _ _ (by norm_num : (3 : ℝ≥0∞) ≠ ⊤)]
    apply setLIntegral_mono' measurableSet_Icc
    intro t ht
    have h := ENNReal.ofReal_le_ofReal (beltramiSpeed_small_bounds (hsmall t ht) (v t)).2
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
      ENNReal.ofReal_ofNat,ofReal_norm] using h

end OAI.Geometry.Nikodym
