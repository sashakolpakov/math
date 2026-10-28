import OAI.Analysis.Calculus.Current.Physical.Jacobian
import OAI.Analysis.Calculus.Current.Physical.Parameters
import Mathlib

/-! Exact change of variables from the moving physical fiber to a fixed ball. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current

def openFiberParameterBall (d : ℕ) : Set (Option (Fin d) → ℂ) :=
  {u | (∑ i, ‖u i‖ ^ 2) < (1 / 100 : ℝ)}

theorem isOpen_openFiberParameterBall (d : ℕ) : IsOpen (openFiberParameterBall d) :=
  isOpen_lt (by fun_prop) continuous_const

theorem openFiberParameterBall_subset (d : ℕ) :
    openFiberParameterBall d ⊆ OAI.Analysis.Calculus.Current.fiberParameterBall d := by
  intro u hu
  change (∑ i, ‖u i‖ ^ 2) ≤ (1 / 100 : ℝ)
  exact (show (∑ i, ‖u i‖ ^ 2) < (1 / 100 : ℝ) from hu).le

theorem physical_defining_coordinates {d : ℕ} (a : ℝ) (τ : ℂ)
    (q : Option (Fin d) → ℂ) :
    OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q =
      100 * (∑ i, ‖OAI.Analysis.Calculus.Current.physicalFiberCoordinates a τ q i‖ ^ 2) - 1 := by
  unfold OAI.Analysis.Calculus.Current.physicalFiberDefining OAI.Analysis.Calculus.Current.fiberDefining
  simp only [Fintype.sum_option, OAI.Analysis.Calculus.Current.fiberMap, OAI.Analysis.Calculus.Current.physicalFiberCoordinates]
  simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, mul_pow, div_pow]
  norm_num
  rw [← Finset.sum_div]
  ring

theorem physicalFiberInverse_injOn_parameter_ball {d : ℕ} (a : ℝ) (τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) :
    InjOn (OAI.Analysis.Calculus.Current.physicalFiberInverse a τ) (OAI.Analysis.Calculus.Current.fiberParameterBall d) := by
  intro u hu v hv huv
  have hu' := OAI.Analysis.Calculus.Current.physicalCoordinates_right_inverse a τ u ha.ne'
    (OAI.Analysis.Calculus.Current.fiberParameterBall_numerator a τ ha ht hu) (OAI.Analysis.Calculus.Current.fiberParameterBall_denominator hu)
  have hv' := OAI.Analysis.Calculus.Current.physicalCoordinates_right_inverse a τ v ha.ne'
    (OAI.Analysis.Calculus.Current.fiberParameterBall_numerator a τ ha ht hv) (OAI.Analysis.Calculus.Current.fiberParameterBall_denominator hv)
  rw [← hu', ← hv', huv]

theorem physicalFiberInverse_image_open_ball {d : ℕ} (a : ℝ) (τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) :
    OAI.Analysis.Calculus.Current.physicalFiberInverse a τ '' openFiberParameterBall d =
      {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0} := by
  ext q
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' := openFiberParameterBall_subset d hu
    rw [Set.mem_ofPred_eq, OAI.Analysis.Calculus.Current.physical_inverse_defining a τ u ha.ne'
      (OAI.Analysis.Calculus.Current.fiberParameterBall_numerator a τ ha ht hu') (OAI.Analysis.Calculus.Current.fiberParameterBall_denominator hu')]
    change (∑ i, ‖u i‖ ^ 2) < (1 / 100 : ℝ) at hu
    linarith
  · intro hq
    have hreg := OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a τ ha ht
      (show OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 1 from hq.le.trans (by norm_num))
    refine ⟨OAI.Analysis.Calculus.Current.physicalFiberCoordinates a τ q, ?_,
      OAI.Analysis.Calculus.Current.physicalCoordinates_left_inverse a τ q ha.ne' hreg.1 hreg.2⟩
    change (∑ i, ‖OAI.Analysis.Calculus.Current.physicalFiberCoordinates a τ q i‖ ^ 2) < (1 / 100 : ℝ)
    have hh := physical_defining_coordinates a τ q
    change OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0 at hq
    linarith

theorem physicalFiberInverse_image_closed_ball {d : ℕ} (a : ℝ) (τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) :
    OAI.Analysis.Calculus.Current.physicalFiberInverse a τ '' OAI.Analysis.Calculus.Current.fiberParameterBall d =
      {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0} := by
  ext q
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [Set.mem_ofPred_eq, OAI.Analysis.Calculus.Current.physical_inverse_defining a τ u ha.ne'
      (OAI.Analysis.Calculus.Current.fiberParameterBall_numerator a τ ha ht hu) (OAI.Analysis.Calculus.Current.fiberParameterBall_denominator hu)]
    change (∑ i, ‖u i‖ ^ 2) ≤ (1 / 100 : ℝ) at hu
    linarith
  · intro hq
    have hreg := OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a τ ha ht
      (show OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 1 from hq.trans (by norm_num))
    refine ⟨OAI.Analysis.Calculus.Current.physicalFiberCoordinates a τ q, ?_,
      OAI.Analysis.Calculus.Current.physicalCoordinates_left_inverse a τ q ha.ne' hreg.1 hreg.2⟩
    change (∑ i, ‖OAI.Analysis.Calculus.Current.physicalFiberCoordinates a τ q i‖ ^ 2) ≤ (1 / 100 : ℝ)
    have hh := physical_defining_coordinates a τ q
    change OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0 at hq
    linarith

theorem physical_fiber_integral_change {d : ℕ} (a : ℝ) (τ : ℂ)
    (ha : 0 < a) (ht : a ≤ ‖τ‖) (f : (Option (Fin d) → ℂ) → ℝ) :
    (∫ q in {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0}, f q) =
      ∫ u in openFiberParameterBall d,
        |OAI.Analysis.Calculus.Current.physicalInverseJacobian a τ u| * f (OAI.Analysis.Calculus.Current.physicalFiberInverse a τ u) := by
  rw [← physicalFiberInverse_image_open_ball a τ ha ht]
  have hd : ∀ u ∈ openFiberParameterBall d,
      HasFDerivWithinAt (OAI.Analysis.Calculus.Current.physicalFiberInverse a τ)
        (fderiv ℝ (OAI.Analysis.Calculus.Current.physicalFiberInverse a τ) u) (openFiberParameterBall d) u := by
    intro u hu
    have hh := (OAI.Analysis.Calculus.Current.contDiffAt_physicalFiberInverse a τ u
      (OAI.Analysis.Calculus.Current.fiberParameterBall_denominator (openFiberParameterBall_subset d hu))).restrict_scalars ℝ
    exact (hh.differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  simpa only [OAI.Analysis.Calculus.Current.physicalInverseJacobian, smul_eq_mul] using
    (integral_image_eq_integral_abs_det_fderiv_smul volume
      (isOpen_openFiberParameterBall d).measurableSet hd
      ((physicalFiberInverse_injOn_parameter_ball a τ ha ht).mono (openFiberParameterBall_subset d)) f)

end OAI.Analysis.PDE.Green
