import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic

noncomputable section
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def liftFirstJet (ℓ : E →L[ℝ] ℝ) (s : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (x : E) : E →L[ℝ] ℝ :=
  (ℓ x * s x) • ℓ + ((ℓ x) ^ 2 / 2) • D x

def liftSecondJet (ℓ : E →L[ℝ] ℝ) (s : E → ℝ) (D : E → E →L[ℝ] ℝ)
    (DD : E → E →L[ℝ] E →L[ℝ] ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (s x) • ℓ.smulRight ℓ + (ℓ x) • ((D x).smulRight ℓ + ℓ.smulRight (D x)) +
    ((ℓ x) ^ 2 / 2) • DD x

theorem hasFDerivAt_halfSquare (ℓ : E →L[ℝ] ℝ) (x : E) :
    HasFDerivAt (fun y ↦ (ℓ y) ^ 2 / 2) ((ℓ x) • ℓ) x := by
  have h : HasDerivAt (fun t : ℝ ↦ t ^ 2 / 2) (ℓ x) (ℓ x) := by
    convert! (hasDerivAt_pow 2 (ℓ x)).div_const 2 using 1 ; norm_num
  exact h.comp_hasFDerivAt x ℓ.hasFDerivAt

theorem hasFDerivAt_quadraticLift (ℓ : E →L[ℝ] ℝ)
    (s : E → ℝ) (D : E → E →L[ℝ] ℝ) (x : E)
    (hs : HasFDerivAt s (D x) x) :
    HasFDerivAt (fun y ↦ (ℓ y) ^ 2 / 2 * s y) (liftFirstJet ℓ s D x) x := by
  convert! (hasFDerivAt_halfSquare ℓ x).mul hs using 1
  ext v
  simp only [liftFirstJet, add_apply, smul_apply, smul_eq_mul]
  ring

theorem hasFDerivAt_liftFirstJet (ℓ : E →L[ℝ] ℝ)
    (s : E → ℝ) (D : E → E →L[ℝ] ℝ) (DD : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x : E) (hs : HasFDerivAt s (D x) x) (hD : HasFDerivAt D (DD x) x) :
    HasFDerivAt (liftFirstJet ℓ s D) (liftSecondJet ℓ s D DD x) x := by
  have h1 := (ℓ.hasFDerivAt.mul hs).smul_const ℓ
  have h2 := (hasFDerivAt_halfSquare ℓ x).smul hD
  convert! h1.add h2 using 1
  ext v w
  simp only [liftSecondJet, add_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.smulRight_apply]
  ring

@[simp] theorem liftFirstJet_boundary (ℓ : E →L[ℝ] ℝ)
    (s : E → ℝ) (D : E → E →L[ℝ] ℝ) {x : E} (hx : ℓ x = 0) :
    liftFirstJet ℓ s D x = 0 := by simp [liftFirstJet, hx]

@[simp] theorem liftSecondJet_boundary (ℓ : E →L[ℝ] ℝ)
    (s : E → ℝ) (D : E → E →L[ℝ] ℝ) (DD : E → E →L[ℝ] E →L[ℝ] ℝ)
    {x : E} (hx : ℓ x = 0) :
    liftSecondJet ℓ s D DD x = (s x) • ℓ.smulRight ℓ := by
  ext v w
  simp [liftSecondJet, hx]

end OAI.Analysis.PDE.Schauder
