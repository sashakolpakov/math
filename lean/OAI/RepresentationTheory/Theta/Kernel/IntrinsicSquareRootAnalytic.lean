import Mathlib

/-! # Intrinsic Square Root Analytic -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicSquareRootAnalytic.Intrinsic

noncomputable section

/-! A continuous nonzero square root of an ambient analytic function
is locally analytic. The branch is identified by its actual value. -/

open scoped Classical _root_.Topology ContDiff

open Filter
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem contDiffAt_of_square {f D : V → ℂ} {x : V}
    (hf : ContinuousAt f x) (hne : f x ≠ 0)
    (hsq : ∀ᶠ y in 𝓝 x, f y ^ 2 = D y) (hD : ContDiffAt ℂ ⊤ D x) :
    ContDiffAt ℂ ⊤ f x := by
  let a := f x
  have ha : a ≠ 0 := hne
  have hsq₀ : f x ^ 2 = D x := hsq.self_of_nhds
  have hx : D x / a ^ 2 = 1 := by
    rw [← hsq₀]
    exact div_self (pow_ne_zero 2 ha)
  let g : V → ℂ := fun y => a * Complex.sqrt (D y / a ^ 2)
  have hr : ContDiffAt ℂ ⊤ Complex.sqrt (D x / a ^ 2) :=
    (Complex.differentiableOn_sqrt.contDiffOn Complex.isOpen_slitPlane).contDiffAt
      (Complex.isOpen_slitPlane.mem_nhds (by rw [hx]; exact Complex.one_mem_slitPlane))
  have hrcomp : ContDiffAt ℂ ⊤ (fun y => Complex.sqrt (D y / a ^ 2)) x :=
    ContDiffAt.comp (f := fun y => D y / a ^ 2) (g := Complex.sqrt) x hr (hD.div_const (a ^ 2))
  have hg : ContDiffAt ℂ ⊤ g x := contDiffAt_const.mul hrcomp
  have hg₀ : g x = f x := by
    change a * Complex.sqrt (D x / a ^ 2) = a
    rw [hx,Complex.sqrt_one,mul_one]
  have hgsq (y : V) : g y ^ 2 = D y := by
    change (a * Complex.sqrt (D y / a ^ 2)) ^ 2 = D y
    rw [mul_pow,show (Complex.sqrt (D y / a ^ 2)) ^ 2 = D y / a ^ 2 from Complex.cpow_ofNat_inv_pow _ 2]
    field_simp
  have hsum : f x + g x ≠ 0 := by
    rw [hg₀,← two_mul]
    exact mul_ne_zero (by norm_num) hne
  apply hg.congr_of_eventuallyEq
  filter_upwards [hsq,(hf.add hg.continuousAt).eventually_ne hsum] with y hy hny
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans (hgsq y).symm) with h | h
  · exact h
  · exact False.elim (hny (by
      change f y + g y = 0
      rw [h]
      exact neg_add_cancel _))

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicSquareRootAnalytic.Intrinsic
