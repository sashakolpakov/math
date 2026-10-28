import OAI.Analysis.PDE.Weak.Elliptic.Divergence
import OAI.Analysis.PDE.Weak.Boundary.H1WeakGradient
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem H1Zero.gradient_component_eq_of_value_eq
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω) {p : H1Pair m}
    (hp : p ∈ H1Zero univ) (u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hu : ContDiff ℝ 1 u)
    (heq : ∀ᵐ x ∂volume, x ∈ Ω → p.1 x = u x) (j : Fin (m + 1)) :
    ∀ᵐ x ∂volume, x ∈ Ω → p.2 x j = fderiv ℝ u x (Pi.single j 1) := by
  let du := fun x ↦ fderiv ℝ u x (Pi.single j 1)
  have hdu : Continuous du := OAI.Analysis.PDE.Green.continuous_directional hu _
  have hpj : MemLp (fun x ↦ p.2 x j) 2 volume := memLp_cell_component (Lp.memLp p.2) j
  have hlocal : LocallyIntegrableOn (fun x ↦ p.2 x j - du x) Ω volume :=
    ((hpj.locallyIntegrable (by norm_num)).locallyIntegrableOn Ω).sub
      (hdu.locallyIntegrable.locallyIntegrableOn Ω)
  have hz := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocal ?_
  · filter_upwards [hz] with x hx
    exact fun hxs ↦ sub_eq_zero.mp (hx hxs)
  intro φ hφ hs hsub
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hφ2 : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hs
  have hi : Integrable (fun x ↦ φ x * p.2 x j) :=
    hφ2.integrable_mul hpj
  have hd : Integrable (fun x ↦ φ x * du x) :=
    (hφ.continuous.mul hdu).integrable_of_hasCompactSupport hs.mul_right
  have he := OAI.Analysis.PDE.Weak.H1Zero.weak_derivative hp j φ hφ1 hs
  have he' := OAI.Analysis.PDE.Green.integral_directional_by_parts (μ := volume) hφ1 hu hs (Pi.single j 1)
  have hv : (∫ x, p.1 x * fderiv ℝ φ x (Pi.single j 1)) =
      ∫ x, u x * fderiv ℝ φ x (Pi.single j 1) := by
    apply integral_congr_ae
    filter_upwards [heq] with x hx
    by_cases hxs : x ∈ tsupport φ
    · rw [hx (hsub hxs)]
    · have hdφ : fderiv ℝ φ x = 0 := by
        by_contra hn
        exact hxs ((support_fderiv_subset ℝ) hn)
      simp [hdφ]
  rw [hv] at he
  simp only [smul_eq_mul, mul_sub]
  rw [integral_sub hi hd]
  have he'' : (∫ x, φ x * p.2 x j) = -(∫ x, u x * fderiv ℝ φ x (Pi.single j 1)) := by
    simpa only [mul_comm] using he
  have hu' : (∫ x, φ x * du x) = -(∫ x, u x * fderiv ℝ φ x (Pi.single j 1)) := by
    simpa only [du, mul_comm] using he'
  rw [he'', hu', sub_self]

/-- Once the value component has a C¹ representative, the gradient component
of the actual H¹ completion is its classical gradient on that open set. -/
theorem H1Zero.gradient_eq_of_value_eq
    {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω) {p : H1Pair m}
    (hp : p ∈ H1Zero univ) (u : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hu : ContDiff ℝ 1 u)
    (heq : ∀ᵐ x ∂volume, x ∈ Ω → p.1 x = u x) :
    ∀ᵐ x ∂volume, x ∈ Ω → p.2 x = OAI.Analysis.PDE.Variational.cellGradient u x := by
  have hcomp := fun j ↦ OAI.Analysis.PDE.Weak.H1Zero.gradient_component_eq_of_value_eq hΩ hp u hu heq j
  filter_upwards [ae_all_iff.mpr hcomp] with x hx
  intro hxs
  ext j
  exact hx j hxs

end OAI.Analysis.PDE.Weak
