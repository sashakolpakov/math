import Mathlib

noncomputable section
namespace OAI.Geometry.Nikodym

open Set Filter
open scoped Topology ContDiff

/-- The radial Jacobi function of a space form of sectional curvature κ. -/
def curvatureSin (κ t : ℝ) : ℝ :=
  if 0 < κ then Real.sin (Real.sqrt κ*t)/Real.sqrt κ
  else if κ = 0 then t
  else Real.sinh (Real.sqrt (-κ)*t)/Real.sqrt (-κ)

def curvatureCos (κ t : ℝ) : ℝ :=
  if 0 < κ then Real.cos (Real.sqrt κ*t)
  else if κ = 0 then 1
  else Real.cosh (Real.sqrt (-κ)*t)

@[simp] theorem curvatureSin_zero (κ : ℝ) : curvatureSin κ 0 = 0 := by
  simp [curvatureSin]

@[simp] theorem curvatureCos_zero (κ : ℝ) : curvatureCos κ 0 = 1 := by
  simp [curvatureCos]

@[simp] theorem curvatureSin_flat (t : ℝ) : curvatureSin 0 t = t := by
  simp [curvatureSin]

@[simp] theorem curvatureCos_flat (t : ℝ) : curvatureCos 0 t = 1 := by
  simp [curvatureCos]

theorem contDiff_curvatureSin (κ : ℝ) : ContDiff ℝ ∞ (curvatureSin κ) := by
  unfold curvatureSin
  split_ifs <;> fun_prop

theorem contDiff_curvatureCos (κ : ℝ) : ContDiff ℝ ∞ (curvatureCos κ) := by
  unfold curvatureCos
  split_ifs <;> fun_prop

theorem hasDerivAt_curvatureSin (κ t : ℝ) :
    HasDerivAt (curvatureSin κ) (curvatureCos κ t) t := by
  change HasDerivAt (fun s => curvatureSin κ s) (curvatureCos κ t) t
  by_cases hκ : 0 < κ
  · simp only [curvatureSin,curvatureCos,ite_eq_left hκ]
    have hq : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.mpr hκ).ne'
    convert (((hasDerivAt_id t).const_mul (Real.sqrt κ)).sin.div_const (Real.sqrt κ)) using 1 <;>
      simp [hq]
  · by_cases hz : κ = 0
    · subst κ
      simpa only [curvatureSin_flat,curvatureCos_flat,id_eq] using! hasDerivAt_id t
    · simp only [curvatureSin,curvatureCos,ite_eq_right hκ,ite_eq_right hz]
      have hn : 0 < -κ := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hκ) hz)
      have hq : Real.sqrt (-κ) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
      convert (((hasDerivAt_id t).const_mul (Real.sqrt (-κ))).sinh.div_const (Real.sqrt (-κ))) using 1 <;>
        simp [hq]

theorem hasDerivAt_curvatureCos (κ t : ℝ) :
    HasDerivAt (curvatureCos κ) (-κ*curvatureSin κ t) t := by
  change HasDerivAt (fun s => curvatureCos κ s) (-κ*curvatureSin κ t) t
  by_cases hκ : 0 < κ
  · simp only [curvatureSin,curvatureCos,ite_eq_left hκ]
    have hq : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.mpr hκ).ne'
    have hsq : (Real.sqrt κ)^2 = κ := Real.sq_sqrt hκ.le
    convert ((hasDerivAt_id t).const_mul (Real.sqrt κ)).cos using 1 <;>
      simp only [id_eq,mul_one]
    field_simp
    linear_combination Real.sin (Real.sqrt κ*t)*hsq
  · by_cases hz : κ = 0
    · subst κ
      simpa only [curvatureCos_flat,neg_zero,zero_mul] using hasDerivAt_const t (1:ℝ)
    · simp only [curvatureSin,curvatureCos,ite_eq_right hκ,ite_eq_right hz]
      have hn : 0 < -κ := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hκ) hz)
      have hq : Real.sqrt (-κ) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
      have hsq : (Real.sqrt (-κ))^2 = -κ := Real.sq_sqrt hn.le
      convert ((hasDerivAt_id t).const_mul (Real.sqrt (-κ))).cosh using 1 <;>
        simp only [id_eq,mul_one]
      field_simp
      linear_combination -Real.sinh (Real.sqrt (-κ)*t)*hsq

theorem curvature_energy (κ t : ℝ) :
    (curvatureCos κ t)^2 + κ*(curvatureSin κ t)^2 = 1 := by
  let F : ℝ → ℝ := fun s => (curvatureCos κ s)^2 + κ*(curvatureSin κ s)^2
  have hF (s : ℝ) : HasDerivAt F 0 s := by
    convert ((hasDerivAt_curvatureCos κ s).pow 2).add
      (((hasDerivAt_curvatureSin κ s).pow 2).const_mul κ) using 1 ; ring
  have h := is_const_of_deriv_eq_zero (fun s => (hF s).differentiableAt)
    (fun s => (hF s).deriv) t 0
  simpa [F] using h

end OAI.Geometry.Nikodym
