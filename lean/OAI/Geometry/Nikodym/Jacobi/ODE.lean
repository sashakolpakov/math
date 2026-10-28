import OAI.Geometry.Nikodym.Jacobi.Functions

noncomputable section
namespace OAI.Geometry.Nikodym

open Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eq_of_hasDerivAt_zero_on_convex {S : Set ℝ} (hS : Convex ℝ S)
    {f : ℝ → E} (hf : ∀ t ∈ S, HasDerivAt f 0 t)
    {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) : f b = f a := by
  have hd : ∀ t ∈ S, HasFDerivWithinAt f (0 : ℝ →L[ℝ] E) S t := by
    intro t ht
    simpa using (hf t ht).hasFDerivAt.hasFDerivWithinAt
  have h := hS.norm_image_sub_le_of_norm_hasFDerivWithin_le hd
    (fun t ht => by simp : ∀ t ∈ S, ‖(0 : ℝ →L[ℝ] E)‖ ≤ (0:ℝ)) ha hb
  simpa only [zero_mul,norm_le_zero_iff,sub_eq_zero] using h

theorem hasDerivAt_jacobi_first_integral {κ t : ℝ} {J V : ℝ → E}
    (hJ : HasDerivAt J (V t) t) (hV : HasDerivAt V ((-κ) • J t) t) :
    HasDerivAt (fun s => curvatureCos κ s • J s - curvatureSin κ s • V s) 0 t := by
  convert ((hasDerivAt_curvatureCos κ t).smul hJ).sub
    ((hasDerivAt_curvatureSin κ t).smul hV) using 1
  module

theorem hasDerivAt_jacobi_second_integral {κ t : ℝ} {J V : ℝ → E}
    (hJ : HasDerivAt J (V t) t) (hV : HasDerivAt V ((-κ) • J t) t) :
    HasDerivAt (fun s => (κ*curvatureSin κ s) • J s + curvatureCos κ s • V s) 0 t := by
  convert (((hasDerivAt_curvatureSin κ t).const_mul κ).smul hJ).add
    ((hasDerivAt_curvatureCos κ t).smul hV) using 1
  module

/-- Exact uniqueness and solution formula for the constant-curvature
Jacobi equation on any real interval containing zero. -/
theorem constant_curvature_ode_solution {S : Set ℝ} (hS : Convex ℝ S) (h0 : 0 ∈ S)
    (κ : ℝ) {J V : ℝ → E}
    (hJ : ∀ t ∈ S, HasDerivAt J (V t) t)
    (hV : ∀ t ∈ S, HasDerivAt V ((-κ) • J t) t)
    {t : ℝ} (ht : t ∈ S) :
    J t = curvatureCos κ t • J 0 + curvatureSin κ t • V 0 ∧
    V t = (-κ*curvatureSin κ t) • J 0 + curvatureCos κ t • V 0 := by
  let A : ℝ → E := fun s => curvatureCos κ s • J s - curvatureSin κ s • V s
  let B : ℝ → E := fun s => (κ*curvatureSin κ s) • J s + curvatureCos κ s • V s
  have hA : A t = J 0 := by
    have hh := eq_of_hasDerivAt_zero_on_convex hS
      (fun s hs => hasDerivAt_jacobi_first_integral (κ := κ) (hJ s hs) (hV s hs)) h0 ht
    simpa only [A,curvatureCos_zero,curvatureSin_zero,one_smul,zero_smul,sub_zero] using hh
  have hB : B t = V 0 := by
    have hh := eq_of_hasDerivAt_zero_on_convex hS
      (fun s hs => hasDerivAt_jacobi_second_integral (κ := κ) (hJ s hs) (hV s hs)) h0 ht
    simpa only [B,curvatureCos_zero,curvatureSin_zero,mul_zero,zero_smul,one_smul,zero_add] using hh
  constructor
  · calc
      J t = ((curvatureCos κ t)^2+κ*(curvatureSin κ t)^2) • J t := by rw [curvature_energy,one_smul]
      _ = curvatureCos κ t • A t + curvatureSin κ t • B t := by dsimp [A,B]; module
      _ = _ := by rw [hA,hB]
  · calc
      V t = ((curvatureCos κ t)^2+κ*(curvatureSin κ t)^2) • V t := by rw [curvature_energy,one_smul]
      _ = (-κ*curvatureSin κ t) • A t + curvatureCos κ t • B t := by dsimp [A,B]; module
      _ = _ := by rw [hA,hB]

theorem constant_curvature_jacobi_solution {S : Set ℝ} (hS : Convex ℝ S) (h0 : 0 ∈ S)
    (κ : ℝ) {J V : ℝ → E} {w : E}
    (hJ : ∀ t ∈ S, HasDerivAt J (V t) t)
    (hV : ∀ t ∈ S, HasDerivAt V ((-κ) • J t) t)
    (hJ0 : J 0 = 0) (hV0 : V 0 = w) {t : ℝ} (ht : t ∈ S) :
    J t = curvatureSin κ t • w ∧ V t = curvatureCos κ t • w := by
  simpa only [hJ0,hV0,smul_zero,zero_add] using constant_curvature_ode_solution hS h0 κ hJ hV ht

end OAI.Geometry.Nikodym
