import OAI.Analysis.PDE.Energy.Comparison

/-! The sharp upper half of the rank-extension energy comparison.  It holds
for every positive semidefinite background, regardless of its rank. -/

noncomputable section
namespace OAI.Analysis.PDE.Energy

open Matrix Set _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped MatrixOrder ComplexOrder Matrix.Norms.Elementwise

theorem mooreDet_le_of_psd_difference {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : (OAI.LinearAlgebra.Moore.complexify A).PosSemidef) (hD : (OAI.LinearAlgebra.Moore.complexify (B - A)).PosSemidef) :
    OAI.LinearAlgebra.Moore.mooreDet n A ≤ OAI.LinearAlgebra.Moore.mooreDet n B := by
  let D := B - A
  have hpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (OAI.LinearAlgebra.Moore.complexify (A + t • D)).PosSemidef := by
    rw [OAI.LinearAlgebra.Moore.complexify_add, OAI.LinearAlgebra.Moore.complexify_real_smul]
    exact hA.add (hD.smul ht.1)
  have hcont : ContinuousOn (fun t ↦ OAI.LinearAlgebra.Moore.mooreDet n (A + t • D)) (Icc (0 : ℝ) 1) :=
    fun t _ ↦ (OAI.LinearAlgebra.Moore.hasDerivAt_mooreDet_affine A D t).continuousAt.continuousWithinAt
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) 1) hcont
    (fun t _ ↦ (OAI.LinearAlgebra.Moore.hasDerivAt_mooreDet_affine A D t).hasDerivWithinAt)
    (fun t ht ↦ OAI.LinearAlgebra.Moore.mooreDifferential_nonneg_of_posSemidef _ _ (hpos t (interior_subset ht)) hD)
  simpa [D] using hm (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) zero_le_one

theorem mooreDet_segment_ge_scaled {n : ℕ}
    (D B : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hD : (OAI.LinearAlgebra.Moore.complexify D).PosSemidef) (hB : (OAI.LinearAlgebra.Moore.complexify B).PosSemidef)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t^n * OAI.LinearAlgebra.Moore.mooreDet n D ≤ OAI.LinearAlgebra.Moore.mooreDet n (t • D + (1-t) • B) := by
  rw [← OAI.LinearAlgebra.Moore.mooreDet_smul]
  apply mooreDet_le_of_psd_difference
  · rw [OAI.LinearAlgebra.Moore.complexify_real_smul]
    exact hD.smul ht.1
  · rw [add_sub_cancel_left, OAI.LinearAlgebra.Moore.complexify_real_smul]
    exact hB.smul (sub_nonneg.mpr ht.2)

theorem integral_mooreDet_segment_lower {n : ℕ}
    (D B : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hD : (OAI.LinearAlgebra.Moore.complexify D).PosSemidef) (hB : (OAI.LinearAlgebra.Moore.complexify B).PosSemidef) :
    OAI.LinearAlgebra.Moore.mooreDet n D / ((n : ℝ) + 1) ≤
      ∫ t in (0 : ℝ)..1, OAI.LinearAlgebra.Moore.mooreDet n (t • D + (1-t) • B) := by
  have hc : Continuous (fun t : ℝ => OAI.LinearAlgebra.Moore.mooreDet n (t • D + (1-t) • B)) :=
    (OAI.LinearAlgebra.Moore.continuous_mooreDet n).comp
      ((continuous_id.smul continuous_const).add ((continuous_const.sub continuous_id).smul continuous_const))
  have h := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
    (show IntervalIntegrable (fun t : ℝ => t^n * OAI.LinearAlgebra.Moore.mooreDet n D) volume 0 1 from
      (by fun_prop : Continuous (fun t : ℝ => t^n * mooreDet n D)).intervalIntegrable 0 1)
    (hc.intervalIntegrable 0 1) (fun t ht => mooreDet_segment_ge_scaled D B hD hB ht)
  rw [intervalIntegral.integral_mul_const, integral_pow] at h
  simpa only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero, Nat.cast_add, Nat.cast_one,
    one_div, div_eq_mul_inv, mul_comm, one_mul] using h

theorem pointwise_rank_energy_upper {n : ℕ}
    (D B : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hD : (OAI.LinearAlgebra.Moore.complexify D).PosSemidef) (hB : (OAI.LinearAlgebra.Moore.complexify B).PosSemidef)
    {u : ℝ} (hu : u ≤ 0) :
    (-u) * OAI.LinearAlgebra.Moore.mooreDet n D + u * (∫ t in (0 : ℝ)..1, OAI.LinearAlgebra.Moore.mooreDet n (t • D + (1-t) • B)) ≤
      (n : ℝ) / ((n : ℝ)+1) * ((-u) * OAI.LinearAlgebra.Moore.mooreDet n D) := by
  have h := mul_le_mul_of_nonpos_left (integral_mooreDet_segment_lower D B hD hB) hu
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  have he : (n : ℝ)/((n : ℝ)+1)*((-u)*OAI.LinearAlgebra.Moore.mooreDet n D) =
      (-u)*OAI.LinearAlgebra.Moore.mooreDet n D + u*(OAI.LinearAlgebra.Moore.mooreDet n D/((n : ℝ)+1)) := by
    field_simp
    ring
  rw [he]
  linarith

theorem continuous_moore_segment_integral {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X] {n : ℕ}
    {D B : X → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    (hD : Continuous D) (hB : Continuous B) :
    Continuous (fun x => ∫ t in (0 : ℝ)..1,
      OAI.LinearAlgebra.Moore.mooreDet n (t • D x + (1-t) • B x)) := by
  have hp : Continuous (fun p : X × ℝ =>
      OAI.LinearAlgebra.Moore.mooreDet n (p.2 • D p.1 + (1-p.2) • B p.1)) := by
    exact (OAI.LinearAlgebra.Moore.continuous_mooreDet n).comp
      ((continuous_snd.smul (hD.comp continuous_fst)).add
        ((continuous_const.sub continuous_snd).smul (hB.comp continuous_fst)))
  have hi : Continuous (fun x => ∫ t in Icc (0 : ℝ) 1,
      OAI.LinearAlgebra.Moore.mooreDet n (t • D x + (1-t) • B x)) :=
    continuous_parametric_integral_of_continuous (E := ℝ) hp isCompact_Icc
  simpa only [intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc] using hi

/-- The sharp upper comparison in the rank appendix does not require a rank
restriction: positivity of the background alone gives the factor n/(n+1). -/
theorem determinant_energy_sharp_upper {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)} (hS : MeasurableSet S)
    (hb : Bornology.IsBounded S) {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ}
    (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hneg : ∀ x ∈ S, u x ≤ 0)
    (hpos : ∀ x ∈ S,
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x)).PosSemidef)
    (hback : ∀ x ∈ S, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)).PosSemidef) :
    determinantMass e S (fun y => B y + u y) u + determinantSegmentEnergy e S B u ≤
      (n : ℝ) / ((n : ℝ)+1) * determinantMass e S (fun y => B y + u y) u := by
  have hXi := continuous_integrableOn_bounded hb
    (continuous_mass_integrand e (hB.add hu) hu.continuous)
  have hYi := continuous_integrableOn_bounded hb
    (hu.continuous.mul (continuous_moore_segment_integral
      (continuous_quaternionHessian_three e (hB.add hu))
      (continuous_quaternionHessian_three e hB)))
  change IntegrableOn (fun x => u x * ∫ t in (0 : ℝ)..1,
    OAI.LinearAlgebra.Moore.mooreDet n (t • OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x +
      (1-t) • OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)) S at hYi
  have hi := setIntegral_mono_on (hXi.add hYi) (hXi.const_mul ((n : ℝ)/((n : ℝ)+1)))
    hS (fun x hx => pointwise_rank_energy_upper _ _ (hpos x hx) (hback x hx) (hneg x hx))
  simp only [Pi.add_apply] at hi
  rw [integral_add hXi hYi, integral_const_mul] at hi
  exact hi

theorem normalized_determinant_energy_sharp_upper {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)} (hS : MeasurableSet S)
    (hb : Bornology.IsBounded S) {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ}
    (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hneg : ∀ x ∈ S, u x ≤ 0)
    (hpos : ∀ x ∈ S,
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x)).PosSemidef)
    (hback : ∀ x ∈ S, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)).PosSemidef)
    {Λ : ℝ} (hΛ : 0 < Λ) :
    (determinantMass e S (fun y => B y + u y) u + determinantSegmentEnergy e S B u) / Λ ≤
      (n : ℝ) / ((n : ℝ)+1) * (determinantMass e S (fun y => B y + u y) u / Λ) := by
  simpa only [mul_div_assoc] using
    (div_le_div_of_nonneg_right
      (determinant_energy_sharp_upper e hS hb hB hu hneg hpos hback) hΛ.le)

end OAI.Analysis.PDE.Energy
