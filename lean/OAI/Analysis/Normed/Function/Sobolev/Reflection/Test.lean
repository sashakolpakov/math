import OAI.Analysis.Normed.Function.Sobolev.Reflection.Extension

open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.Normed.Function.Sobolev

variable {d N : ℕ}

def reflectionTest (k : Fin d) (a c : Fin N → ℝ)
    (φ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  φ x + ∑j, c j * φ (normalScale k (a j)⁻¹ x)

theorem contDiff_reflectionTest (k : Fin d) (a c : Fin N → ℝ)
    {φ : (Fin d → ℝ) → ℝ} {n : WithTop ℕ∞} (hφ : ContDiff ℝ n φ) :
    ContDiff ℝ n (reflectionTest k a c φ) :=
  hφ.add (ContDiff.sum (fun j _ ↦ contDiff_const.mul (hφ.comp (normalScale k (a j)⁻¹).contDiff)))

theorem hasCompactSupport_reflectionTest (k : Fin d) (a c : Fin N → ℝ)
    (ha : ∀j, a j ≠ 0) {φ : (Fin d → ℝ) → ℝ} (hs : HasCompactSupport φ) :
    HasCompactSupport (reflectionTest k a c φ) := by
  have ht (s : Finset (Fin N)) : HasCompactSupport
      (fun x ↦ ∑j ∈ s, c j * φ (normalScale k (a j)⁻¹ x)) := by
    induction s using Finset.induction_on with
    | empty =>
      apply HasCompactSupport.intro (K := ∅) isCompact_empty
      intro x hx
      simp
    | @insert j s hj ih =>
      have hjc : HasCompactSupport (fun x ↦ c j * φ (normalScale k (a j)⁻¹ x)) :=
        (hasCompactSupport_normalScale k (inv_ne_zero (ha j)) hs).mul_left
      convert hjc.add ih using 1
      funext x
      simp only [Finset.sum_insert hj, Pi.add_apply]
  exact hs.add (ht Finset.univ)

theorem reflectionTest_derivative (k i : Fin d) (a c : Fin N → ℝ)
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ) (x : Fin d → ℝ) :
    fderiv ℝ (reflectionTest k a c φ) x (Pi.single i 1) =
      reflectionTest k a (fun j ↦ c j * (if i = k then (a j)⁻¹ else 1))
        (fun y ↦ fderiv ℝ φ y (Pi.single i 1)) x := by
  have hd := hφ.differentiable one_ne_zero
  have hs (j : Fin N) : HasFDerivAt
      (fun y ↦ c j * φ (normalScale k (a j)⁻¹ y))
      (c j • ((fderiv ℝ φ (normalScale k (a j)⁻¹ x)).comp
        (normalScale k (a j)⁻¹))) x :=
    ((hd _).hasFDerivAt.comp x (normalScale k (a j)⁻¹).hasFDerivAt).const_mul (c j)
  have he := ((hd x).hasFDerivAt.add (HasFDerivAt.sum (u := Finset.univ) (fun j _ ↦ hs j))).fderiv
  have hf : (φ + ∑j, fun y ↦ c j * φ (normalScale k (a j)⁻¹ y)) =
      reflectionTest k a c φ := by
    funext y
    simp [reflectionTest]
  rw [hf] at he
  rw [he]
  simp only [reflectionTest, add_apply, sum_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    normalScale_single, map_smul, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem integral_mul_reflectionTest (k : Fin d) (a c : Fin N → ℝ)
    (ha : ∀j, a j ≠ 0) {u φ : (Fin d → ℝ) → ℝ}
    (hu : Integrable u) (hφ : Continuous φ) (hs : HasCompactSupport φ) :
    (∫x in {x | 0 < x k}, u x * reflectionTest k a c φ x) =
      (∫x in {x | 0 < x k}, u x * φ x) +
      ∑j, c j * (∫x in {x | 0 < x k}, u x * φ (normalScale k (a j)⁻¹ x)) := by
  have hi0 : IntegrableOn (fun x ↦ u x * φ x) {x | 0 < x k} :=
    (integrable_mul_compact_test hu hφ hs).integrableOn
  have hi (j : Fin N) : IntegrableOn
      (fun x ↦ c j * (u x * φ (normalScale k (a j)⁻¹ x))) {x | 0 < x k} :=
    ((integrable_mul_compact_test hu
    (hφ.comp (normalScale k (a j)⁻¹).continuous)
    (hasCompactSupport_normalScale k (inv_ne_zero (ha j)) hs)).const_mul (c j)).integrableOn
  have he (x : Fin d → ℝ) : u x * reflectionTest k a c φ x =
      u x * φ x + ∑j, c j * (u x * φ (normalScale k (a j)⁻¹ x)) := by
    simp only [reflectionTest,mul_add,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_add hi0 (integrable_finsetSum _ (fun j _ ↦ hi j)),
    integral_finsetSum _ (fun j _ ↦ hi j)]
  simp_rw [integral_const_mul]

end OAI.Analysis.Normed.Function.Sobolev
