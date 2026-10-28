import OAI.Analysis.PDE.Weak.Elliptic.Cutoff
import OAI.Analysis.PDE.Weak.Elliptic.Energy

noncomputable section
open _root_.MeasureTheory Filter InnerProductSpace
namespace OAI.Analysis.PDE.Weak

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {μ : Measure X}

omit [NormedSpace ℝ X] in
theorem norm_cutoffL2_le (η : X → ℝ) (hη : Continuous η) {M : ℝ}
    (hM : ∀ x, |η x| ≤ M) (u : Lp E 2 μ) :
    ‖cutoffL2 η hη hM u‖ ≤ M * ‖u‖ :=
  norm_fieldMultiplier_le (scalarField η) (continuous_scalarField hη).aestronglyMeasurable
    (Eventually.of_forall fun x ↦ (norm_scalarField_le η x).trans (hM x)) u

omit [NormedSpace ℝ X] in
theorem norm_vectorProductL2_le (g : X → E) (hg : Continuous g) {M : ℝ}
    (hM : ∀ x, ‖g x‖ ≤ M) (u : Lp ℝ 2 μ) :
    ‖vectorProductL2 g hg hM u‖ ≤ M * ‖u‖ :=
  norm_fieldMultiplier_le (vectorField g) (continuous_vectorField hg).aestronglyMeasurable
    (Eventually.of_forall fun x ↦ (norm_vectorField_le g x).trans (hM x)) u

omit [NormedSpace ℝ X] in
theorem inner_cutoffL2 (η : X → ℝ) (hη : Continuous η) {M : ℝ}
    (hM : ∀ x, |η x| ≤ M) (u w : Lp E 2 μ) :
    inner ℝ u (cutoffL2 η hη hM w) = inner ℝ (cutoffL2 η hη hM u) w := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cutoffL2_ae η hη hM u, cutoffL2_ae η hη hM w] with x hx hy
  rw [hx, hy, real_inner_smul_left, real_inner_smul_right]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [BorelSpace X] [SecondCountableTopology X] in
theorem fieldMultiplier_inner (A : X → E →L[ℝ] E) (hA : AEStronglyMeasurable A μ)
    {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖A x‖ ≤ M) (u w : Lp E 2 μ) :
    inner ℝ (fieldMultiplierCLM A hA hM u) w =
      ∫ x, inner ℝ (A x (u x)) (w x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fieldMultiplierCLM_ae A hA hM u] with x hx
  rw [hx]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [BorelSpace X] [SecondCountableTopology X] in
theorem fieldMultiplier_lower_bound (A : X → E →L[ℝ] E)
    (hA : AEStronglyMeasurable A μ) {M lam : ℝ}
    (hM : ∀ᵐ x ∂μ, ‖A x‖ ≤ M)
    (hell : ∀ᵐ x ∂μ, ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v) (u : Lp E 2 μ) :
    lam * ‖u‖ ^ 2 ≤ inner ℝ (fieldMultiplierCLM A hA hM u) u := by
  calc
    _ = ∫ x, lam * inner ℝ (u x) (u x) ∂μ := by
      rw [integral_const_mul, ← L2.inner_def, real_inner_self_eq_norm_sq]
    _ ≤ ∫ x, inner ℝ (fieldMultiplierCLM A hA hM u x) (u x) ∂μ := by
      apply integral_mono_ae ((L2.integrable_inner (𝕜 := ℝ) u u).const_mul lam)
        (L2.integrable_inner (𝕜 := ℝ) _ _)
      filter_upwards [fieldMultiplierCLM_ae A hA hM u, hell] with x hx he
      rw [hx, real_inner_self_eq_norm_sq]
      exact he _
    _ = _ := (L2.inner_def _ _).symm

omit [NormedSpace ℝ X] in
theorem cutoffL2_fieldMultiplier (η : X → ℝ) (hη : Continuous η) {M : ℝ}
    (hM : ∀ x, |η x| ≤ M) (A : X → E →L[ℝ] E)
    (hA : AEStronglyMeasurable A μ) {B : ℝ} (hB : ∀ᵐ x ∂μ, ‖A x‖ ≤ B)
    (u : Lp E 2 μ) :
    cutoffL2 η hη hM (fieldMultiplierCLM A hA hB u) =
      fieldMultiplierCLM A hA hB (cutoffL2 η hη hM u) := by
  apply Lp.ext
  filter_upwards [cutoffL2_ae η hη hM (fieldMultiplierCLM A hA hB u),
    fieldMultiplierCLM_ae A hA hB u,
    fieldMultiplierCLM_ae A hA hB (cutoffL2 η hη hM u), cutoffL2_ae η hη hM u]
    with x hx hy hz hw
  rw [hx, hy, hz, hw, map_smul]

variable [μ.IsAddRightInvariant]

/-- Exact product rule on the genuine L² coefficient multiplier. -/
theorem differenceQuotientL2_fieldMultiplier (v : X) (h : ℝ)
    (A : X → E →L[ℝ] E) (hA : Continuous A) {M D : ℝ}
    (hM : ∀ x, ‖A x‖ ≤ M) (hD : ∀ x, ‖differenceQuotient v h A x‖ ≤ D)
    (u : Lp E 2 μ) :
    differenceQuotientL2 μ v h
        (fieldMultiplierCLM A hA.aestronglyMeasurable (Eventually.of_forall hM) u) =
      fieldMultiplierCLM (fun x ↦ A (x + h • v))
        (hA.comp (continuous_id.add continuous_const)).aestronglyMeasurable
        (Eventually.of_forall fun _ ↦ hM _) (differenceQuotientL2 μ v h u) +
      fieldMultiplierCLM (differenceQuotient v h A)
        (continuous_differenceQuotient v h hA).aestronglyMeasurable
        (Eventually.of_forall hD) u := by
  apply Lp.ext
  have ht := (measurePreserving_add_right μ (h • v)).quasiMeasurePreserving.ae
    (fieldMultiplierCLM_ae A hA.aestronglyMeasurable (Eventually.of_forall hM) u)
  filter_upwards [coe_differenceQuotientL2 μ v h
      (fieldMultiplierCLM A hA.aestronglyMeasurable (Eventually.of_forall hM) u),
    fieldMultiplierCLM_ae A hA.aestronglyMeasurable (Eventually.of_forall hM) u, ht,
    Lp.coeFn_add
      (fieldMultiplierCLM (fun x ↦ A (x + h • v))
        (hA.comp (continuous_id.add continuous_const)).aestronglyMeasurable
        (Eventually.of_forall fun x ↦ hM _) (differenceQuotientL2 μ v h u))
      (fieldMultiplierCLM (differenceQuotient v h A)
        (continuous_differenceQuotient v h hA).aestronglyMeasurable
        (Eventually.of_forall hD) u),
    fieldMultiplierCLM_ae (fun x ↦ A (x + h • v))
      (hA.comp (continuous_id.add continuous_const)).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ hM _) (differenceQuotientL2 μ v h u),
    fieldMultiplierCLM_ae (differenceQuotient v h A)
      (continuous_differenceQuotient v h hA).aestronglyMeasurable
      (Eventually.of_forall hD) u,
    coe_differenceQuotientL2 μ v h u] with x hx hy hz hw hp hq hr
  rw [hx, hw]
  simp only [Pi.add_apply, hp, hq, hr, differenceQuotient, hy, hz,
    map_smul, map_sub, smul_apply, sub_apply]
  module

end OAI.Analysis.PDE.Weak
