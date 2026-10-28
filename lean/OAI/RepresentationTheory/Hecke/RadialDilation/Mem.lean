import OAI.RepresentationTheory.Hecke.RadialDilation.Cm

/-! # Mem -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.Mem.Realization

noncomputable section

/-!
# Concrete radial substitution for RadialDilation

The radial space is the one in the checked RadialDilation theorem. This file constructs
its dilation operator and proves that substitution by a scalar of valuation M
has the specified radial formula, rather than assuming an operator with that
formula. The comparison of the p-adic norm with LocalWeil's Haar modulus is separate.
-/

open scoped Classical

variable (q : ℕ) [Fact q.Prime]

abbrev Position := Fin 3 → ℚ_[q]

def radialBall (j : ℤ) (x : Position q) : ℂ :=
  if ∀ i, ‖x i‖ ≤ (q : ℝ) ^ (-j) then 1 else 0

theorem radialBall_mem (j : ℤ) : radialBall q j ∈ Cm.radialInput q :=
  Submodule.subset_span ⟨j, rfl⟩

theorem radialBall_closedBall (j : ℤ) :
    radialBall q j = (Metric.closedBall (0 : Position q) ((q : ℝ) ^ (-j))).indicator
      (fun _ => (1 : ℂ)) := by
  have hq : 0 < (q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).pos
  funext x
  have he : ‖x‖ ≤ (q : ℝ) ^ (-j) ↔ ∀ i, ‖x i‖ ≤ (q : ℝ) ^ (-j) :=
    pi_norm_le_iff_of_nonneg (le_of_lt (zpow_pos hq (-j)))
  simp only [radialBall, Set.indicator, Metric.mem_closedBall, dist_zero_right, he]

theorem radialBall_schwartz (j : ℤ) :
    radialBall q j ∈ Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] 3 := by
  have hq : 0 < (q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).pos
  let K := Metric.closedBall (0 : Position q) ((q : ℝ) ^ (-j))
  have hK : IsClopen K :=
    IsUltrametricDist.isClopen_closedBall _ (zpow_pos hq (-j)).ne'
  apply Weil.Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem
  · rw [radialBall_closedBall]
    exact (LocallyConstant.charFn ℂ hK).isLocallyConstant
  · apply HasCompactSupport.intro (isCompact_closedBall (0 : Position q) ((q : ℝ) ^ (-j)))
    intro x hx
    rw [radialBall_closedBall]
    exact Set.indicator_of_notMem hx _

theorem radial_le_schwartz :
    Cm.radialInput q ≤ Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] 3 := by
  apply Submodule.span_le.mpr
  rintro f ⟨j, rfl⟩
  exact radialBall_schwartz q j

def radialSchwartzEmbedding : Cm.radialInput q →ₗ[ℂ]
    Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] 3 :=
  (Cm.radialInput q).inclusion (radial_le_schwartz q)

theorem radial_eq_of_norm_eq (b : Cm.radialInput q) (x y : Position q)
    (hxy : ∀ i, ‖x i‖ = ‖y i‖) : b.val x = b.val y := by
  obtain ⟨b, hb⟩ := b
  change b x = b y
  induction hb using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨j, rfl⟩ := hf
      simp only [hxy]
  | zero => rfl
  | add f g _ _ hf hg => exact congrArg₂ (· + ·) hf hg
  | smul c f _ hf => exact congrArg (c * ·) hf

theorem radial_unit_invariant (b : Cm.radialInput q) (a : ℚ_[q])
    (ha : ‖a‖ = 1) (x : Position q) :
    b.val (fun i => a * x i) = b.val x := by
  apply radial_eq_of_norm_eq
  intro i
  rw [norm_mul, ha, one_mul]

def inverseSubstitution (a : ℚ_[q]) :
    (Position q → ℂ) →ₗ[ℂ] (Position q → ℂ) where
  toFun f x := f (fun i => a⁻¹ * x i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem inverseSubstitution_ball (a : ℚ_[q]) (n : ℤ)
    (ha : ‖a‖ = (q : ℝ) ^ (-n)) (j : ℤ) :
    inverseSubstitution q a (radialBall q j) = radialBall q (j + n) := by
  have hq : 0 < (q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).pos
  have hinv : ‖a⁻¹‖ = (q : ℝ) ^ n := by
    rw [norm_inv, ha, zpow_neg, inv_inv]
  have hratio : (q : ℝ) ^ (-j) / (q : ℝ) ^ n =
      (q : ℝ) ^ (-(j + n)) := by
    rw [← zpow_sub₀ hq.ne']
    congr 1
    ring
  funext x
  change (if ∀ i, ‖a⁻¹ * x i‖ ≤ (q : ℝ) ^ (-j) then (1 : ℂ) else 0) = _
  simp only [norm_mul, hinv]
  have he : (∀ i, (q : ℝ) ^ n * ‖x i‖ ≤ (q : ℝ) ^ (-j)) ↔
      ∀ i, ‖x i‖ ≤ (q : ℝ) ^ (-(j + n)) := by
    apply forall_congr'
    intro i
    rw [mul_comm ((q : ℝ) ^ n), ← le_div_iff₀ (zpow_pos hq n), hratio]
  simp only [he, radialBall]

theorem inverseSubstitution_mem (a : ℚ_[q]) (n : ℤ)
    (ha : ‖a‖ = (q : ℝ) ^ (-n))
    (f : Position q → ℂ) (hf : f ∈ Cm.radialInput q) :
    inverseSubstitution q a f ∈ Cm.radialInput q := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨j, rfl⟩ := hg
      change inverseSubstitution q a (radialBall q j) ∈ Cm.radialInput q
      rw [inverseSubstitution_ball q a n ha]
      exact radialBall_mem q (j + n)
  | zero => simpa only [map_zero] using (Cm.radialInput q).zero_mem
  | add f g _ _ hf hg =>
      simpa only [map_add] using (Cm.radialInput q).add_mem hf hg
  | smul c f _ hf =>
      simpa only [map_smul] using (Cm.radialInput q).smul_mem c hf

def radialSubstitution (a : ℚ_[q]) (n : ℤ)
    (ha : ‖a‖ = (q : ℝ) ^ (-n)) :
    Cm.radialInput q →ₗ[ℂ] Cm.radialInput q :=
  ((inverseSubstitution q a).comp (Cm.radialInput q).subtype).codRestrict
    (Cm.radialInput q) (fun b => inverseSubstitution_mem q a n ha b.val b.property)

def dilation : Cm.radialInput q →ₗ[ℂ] Cm.radialInput q :=
  (Real.rpow (q : ℝ) (3 / 2 : ℝ) : ℂ) •
    radialSubstitution q (q : ℚ_[q]) 1 (by simp [Padic.norm_p])

theorem dilation_apply (b : Cm.radialInput q) (x : Position q) :
    (dilation q b).val x =
      (Real.rpow (q : ℝ) (3 / 2 : ℝ) : ℂ) *
        b.val (fun i => (q : ℚ_[q])⁻¹ * x i) := rfl

/-- The norm-normalized ordinary scalar substitution. -/
def normalizedScalarSubstitution (a : ℚ_[q]) (n : ℤ)
    (ha : ‖a‖ = (q : ℝ) ^ (-n)) :
    Cm.radialInput q →ₗ[ℂ] Cm.radialInput q :=
  ((Real.sqrt (‖a‖ ^ 3))⁻¹ : ℂ) • radialSubstitution q a n ha

theorem norm_normalization (a : ℚ_[q]) (M : ℕ)
    (ha : ‖a‖ = (q : ℝ) ^ (-(M : ℤ))) :
    (Real.sqrt (‖a‖ ^ 3))⁻¹ = Real.rpow (q : ℝ) (3 * (M : ℝ) / 2) := by
  have hq : 0 < (q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).pos
  rw [ha, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_intCast,
    ← Real.rpow_mul (le_of_lt hq), ← Real.rpow_mul (le_of_lt hq),
    ← Real.rpow_neg (le_of_lt hq)]
  congr 1
  push_cast
  ring

/-- The concrete operator supplies RadialDilation's hUq once the local scalar's norm
is read from its valuation. Unit factors disappear on radial functions. -/
theorem normalizedScalarSubstitution_apply (a : ℚ_[q]) (M : ℕ)
    (ha : ‖a‖ = (q : ℝ) ^ (-(M : ℤ)))
    (b : Cm.radialInput q) (x : Position q) :
    (normalizedScalarSubstitution q a M ha b).val x =
      (Real.rpow (q : ℝ) (3 * (M : ℝ) / 2) : ℂ) *
        b.val (fun i => ((q : ℚ_[q]) ^ M)⁻¹ * x i) := by
  change ((Real.sqrt (‖a‖ ^ 3))⁻¹ : ℂ) *
    b.val (fun i => a⁻¹ * x i) = _
  rw [← Complex.ofReal_inv, norm_normalization q a M ha]
  congr 1
  apply radial_eq_of_norm_eq
  intro i
  simp only [norm_mul, norm_inv, ha, Padic.norm_p_pow]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.Mem.Realization
