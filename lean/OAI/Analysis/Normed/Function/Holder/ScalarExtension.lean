import OAI.Analysis.Normed.Function.Holder.Banach
import Mathlib.Analysis.MeanInequalitiesPow

open Set
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder

variable {X : Type*} [MetricSpace X] {K : Set X}

/-- The scalar McShane formula for the snowflake distance. -/
def holderInfExtension (f : K → ℝ) (H α : ℝ) (x : X) : ℝ :=
  ⨅ y : K, f y + H * dist x y ^ α

theorem holderInfExtension_bddBelow (f : K → ℝ) {B H α : ℝ}
    (hf : ∀ y, |f y| ≤ B) (hH : 0 ≤ H) (x : X) :
    BddBelow (range fun y : K ↦ f y + H * dist x y ^ α) := by
  refine ⟨-B, ?_⟩
  rintro z ⟨y, rfl⟩
  exact (abs_le.mp (hf y)).1.trans (le_add_of_nonneg_right (by positivity))

theorem dist_rpow_triangle {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (x y z : X) :
    dist x z ^ α ≤ dist x y ^ α + dist y z ^ α := by
  exact (Real.rpow_le_rpow dist_nonneg (dist_triangle x y z) hα).trans
    (Real.rpow_add_le_add_rpow dist_nonneg dist_nonneg hα hα1)

theorem holderInfExtension_eq [Nonempty K] (f : K → ℝ) {B H α : ℝ}
    (hf : ∀ y, |f y| ≤ B) (hH : 0 ≤ H) (hα : 0 < α)
    (hh : ∀ y z : K, |f y - f z| ≤ H * dist (y : X) z ^ α) (y : K) :
    holderInfExtension f H α y = f y := by
  apply le_antisymm
  · have h := ciInf_le (holderInfExtension_bddBelow f (α := α) hf hH y) y
    simpa [holderInfExtension, Real.zero_rpow hα.ne'] using h
  · apply le_ciInf
    intro z
    have h := (le_abs_self (f y - f z)).trans (hh y z)
    linarith

theorem holderInfExtension_lower [Nonempty K] (f : K → ℝ) {B H α : ℝ}
    (hf : ∀ y, |f y| ≤ B) (hH : 0 ≤ H) (x : X) :
    -B ≤ holderInfExtension f H α x := by
  apply le_ciInf
  intro y
  exact (abs_le.mp (hf y)).1.trans (le_add_of_nonneg_right (by positivity))

theorem holderInfExtension_one_sided [Nonempty K] (f : K → ℝ) {B H α : ℝ}
    (hf : ∀ y, |f y| ≤ B) (hH : 0 ≤ H) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (x y : X) : holderInfExtension f H α x ≤ holderInfExtension f H α y + H * dist x y ^ α := by
  have hb : holderInfExtension f H α x - H * dist x y ^ α ≤ holderInfExtension f H α y := by
    apply le_ciInf
    intro z
    have hbase := ciInf_le (holderInfExtension_bddBelow f (α := α) hf hH x) z
    have htri := mul_le_mul_of_nonneg_left (dist_rpow_triangle hα hα1 x y z) hH
    change holderInfExtension f H α x ≤ f z + H * dist x z ^ α at hbase
    nlinarith
  linarith

theorem holderInfExtension_holder [Nonempty K] (f : K → ℝ) {B H α : ℝ}
    (hf : ∀ y, |f y| ≤ B) (hH : 0 ≤ H) (hα : 0 ≤ α) (hα1 : α ≤ 1) (x y : X) :
    |holderInfExtension f H α x - holderInfExtension f H α y| ≤ H * dist x y ^ α := by
  have hxy := holderInfExtension_one_sided f hf hH hα hα1 x y
  have hyx := holderInfExtension_one_sided f hf hH hα hα1 y x
  rw [dist_comm y x] at hyx
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem abs_min_const_sub_le (B a b : ℝ) : |min B a - min B b| ≤ |a - b| := by
  rcases le_total a B with ha | ha <;> rcases le_total b B with hb | hb
  · simp only [min_eq_right ha, min_eq_right hb, le_refl]
  · rw [min_eq_right ha, min_eq_left hb, abs_of_nonpos (sub_nonpos.mpr ha),
      abs_of_nonpos (sub_nonpos.mpr (ha.trans hb))]
    linarith
  · rw [min_eq_left ha, min_eq_right hb, abs_of_nonneg (sub_nonneg.mpr hb),
      abs_of_nonneg (sub_nonneg.mpr (hb.trans ha))]
    linarith
  · simp only [min_eq_left ha, min_eq_left hb, sub_self, abs_zero, abs_nonneg]

/-- Bounded scalar extension, preserving both the supremum bound and the
Hölder constant on a nonempty subset. -/
def boundedHolderExtension (f : K → ℝ) (B H α : ℝ) (x : X) : ℝ :=
  min B (holderInfExtension f H α x)

theorem boundedHolderExtension_bound [Nonempty K] (f : K → ℝ) {B H α : ℝ}
    (hB : 0 ≤ B) (hf : ∀ y, |f y| ≤ B) (hH : 0 ≤ H) (x : X) :
    |boundedHolderExtension f B H α x| ≤ B := by
  apply abs_le.mpr
  exact ⟨le_min (by linarith) (holderInfExtension_lower f hf hH x), min_le_left _ _⟩

theorem boundedHolderExtension_eq [Nonempty K] (f : K → ℝ) {B H α : ℝ}
    (hf : ∀ y, |f y| ≤ B) (hH : 0 ≤ H) (hα : 0 < α)
    (hh : ∀ y z : K, |f y - f z| ≤ H * dist (y : X) z ^ α) (y : K) :
    boundedHolderExtension f B H α y = f y := by
  rw [boundedHolderExtension, holderInfExtension_eq f hf hH hα hh]
  exact min_eq_right (abs_le.mp (hf y)).2

theorem boundedHolderExtension_holder [Nonempty K] (f : K → ℝ) {B H α : ℝ}
    (hf : ∀ y, |f y| ≤ B) (hH : 0 ≤ H) (hα : 0 ≤ α) (hα1 : α ≤ 1) (x y : X) :
    |boundedHolderExtension f B H α x - boundedHolderExtension f B H α y| ≤ H * dist x y ^ α :=
  (abs_min_const_sub_le B _ _).trans (holderInfExtension_holder f hf hH hα hα1 x y)

end OAI.Analysis.Normed.Function.Holder
