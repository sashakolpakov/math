import OAI.Geometry.Kakeya.Quadratic.HausdorffProductCover

open Set _root_.MeasureTheory Metric
open scoped ENNReal Topology

noncomputable section
namespace OAI.Geometry.Kakeya.Quadratic

theorem interval_grid {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ N : ℕ, ∃ V : Fin N → Set ℝ,
      Icc (-R) R ⊆ ⋃ i, V i ∧
      (∀ i, ediam (V i) ≤ ENNReal.ofReal δ) ∧
      (N : ℝ) * δ ≤ 2*R+1 := by
  let N : ℕ := ⌊2*R/δ⌋₊ + 1
  let V : Fin N → Set ℝ := fun i => Icc (-R+(i:ℝ)*δ) (-R+((i:ℝ)+1)*δ)
  refine ⟨N, V, ?_, ?_, ?_⟩
  · intro x hx
    have hx0 : 0 ≤ (x+R)/δ := div_nonneg (by linarith [hx.1]) hδ.le
    have hxR : (x+R)/δ ≤ 2*R/δ := div_le_div_of_nonneg_right (by linarith [hx.2]) hδ.le
    let i : Fin N := ⟨⌊(x+R)/δ⌋₊, Nat.lt_succ_of_le (Nat.floor_mono hxR)⟩
    refine mem_iUnion.mpr ⟨i, ?_⟩
    change -R+(⌊(x+R)/δ⌋₊:ℝ)*δ ≤ x ∧ x ≤ -R+((⌊(x+R)/δ⌋₊:ℝ)+1)*δ
    have hlow := (le_div_iff₀ hδ).mp (Nat.floor_le hx0)
    have hupp := (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one ((x+R)/δ))
    constructor <;> linarith
  · intro i
    apply Metric.ediam_le_of_forall_dist_le
    intro x hx y hy
    rw [Real.dist_eq]
    apply abs_sub_le_iff.mpr
    change -R+(i:ℝ)*δ ≤ x ∧ x ≤ -R+((i:ℝ)+1)*δ at hx
    change -R+(i:ℝ)*δ ≤ y ∧ y ≤ -R+((i:ℝ)+1)*δ at hy
    constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]
  · have hf := (le_div_iff₀ hδ).mp
      (Nat.floor_le (show 0 ≤ 2*R/δ from div_nonneg (by positivity) hδ.le))
    change ((⌊2*R/δ⌋₊+1:ℕ):ℝ)*δ ≤ 2*R+1
    push_cast
    nlinarith

theorem finitePowerCover_cube (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    FinitePowerCover (Set.pi Set.univ (fun _ : Fin n => Icc (-R) R)) (n : ℝ)
      (ENNReal.ofReal (2*R+1)^n) := by
  classical
  intro δ hδ hδ1
  have hδt : δ ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) hδ1
  have hdr : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδt
  have hdr1 : δ.toReal ≤ 1 := by
    exact (ENNReal.toReal_le_toReal hδt (by norm_num)).mpr hδ1
  obtain ⟨N, V, hVc, hVd, hNc⟩ := interval_grid hR hdr hdr1
  let I := Fin n → Fin N
  let e := (Fintype.equivFin I).symm
  let W : Fin (Fintype.card I) → Set (Fin n → ℝ) :=
    fun i => Set.pi Set.univ (fun j => V (e i j))
  refine ⟨Fintype.card I, W, ?_, ?_, ?_⟩
  · intro x hx
    have hxj (j : Fin n) : ∃ i : Fin N, x j ∈ V i :=
      mem_iUnion.mp (hVc (hx j (mem_univ j)))
    choose i hi using hxj
    refine mem_iUnion.mpr ⟨(Fintype.equivFin I) i, ?_⟩
    simpa [W, e] using (show x ∈ Set.pi Set.univ (fun j => V (i j)) from fun j _ => hi j)
  · intro i
    apply Metric.ediam_pi_le_of_le
    intro j
    simpa only [ENNReal.ofReal_toReal hδt] using hVd (e i j)
  · change (Fintype.card (Fin n → Fin N) : ℝ≥0∞)*δ^(n:ℝ) ≤ _
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, ENNReal.rpow_natCast]
    rw [← mul_pow]
    apply pow_le_pow_left'
    rw [← ENNReal.ofReal_toReal hδt, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
    exact ENNReal.ofReal_le_ofReal hNc

end OAI.Geometry.Kakeya.Quadratic
