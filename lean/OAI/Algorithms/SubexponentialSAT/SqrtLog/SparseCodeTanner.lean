import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCodeBasic

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SparseCode

open scoped BigOperators

/-- The real inequality used after counting the active left and right
vertices. It has no graph or coding hypotheses hidden in its statement. -/
theorem tanner_scalar_bound {S u v D N δ ε : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hD : 0 < D) (hN : 0 < N)
    (hδ : 0 ≤ δ)
    (hleft : δ * D * u ≤ S) (hright : δ * D * v ≤ S)
    (hmix : S ≤ D * u * v / N + ε * D * Real.sqrt (u * v)) :
    N * D * δ * (δ - ε) ≤ S := by
  let t := Real.sqrt (u * v)
  have ht : 0 < t := Real.sqrt_pos.2 (mul_pos hu hv)
  have ht2 : t ^ 2 = u * v := Real.sq_sqrt (le_of_lt (mul_pos hu hv))
  have hδD : 0 ≤ δ * D := mul_nonneg hδ hD.le
  have hlocal : δ * D * t ≤ S := by
    rcases le_total u v with huv | hvu
    · have htv : t ≤ v := Real.sqrt_le_iff.mpr ⟨hv.le, by nlinarith⟩
      exact (mul_le_mul_of_nonneg_left htv hδD).trans hright
    · have htu : t ≤ u := Real.sqrt_le_iff.mpr ⟨hu.le, by nlinarith⟩
      exact (mul_le_mul_of_nonneg_left htu hδD).trans hleft
  have hmul : (δ - ε) * (D * t) ≤ (t / N) * (D * t) := by
    calc
      (δ - ε) * (D * t) = δ * D * t - ε * D * t := by ring
      _ ≤ D * u * v / N := by linarith
      _ = (t / N) * (D * t) := by rw [div_mul_eq_mul_div]; congr 1; nlinarith
  have hratio : δ - ε ≤ t / N := le_of_mul_le_mul_right hmul (mul_pos hD ht)
  have hsize : N * (δ - ε) ≤ t := by
    have := (le_div_iff₀ hN).mp hratio
    nlinarith
  calc
    N * D * δ * (δ - ε) = (δ * D) * (N * (δ - ε)) := by ring
    _ ≤ (δ * D) * t := mul_le_mul_of_nonneg_left hsize hδD
    _ ≤ S := hlocal

namespace PortGraph

variable {V P R : Type*} [Fintype V] [Fintype P]
    [DecidableEq V] [DecidableEq P]

def leftActive (w : V × P → F3) : Finset V :=
  Finset.univ.filter fun v => leftWord w v ≠ 0

def rightActive (G : PortGraph V P) (w : V × P → F3) : Finset V :=
  Finset.univ.filter fun v => G.rightWord w v ≠ 0

omit [DecidableEq V] [DecidableEq P] in
@[simp] theorem mem_leftActive (w : V × P → F3) (v : V) :
    v ∈ leftActive w ↔ leftWord w v ≠ 0 := by simp [leftActive]

omit [DecidableEq V] [DecidableEq P] in
@[simp] theorem mem_rightActive (G : PortGraph V P) (w : V × P → F3) (v : V) :
    v ∈ G.rightActive w ↔ G.rightWord w v ≠ 0 := by simp [rightActive]

omit [DecidableEq V] [DecidableEq P] in
theorem sum_left_weights (w : V × P → F3) :
    ∑ v, weight (leftWord w v) = weight w := by
  simp only [weight_eq_sum, leftWord]
  exact (Fintype.sum_prod_type (fun e : V × P => if w e ≠ 0 then (1 : ℕ) else 0)).symm

omit [DecidableEq V] [DecidableEq P] in
theorem sum_right_weights (G : PortGraph V P) (w : V × P → F3) :
    ∑ v, weight (G.rightWord w v) = weight w := by
  simp only [weight_eq_sum, rightWord]
  calc
    _ = ∑ e : V × P, if w (G.rotation.symm e) ≠ 0 then (1 : ℕ) else 0 :=
      (Fintype.sum_prod_type
        (fun e : V × P => if w (G.rotation.symm e) ≠ 0 then (1 : ℕ) else 0)).symm
    _ = _ := G.rotation.symm.sum_comp (fun e => if w e ≠ 0 then (1 : ℕ) else 0)

omit [DecidableEq V] [DecidableEq P] in
theorem leftActive_nonempty (w : V × P → F3) (hw : w ≠ 0) :
    (leftActive w).Nonempty := by
  obtain ⟨e, he⟩ := Function.ne_iff.mp hw
  refine ⟨e.1, (mem_leftActive w e.1).2 ?_⟩
  intro hz
  have := congrFun hz e.2
  exact he this

omit [DecidableEq V] [DecidableEq P] in
theorem rightActive_nonempty (G : PortGraph V P) (w : V × P → F3) (hw : w ≠ 0) :
    (G.rightActive w).Nonempty := by
  obtain ⟨e, he⟩ := Function.ne_iff.mp hw
  refine ⟨(G.rotation e).1, (mem_rightActive G w _).2 ?_⟩
  intro hz
  have hh := congrFun hz (G.rotation e).2
  simp only [rightWord, Prod.mk.eta, Equiv.symm_apply_apply, Pi.zero_apply] at hh
  exact he hh

omit [DecidableEq P] in
theorem support_subset_edgesBetween (G : PortGraph V P) (w : V × P → F3) :
    support w ⊆ G.edgesBetween (leftActive w) (G.rightActive w) := by
  intro e he
  have hw := (mem_support w e).mp he
  simp only [edgesBetween, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · apply (mem_leftActive w e.1).2
    intro hz
    exact hw (congrFun hz e.2)
  · apply (mem_rightActive G w (G.rotation e).1).2
    intro hz
    have hh := congrFun hz (G.rotation e).2
    simp only [rightWord, Prod.mk.eta, Equiv.symm_apply_apply, Pi.zero_apply] at hh
    exact hw hh

omit [DecidableEq P] in
theorem weight_le_edgeCount (G : PortGraph V P) (w : V × P → F3) :
    weight w ≤ G.edgeCount (leftActive w) (G.rightActive w) :=
  Finset.card_le_card (support_subset_edgesBetween G w)

omit [DecidableEq V] [DecidableEq P] in
theorem local_left_mass {Q : CheckMatrix R P} {δ : ℝ}
    (hQ : HasRelativeDistance Q δ) (w : V × P → F3)
    (hw : ∀ v, IsCodeword Q (leftWord w v)) :
    δ * Fintype.card P * (leftActive w).card ≤ (weight w : ℝ) := by
  calc
    δ * Fintype.card P * (leftActive w).card =
        ∑ _v ∈ leftActive w, δ * Fintype.card P := by simp [mul_comm]
    _ ≤ ∑ v ∈ leftActive w, (weight (leftWord w v) : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      exact hQ _ (hw v) ((mem_leftActive w v).mp hv)
    _ ≤ ∑ v, (weight (leftWord w v) : ℝ) :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.cast_nonneg _)
    _ = (weight w : ℝ) := by exact_mod_cast sum_left_weights w

omit [DecidableEq V] [DecidableEq P] in
theorem local_right_mass (G : PortGraph V P) {Q : CheckMatrix R P} {δ : ℝ}
    (hQ : HasRelativeDistance Q δ) (w : V × P → F3)
    (hw : ∀ v, IsCodeword Q (G.rightWord w v)) :
    δ * Fintype.card P * (G.rightActive w).card ≤ (weight w : ℝ) := by
  calc
    δ * Fintype.card P * (G.rightActive w).card =
        ∑ _v ∈ G.rightActive w, δ * Fintype.card P := by simp [mul_comm]
    _ ≤ ∑ v ∈ G.rightActive w, (weight (G.rightWord w v) : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      exact hQ _ (hw v) ((mem_rightActive G w v).mp hv)
    _ ≤ ∑ v, (weight (G.rightWord w v) : ℝ) :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.cast_nonneg _)
    _ = (weight w : ℝ) := by exact_mod_cast sum_right_weights G w

omit [DecidableEq P] in
/-- Global Tanner distance from only the explicit local distance and the
finite graph mixing inequality. -/
theorem tanner_distance (G : PortGraph V P) {Q : CheckMatrix R P} {δ ε : ℝ}
    (hV : 0 < Fintype.card V) (hP : 0 < Fintype.card P)
    (hδ : 0 ≤ δ) (hQ : HasRelativeDistance Q δ) (hG : G.HasMixing ε)
    (w : V × P → F3) (hw : G.IsTannerCodeword Q w) (hw0 : w ≠ 0) :
    (Fintype.card V : ℝ) * Fintype.card P * δ * (δ - ε) ≤ (weight w : ℝ) := by
  apply tanner_scalar_bound
      (u := ((leftActive w).card : ℝ))
      (v := ((G.rightActive w).card : ℝ))
      (D := (Fintype.card P : ℝ)) (N := (Fintype.card V : ℝ))
      (ε := ε)
  · exact_mod_cast Finset.card_pos.mpr (leftActive_nonempty w hw0)
  · exact_mod_cast Finset.card_pos.mpr (rightActive_nonempty G w hw0)
  · exact_mod_cast hP
  · exact_mod_cast hV
  · exact hδ
  · exact local_left_mass hQ w hw.1
  · exact local_right_mass G hQ w hw.2
  · have he : (weight w : ℝ) ≤
        (G.edgeCount (leftActive w) (G.rightActive w) : ℝ) := by
      exact_mod_cast weight_le_edgeCount G w
    exact he.trans (hG _ _)

end PortGraph

end SubexponentialSAT.SqrtLog.SparseCode

end OAI.Algorithms
