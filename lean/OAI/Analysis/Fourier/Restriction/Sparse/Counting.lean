import OAI.Analysis.Fourier.Restriction.FiniteNet
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

open scoped BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem card_mul_le_of_disjoint_subsets {ι X : Type*} [DecidableEq X]
    (S : Finset ι) (F : Finset X) (B : ι → Finset X) (m : ℕ)
    (hdisj : (S : Set ι).PairwiseDisjoint B)
    (hsub : ∀ i ∈ S, B i ⊆ F) (hcard : ∀ i ∈ S, m ≤ (B i).card) :
    S.card * m ≤ F.card := by
  calc
    S.card * m = ∑ i ∈ S, m := by simp
    _ ≤ ∑ i ∈ S, (B i).card := Finset.sum_le_sum hcard
    _ = (S.biUnion B).card := (Finset.card_biUnion hdisj).symm
    _ ≤ F.card := Finset.card_le_card (by
      intro x hx
      obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hx
      exact hsub i hi hx)

/-- Disjoint small neighborhoods around separated centers convert a
lower local density into an upper bound for the number of nearby centers. -/
theorem separated_local_card_bound {X : Type*} [PseudoMetricSpace X] [DecidableEq X]
    (S E : Finset X) {ρ R : ℝ} (hρR : ρ ≤ R) (x : X) (m : ℕ)
    (hsep : ∀ z ∈ S, ∀ w ∈ S, z ≠ w → 2 * ρ ≤ dist z w)
    (hlower : ∀ z ∈ S, m ≤ (E.filter (fun y ↦ dist z y < ρ)).card) :
    (S.filter (fun z ↦ dist x z < R)).card * m ≤
      (E.filter (fun y ↦ dist x y < 2 * R)).card := by
  classical
  apply card_mul_le_of_disjoint_subsets
    (S.filter (fun z ↦ dist x z < R))
    (E.filter (fun y ↦ dist x y < 2 * R))
    (fun z ↦ E.filter (fun y ↦ dist z y < ρ)) m
  · intro z hz w hw hzw
    apply Finset.disjoint_left.mpr
    intro y hyz hyw
    have hzS := (Finset.mem_filter.mp hz).1
    have hwS := (Finset.mem_filter.mp hw).1
    have hzy := (Finset.mem_filter.mp hyz).2
    have hwy := (Finset.mem_filter.mp hyw).2
    have htri := dist_triangle z y w
    rw [dist_comm y w] at htri
    have hdist := hsep z hzS w hwS hzw
    linarith
  · intro z hz y hy
    have hxz := (Finset.mem_filter.mp hz).2
    obtain ⟨hyE, hzy⟩ := Finset.mem_filter.mp hy
    apply Finset.mem_filter.mpr
    refine ⟨hyE, ?_⟩
    have htri := dist_triangle x z y
    linarith
  · intro z hz
    exact hlower z (Finset.mem_filter.mp hz).1

/-- The geometric counting estimate combined with greedy coloring.
Each color consists of centers separated at the larger scale `R`. -/
theorem separated_density_coloring {X : Type*} [PseudoMetricSpace X] [DecidableEq X]
    (S E : Finset X) {ρ R : ℝ} (hρR : ρ ≤ R) (m k : ℕ) (hm : 0 < m) (hk : 0 < k)
    (hsep : ∀ z ∈ S, ∀ w ∈ S, z ≠ w → 2 * ρ ≤ dist z w)
    (hlower : ∀ z ∈ S, m ≤ (E.filter (fun y ↦ dist z y < ρ)).card)
    (hupper : ∀ z ∈ S, (E.filter (fun y ↦ dist z y < 2 * R)).card < k * m) :
    ∃ c : X → Fin k, ∀ z ∈ S, ∀ w ∈ S, z ≠ w → c z = c w → R ≤ dist z w := by
  apply finite_metric_coloring S R k hk
  intro z hz
  have H := (separated_local_card_bound S E hρR z m hsep hlower).trans_lt (hupper z hz)
  have Hcard : (S.filter (fun w ↦ dist z w < R)).card < k :=
    (Nat.mul_lt_mul_right hm).mp H
  apply lt_of_le_of_lt (Finset.card_le_card ?_) Hcard
  intro w hw
  obtain ⟨hwS, hneq, hdist⟩ := Finset.mem_filter.mp hw
  exact Finset.mem_filter.mpr ⟨hwS, hdist⟩

end OAI.Analysis.Fourier.Restriction
