import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MonomialFinitenessIs
import Mathlib.Topology.Compactness.Compact

/-! # Controlled Exponent Bound -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ControlledExponentBound.MonomialFiniteness

noncomputable section

/-! Dickson's lemma has a uniform finite horizon for exponent sequences with prescribed coordinate growth. This supplies field-independent termination bounds for controlled leading-monomial enlargement. -/

theorem exists_controlled_exponent_horizon (n : ℕ) (growth : ℕ → ℕ) :
    ∃ B : ℕ, ∀ f : ℕ → MonomialFinitenessIs.MonomialFiniteness.Exponent n,
      (∀ k i, f k i ≤ growth k) → ∃ i j : ℕ, i < j ∧ j < B ∧ f i ≤ f j := by
  classical
  let A := fun k => Fin n → Fin (growth k + 1)
  let : ∀ k, TopologicalSpace (A k) := fun _ => ⊥
  let : ∀ k, DiscreteTopology (A k) := fun _ => ⟨rfl⟩
  let X := (k : ℕ) → A k
  let U : ℕ × ℕ → Set X := fun ij =>
    {f | ij.1 < ij.2 ∧ ∀ a : Fin n, (f ij.1 a).val ≤ (f ij.2 a).val}
  have hU : ∀ ij, IsOpen (U ij) := by
    intro ij
    let V : Set (A ij.1 × A ij.2) := {p | ij.1 < ij.2 ∧ ∀ a, (p.1 a).val ≤ (p.2 a).val}
    have hV : IsOpen V := isOpen_discrete _
    exact hV.preimage ((continuous_apply ij.1).prodMk (continuous_apply ij.2))
  have hcover : (Set.univ : Set X) ⊆ ⋃ ij, U ij := by
    intro f _
    obtain ⟨i, j, hij, hle⟩ := (wellQuasiOrdered_le : WellQuasiOrdered (fun a b : MonomialFinitenessIs.MonomialFiniteness.Exponent n => a ≤ b))
      (fun k a => (f k a).val)
    exact Set.mem_iUnion.mpr ⟨(i, j), hij, hle⟩
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  refine ⟨T.sup Prod.snd + 1, fun f hf => ?_⟩
  let x : X := fun k i => ⟨f k i, Nat.lt_succ_of_le (hf k i)⟩
  obtain ⟨ij, hij, hx⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ x))
  exact ⟨ij.1, ij.2, hx.1, Nat.lt_succ_of_le (Finset.le_sup hij), hx.2⟩

def controlledExponentHorizon (n : ℕ) (growth : ℕ → ℕ) : ℕ :=
  (exists_controlled_exponent_horizon n growth).choose

theorem controlledExponentHorizon_spec (n : ℕ) (growth : ℕ → ℕ) (f : ℕ → MonomialFinitenessIs.MonomialFiniteness.Exponent n)
    (hf : ∀ k i, f k i ≤ growth k) :
    ∃ i j : ℕ, i < j ∧ j < controlledExponentHorizon n growth ∧ f i ≤ f j :=
  (exists_controlled_exponent_horizon n growth).choose_spec f hf

theorem controlled_bad_exponent_length (n : ℕ) (growth : ℕ → ℕ) (L : ℕ)
    (f : Fin L → MonomialFinitenessIs.MonomialFiniteness.Exponent n) (hf : ∀ k i, f k i ≤ growth k.val)
    (hbad : ∀ i j : Fin L, i < j → ¬ f i ≤ f j) : L < controlledExponentHorizon n growth := by
  classical
  by_contra hL
  have hBL : controlledExponentHorizon n growth ≤ L := Nat.le_of_not_gt hL
  let F : ℕ → MonomialFinitenessIs.MonomialFiniteness.Exponent n := fun k => if hk : k < L then f ⟨k, hk⟩ else 0
  have hF : ∀ k i, F k i ≤ growth k := by
    intro k i
    by_cases hk : k < L
    · simpa only [F, dite_eq_left hk] using hf ⟨k, hk⟩ i
    · simp only [F, dite_eq_right hk, Pi.zero_apply, Nat.zero_le]
  obtain ⟨i, j, hij, hjB, hle⟩ := controlledExponentHorizon_spec n growth F hF
  have hjL : j < L := hjB.trans_le hBL
  have hiL : i < L := hij.trans hjL
  exact hbad ⟨i, hiL⟩ ⟨j, hjL⟩ hij (by simpa only [F, dite_eq_left hiL, dite_eq_left hjL] using hle)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ControlledExponentBound.MonomialFiniteness
