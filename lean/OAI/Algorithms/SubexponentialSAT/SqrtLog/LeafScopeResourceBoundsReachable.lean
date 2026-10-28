import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeResourceBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCodeBounds

namespace OAI.Algorithms

/-! Pointwise bounds on every trial of the concrete selector recurrence.
The score may be arbitrary: resource validity does not assume score correctness. -/
namespace SubexponentialSAT.SqrtLog.LeafScopeResourceBounds
open HashSelectProgram

abbrev selected (score : Records → List Bool → List Bool)
    (seed : List Bool) (rest initial : Records) (round : ℕ) :=
  iter (payloadNext score seed rest) round initial

theorem selected_length (score : Records → List Bool → List Bool)
    (seed : List Bool) (rest initial : Records) (round : ℕ) :
    (selected score seed rest initial round).length = initial.length + round := by
  induction round with
  | zero => simp [selected, iter]
  | succ round ih => simp [selected, iter_succ_apply, payloadNext, selected] at *; omega

theorem selected_slots {α : Type*} (decode : List Bool → List α)
    (score : Records → List Bool → List Bool) (seed : List Bool) (rest initial : Records)
    (P round : ℕ) (hfamily : ∀ bits ∈ seed :: rest, (decode bits).length ≤ P) :
    slots ((selected score seed rest initial round).map decode) ≤ slots (initial.map decode) + round * P := by
  induction round with
  | zero => simp [selected, iter]
  | succ round ih =>
    have hh := hfamily _ (HashSelect.best_mem
      (fun bits => BinaryArithmetic.toNat (score (selected score seed rest initial round) bits)) seed rest)
    simp only [selected, iter_succ_apply, payloadNext, List.map_cons, slots, List.sum_cons,
      Nat.add_mul, Nat.one_mul] at *
    omega

theorem selected_rows {α : Type*} (decode : List Bool → List α)
    (score : Records → List Bool → List Bool) (seed : List Bool) (rest initial : Records)
    (D P round : ℕ) (hinitial : ∀ bits ∈ initial, (decode bits).length ≤ D)
    (hfamily : ∀ bits ∈ seed :: rest, (decode bits).length ≤ P) :
    ∀ row ∈ (selected score seed rest initial round).map decode, row.length ≤ D + P + 1 := by
  induction round with
  | zero =>
    intro row hr
    obtain ⟨bits, hb, rfl⟩ := List.mem_map.mp hr
    have hh := hinitial bits hb
    omega
  | succ round ih =>
    intro row hr
    simp only [selected, iter_succ_apply, payloadNext, List.map_cons, List.mem_cons] at hr
    rcases hr with rfl | hr
    · have hh := hfamily _ (HashSelect.best_mem
        (fun bits => BinaryArithmetic.toNat (score (selected score seed rest initial round) bits)) seed rest)
      dsimp only [selected] at hh
      omega
    · exact ih row hr

abbrev trial {α : Type*} (decode : List Bool → List α)
    (score : Records → List Bool → List Bool) (seed : List Bool) (rest initial : Records)
    (round : ℕ) (bits : List Bool) :=
  (bits :: selected score seed rest initial round).map decode

theorem trial_resources {α : Type*} (decode : List Bool → List α)
    (score : Records → List Bool → List Bool) (seed : List Bool) (rest initial : Records)
    (D P round : ℕ) (hinitial : ∀ bits ∈ initial, (decode bits).length ≤ D)
    (hfamily : ∀ bits ∈ seed :: rest, (decode bits).length ≤ P)
    (bits : List Bool) (hb : bits ∈ seed :: rest) :
    (trial decode score seed rest initial round bits).length = initial.length + round + 1 ∧
    slots (trial decode score seed rest initial round bits) ≤ slots (initial.map decode) + (round + 1) * P ∧
    ∀ row ∈ trial decode score seed rest initial round bits, row.length ≤ D + P + 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [trial, selected_length]
  · have hs := selected_slots decode score seed rest initial P round hfamily
    have hh := hfamily bits hb
    simp only [trial, List.map_cons, slots, List.sum_cons, Nat.add_mul, Nat.one_mul] at *
    omega
  · intro row hr
    simp only [trial, List.map_cons, List.mem_cons] at hr
    rcases hr with rfl | hr
    · have hh := hfamily bits hb
      omega
    · exact selected_rows decode score seed rest initial D P round hinitial hfamily row hr

/-- The actual supplied code-row table plus the actual selector trial and optional
marked clause. All assumptions concern runtime parsing or input width. -/
theorem supplied_trial (n B t d k round : ℕ) (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ) (hcodes : ∀ i, (codes i).length ≤ k)
    (s : SparseCode.SuppliedShifts clauses.length B)
    (Q : SparseCode.SuppliedLocal clauses.length B)
    (decode : List Bool → List (Fin clauses.length × ZMod 3))
    (score : Records → List Bool → List Bool) (seed : List Bool) (rest initial : Records)
    (hdecode : initial.map decode = CodeRowsProgram.serializedRows clauses.length s Q)
    (hfamily : ∀ bits ∈ seed :: rest, (decode bits).length ≤ SparseCode.distanceDenom clauses.length B)
    (bits : List Bool) (hb : bits ∈ seed :: rest) (mark : Option (Fin clauses.length))
    (hn : 0 < n) (hm : 0 < clauses.length) (hB : 0 < B) (hmb : clauses.length ≤ n * B) :
    let rows := trial decode score seed rest initial round bits
    let scopes := HashScopeProgram.Complete.scopes t d codes rows mark
    scopes.length ≤ 3 * n + round + 2 ∧
    slots scopes ≤ (3 * n * SparseCode.degreeBound clauses.length B +
      (round + 1) * SparseCode.distanceDenom clauses.length B + 1) * k ∧
    ∀ row ∈ scopes, row.length ≤
      (SparseCode.degreeBound clauses.length B + SparseCode.distanceDenom clauses.length B + 1) * k := by
  have hi : ∀ bits ∈ initial, (decode bits).length ≤ SparseCode.degreeBound clauses.length B := by
    intro bits hb
    apply CodeRowsProgram.serializedRows_supplied_slots s Q
    rw [← hdecode]
    exact List.mem_map.mpr ⟨bits,hb,rfl⟩
  obtain ⟨hl,hs,ha⟩ := trial_resources decode score seed rest initial
    (SparseCode.degreeBound clauses.length B) (SparseCode.distanceDenom clauses.length B) round hi hfamily bits hb
  have hlen : initial.length ≤ 3*n := by
    have hh := SparseCode.totalRows_le hn hm hB hmb
    have he : initial.length = SparseCode.totalRows clauses.length B := by
      simpa [CodeRowsProgram.serializedRows_supplied_length] using congrArg List.length hdecode
    exact he.le.trans hh
  have hslots : slots (initial.map decode) ≤ 3*n*SparseCode.degreeBound clauses.length B := by
    rw [hdecode]
    exact (supplied_slots s Q).trans (Nat.mul_le_mul_right _ (SparseCode.totalRows_le hn hm hB hmb))
  have hmark : mark.isSome.toNat ≤ 1 := by cases mark <;> simp
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [HashScopeProgram.Complete.scopes_length, hl]
    omega
  · apply (scope_mass t d k codes hcodes _ mark).trans
    apply Nat.mul_le_mul_right
    omega
  · exact scope_arity t d k _ codes hcodes _ mark ha (by omega)

end SubexponentialSAT.SqrtLog.LeafScopeResourceBounds

end OAI.Algorithms
