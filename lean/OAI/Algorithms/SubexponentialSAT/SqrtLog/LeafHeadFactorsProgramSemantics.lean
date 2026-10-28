import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgramRun
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgramSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramController
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingPrefix

namespace OAI.Algorithms

/-! The physical row predicate selects exactly the computed factor colors. -/
namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls MulticolorTypes

def indices (A N : ℕ) : List (Fin A ⊕ Fin N) :=
  Packing.headsFirstIndices (List.finRange A) (List.finRange N)

@[simp] theorem indices_length (A N : ℕ) : (indices A N).length = A + N := by
  simp [indices, Packing.headsFirst_length]

theorem factor_index (A N : ℕ) (f : Fin N) :
    LocalExpectation.indexCode (indices A N) (.inr f) = A + f.val := by
  unfold indices
  rw [Packing.headsFirst_index_factor]
  simp [LocalExpectation.indexCode]

theorem assignNat_length {X : Type*} (a : X) (tail : List X)
    (evaluate : ℕ → List X → ℕ) (n : ℕ) (fixed : List X) :
    (Subexp.NaturalAssignment.assignNat a tail evaluate n fixed).length = n + fixed.length := by
  induction n generalizing fixed with
  | zero => simp [Subexp.NaturalAssignment.assignNat]
  | succ n ih =>
    simp only [Subexp.NaturalAssignment.assignNat, ih, List.length_cons]
    omega

variable {I : Type*} [Fintype I] [DecidableEq I] {A N r Q : ℕ}

/-- Exactly the row list flattened by the existing assignment controller. -/
def sourceRows (owner : I → Fin A) (factor : I → Fin N)
    (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I (Fin A) Q)) (w : PackingProgram.Weights) :
    List (List Bool) :=
  (PackingProgram.selectedValues owner factor a tail terms (indices A N) w).reverse.map
    Subexp.ReadPlan.encodeWord

omit [Fintype I] [DecidableEq I] in
@[simp] theorem sourceRows_length (owner : I → Fin A) (factor : I → Fin N)
    (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I (Fin A) Q)) (w : PackingProgram.Weights) :
    (sourceRows owner factor a tail terms w).length = A + N := by
  simp [sourceRows, PackingProgram.selectedValues, assignNat_length]

omit [Fintype I] [DecidableEq I] in
theorem sourceRows_width (owner : I → Fin A) (factor : I → Fin N)
    (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I (Fin A) Q)) (w : PackingProgram.Weights) :
    ∀ row ∈ sourceRows owner factor a tail terms w, row.length = Q * r := by
  intro row hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  simp [Subexp.ReadPlan.wordWidth]

omit [DecidableEq I] in
theorem computed_predicate (owner : I → Fin A) (factor : I → Fin N)
    (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I (Fin A) Q)) (w : PackingProgram.Weights)
    (x y : ℚ) (hy : y ^ 2 = (w.incidence : ℚ) / w.denominator)
    (hx : x ^ 2 = (w.head : ℚ) / w.denominator)
    (t : Fin Q) (g : Fin r) (f : Fin N) :
    predicate (sourceRows owner factor a tail terms w) A (t.val * r + g.val) f.val =
      decide (Packing.computedWords owner factor a tail terms (indices A N) x y (.inr f) t = g) := by
  let values := PackingProgram.selectedValues owner factor a tail terms (indices A N) w
  have hlen : values.length = A + N := by
    simp [values, PackingProgram.selectedValues, assignNat_length]
  have hlt : A + f.val < values.reverse.length := by
    simpa only [List.length_reverse, hlen] using Nat.add_lt_add_left f.isLt A
  have he := congrFun (PackingProgram.selectedValues_eq_computedWords
    owner factor a tail terms (indices A N) w x y hy hx) (.inr f)
  rw [factor_index, Subexp.AssignmentEnumeration.decode_eq_reverse_getD,
    List.getD_eq_getElem _ _ hlt] at he
  unfold predicate sourceRows
  change ((values.reverse.map Subexp.ReadPlan.encodeWord).getD (A + f.val) []).getD
    (t.val * r + g.val) false = _
  have hrow : (values.reverse.map Subexp.ReadPlan.encodeWord).getD (A + f.val) [] =
      Subexp.ReadPlan.encodeWord values.reverse[A + f.val] := by
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hlt), List.getElem_map]
  rw [hrow, HeadIdentifierProgram.encodeWord_getD, he]

omit [DecidableEq I] in
theorem computed_chosen_mem (owner : I → Fin A) (factor : I → Fin N)
    (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I (Fin A) Q)) (w : PackingProgram.Weights)
    (x y : ℚ) (hy : y ^ 2 = (w.incidence : ℚ) / w.denominator)
    (hx : x ^ 2 = (w.head : ℚ) / w.denominator)
    (t : Fin Q) (g : Fin r) (f : Fin N) :
    f.val ∈ chosenIds (predicate (sourceRows owner factor a tail terms w) A
      (t.val * r + g.val)) N ↔
      Packing.computedWords owner factor a tail terms (indices A N) x y (.inr f) t = g := by
  simp [chosenIds, f.isLt, computed_predicate owner factor a tail terms w x y hy hx t g f]

omit [Fintype I] [DecidableEq I] in
/-- This runs on the actual controller bytes, not on a supplied set of factors. -/
theorem computed_program_runsIn (regs : Fin 16 → Bool)
    (owner : I → Fin A) (factor : I → Fin N) (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I (Fin A) Q)) (w : PackingProgram.Weights)
    (t : Fin Q) (g : Fin r) :
    RunsIn program (budget A N (A + N) (Q * r) (t.val * r + g.val))
      ((input regs (sourceRows owner factor a tail terms w) A N (Q * r)
        (t.val * r + g.val)).withPC (some program.entry))
      ((result (sourceRows owner factor a tail terms w) A N (Q * r)
        (t.val * r + g.val)).withPC none) := by
  simpa only [sourceRows_length] using program_runsIn regs
    (sourceRows owner factor a tail terms w) A N (Q * r) (t.val * r + g.val)
    (sourceRows_width owner factor a tail terms w) (by simp)

theorem chosenIds_bound (p : ℕ → Bool) (N : ℕ) : ∀ f ∈ chosenIds p N, f < N := by
  intro f hf
  exact List.mem_range.mp (List.mem_of_mem_filter hf)

theorem chosenIds_nodup (p : ℕ → Bool) (N : ℕ) : (chosenIds p N).Nodup :=
  (show (List.range N).Nodup from List.nodup_range).filter p

theorem encodedIds_length_bound (p : ℕ → Bool) (N : ℕ) :
    (ProgramEncoding.encodeRecords ((chosenIds p N).map Encoding.encodeNat)).length ≤
      1 + (2 * N + 2) * N := by
  have h := ProgramEncoding.encodeRecords_length_le
    ((chosenIds p N).map Encoding.encodeNat) N (by
      intro payload hp
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hp
      simpa using Nat.succ_le_of_lt (chosenIds_bound p N f hf))
  have hc : (chosenIds p N).length ≤ N := by
    simpa [chosenIds] using List.length_filter_le p (List.range N)
  simp only [List.length_map] at h
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hc) 1)

/-- The result payload ABI uses terminated unary natural encodings. -/
theorem output_abi (rows : List (List Bool)) (A N W z : ℕ) :
    (result rows A N W z).stacks 0 = ProgramEncoding.encodeRecords
      ((chosenIds (predicate rows A z) N).map Encoding.encodeNat) := rfl

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
