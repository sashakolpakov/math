import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeSparse
import OAI.Algorithms.SubexponentialSAT.Subexp.SelectorProgram

namespace OAI.Algorithms

/-! A fixed primitive dictionary lookup. Dictionary normalization guarantees
unique keys. All key and coefficient bits are scanned by the existing finite
record program; key width, coefficient width and dictionary length are runtime
data and do not affect the instruction table. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpRecordScan

variable {K C : Type*} [DecidableEq K]

def encodeDictionary (key : K → List Bool) (coeff : C → List Bool)
    (entries : Sparse.Data K C) : List (List Bool × List Bool) :=
  entries.map (fun a => (key a.1, coeff a.2))

private theorem lookup_map_encode (key : K → List Bool) (coeff : C → List Bool)
    (hk : Function.Injective key) (entries : Sparse.Data K C) (k : K) :
    (encodeDictionary key coeff entries).lookup (key k) = (entries.lookup k).map coeff := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
    rcases a with ⟨j,c⟩
    by_cases h : j = k
    · subst j
      simp [encodeDictionary ]
    · have he : key j ≠ key k := fun hh => h (hk hh)
      simp only [encodeDictionary, List.map_cons, List.lookup_cons] at ih ⊢
      simp [ beq_false_of_ne (Ne.symm h),
        beq_false_of_ne he.symm, ih]

section Semantic
variable [AddCommMonoid C]

private theorem fetch_zero_of_not_mem (entries : Sparse.Data K C) (k : K)
    (h : k ∉ Sparse.keys entries) : Sparse.fetch k entries = 0 := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
    rcases a with ⟨j,c⟩
    have hj : j ≠ k := by intro he; subst j; exact h (by simp [Sparse.keys])
    have ht : k ∉ Sparse.keys entries := by
      intro he; exact h (by simp only [Sparse.keys, List.map_cons, List.mem_cons]; exact Or.inr he)
    simp [Sparse.fetch, hj, ih ht]

/-- On a normalized dictionary, mathematical additive fetch is first-match lookup. -/
theorem fetch_eq_lookup (entries : Sparse.Data K C) (k : K)
    (hn : (Sparse.keys entries).Nodup) :
    Sparse.fetch k entries = (entries.lookup k).getD 0 := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
    rcases a with ⟨j,c⟩
    have hh : j ∉ Sparse.keys entries ∧ (Sparse.keys entries).Nodup := by
      simpa [Sparse.keys] using hn
    by_cases h : j = k
    · subst j
      simp [Sparse.fetch, fetch_zero_of_not_mem entries k hh.1]
    · simp [Sparse.fetch, h, List.lookup_cons, beq_false_of_ne (Ne.symm h), ih hh.2]
end Semantic

abbrev lookupRecords := SubexponentialSAT.Subexp.SelectorProgram.rawRecords
abbrev lookupResult := SubexponentialSAT.Subexp.SelectorProgram.framedResult
abbrev lookupBudget := SubexponentialSAT.Subexp.SelectorProgram.scanBudget

abbrev dictionaryLookup : Cmd 5 6 :=
  .seq (.base (.atom (.set 4 false)))
    (.seq SubexponentialSAT.Subexp.SelectorProgram.peek SubexponentialSAT.Subexp.SelectorProgram.scan)

def dictionaryLookupProgram := compiled dictionaryLookup 0 5

theorem dictionaryLookup_eval (query : List Bool)
    (entries : List (List Bool × List Bool)) (regs : Fin 5 → Bool) :
    ∃ n ≤ lookupBudget query entries + 2, ∃ regs' tail,
      Eval dictionaryLookup n
        (recordState regs (lookupRecords entries) [] query.reverse [] [] [])
        (recordState regs' tail [] query.reverse [] [] (lookupResult (entries.lookup query))) ∧
      regs' 4 = (entries.lookup query).isSome := by
  let initRegs := Function.update regs (4 : Fin 5) false
  have hs : Eval (.base (.atom (.set 4 false))) 1
      (recordState regs (lookupRecords entries) [] query.reverse [] [] [])
      (recordState initRegs (lookupRecords entries) [] query.reverse [] [] []) :=
    .base (.atom _ _)
  have hp := SubexponentialSAT.Subexp.SelectorProgram.peek_eval initRegs (lookupRecords entries) query.reverse []
  obtain ⟨n, hn, final, tail, he, hf⟩ :=
    SubexponentialSAT.Subexp.SelectorProgram.scan_eval query entries initRegs (by simp [initRegs])
  exact ⟨1 + (1 + n), by simpa only [lookupBudget] using (show 1 + (1 + n) ≤ SubexponentialSAT.Subexp.SelectorProgram.scanBudget query entries + 2 by omega), final, tail, hs.seq (hp.seq he), hf⟩

/-- Fully encoded lookup, with the semantic option returned on the output stack. -/
theorem dictionaryLookup_encoded (key : K → List Bool) (coeff : C → List Bool)
    (hk : Function.Injective key) (entries : Sparse.Data K C) (k : K)
    (regs : Fin 5 → Bool) :
    ∃ n ≤ lookupBudget (key k) (encodeDictionary key coeff entries) + 3, ∃ regs' tail,
      Trace dictionaryLookupProgram n
        ((recordState regs (lookupRecords (encodeDictionary key coeff entries))
          [] (key k).reverse [] [] []).withPC (some dictionaryLookupProgram.entry))
        ((recordState regs' tail [] (key k).reverse [] []
          (lookupResult ((entries.lookup k).map coeff))).withPC none) := by
  obtain ⟨n, hn, final, tail, he, _⟩ :=
    dictionaryLookup_eval (key k) (encodeDictionary key coeff entries) regs
  refine ⟨n + 1, by omega, final, tail, ?_⟩
  have hh := compiled_halt_trace he 0 5
  rw [lookup_map_encode key coeff hk] at hh
  exact hh

/-- All scan costs, including failed key comparisons, are linear in serialized
key/payload lengths times the number of entries, with explicit query scans. -/
theorem lookupBudget_bound (query : List Bool) (entries : List (List Bool × List Bool))
    (W B : ℕ) (hk : ∀ a ∈ entries, a.1.length ≤ W)
    (hc : ∀ a ∈ entries, a.2.length ≤ B) :
    lookupBudget query entries ≤ entries.length * (17 * W + 9 * query.length + 13 * B + 40) + 1 := by
  induction entries with
  | nil => simp [lookupBudget, SubexponentialSAT.Subexp.SelectorProgram.scanBudget]
  | cons a entries ih =>
    rcases a with ⟨k,c⟩
    have h1 := hk (k,c) (by simp)
    have h2 := hc (k,c) (by simp)
    have h3 := ih (fun a ha => hk a (by simp [ha])) (fun a ha => hc a (by simp [ha]))
    simp only [lookupBudget, SubexponentialSAT.Subexp.SelectorProgram.scanBudget,
      recordCost, List.length_cons] at *
    nlinarith

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
