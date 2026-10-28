import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BinaryArgmin
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectArgmin

namespace OAI.Algorithms

/-!
# A measured binary argmin scan with a paid loader

`LoaderSpec` is a refinement obligation on a fixed, executable command. It
requires an actual `StructuredCalls.Eval` for every callback, including the
final empty callback; it is not an oracle or an instruction for evaluating a
mathematical score. A caller may satisfy it by parsing prepared records or by
enumerating candidates and executing a score program. The incumbent score is
cached. Its first evaluation and the preparation of the initial incumbent are
outside this scan and must be charged by the caller.
-/

namespace SubexponentialSAT.SqrtLog.BinaryArgmin

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def Fits (B C : ℕ) (a : Entry) : Prop :=
  a.score.length = B ∧ a.payload.length ≤ C

theorem pick_fits {B C : ℕ} {best next : Entry}
    (hb : Fits B C best) (hn : Fits B C next) : Fits B C (pick best next) := by
  unfold pick
  split_ifs <;> assumption

/-- This supplies both the callback implementation and its paid trace. The
single queue stack can encode arbitrary loader context. All other ports are
explicitly framed. The callback must work with every incumbent and register
contents satisfying the bit bounds. -/
structure LoaderSpec (load : Cmd 8 9) (encode : List Entry → List Bool)
    (B C cost : ℕ) : Prop where
  nil : ∀ best regs, Fits B C best →
    ∃ n ≤ cost, ∃ regs', regs' 7 = false ∧
      Eval load n (data regs empty best (encode []))
        (data regs' empty best (encode []))
  cons : ∀ next rest best regs,
    Fits B C best → Fits B C next → (∀ a ∈ rest, Fits B C a) →
    ∃ n ≤ cost, ∃ regs', regs' 7 = true ∧
      Eval load n (data regs empty best (encode (next :: rest)))
        (data regs' next best (encode rest))

/-- The command is fixed independently of score widths and candidate counts. -/
abbrev scanCommand (load : Cmd 8 9) : Cmd 8 9 :=
  .seq load (.while 7 (.seq update load))

def scanBudget (B C cost count : ℕ) : ℕ :=
  cost * (count + 1) + (100 * (B + C + 1) + 1) * count + 1

/-- Exact semantic refinement of the numerical argmin of `HashSelect`. The
cost includes all losing candidates, all score copies, and the terminal load. -/
theorem scan_eval (load : Cmd 8 9) (encode : List Entry → List Bool)
    (B C cost : ℕ) (hload : LoaderSpec load encode B C cost)
    (seed : Entry) (entries : List Entry) (regs : Fin 8 → Bool)
    (hs : Fits B C seed) (hentries : ∀ a ∈ entries, Fits B C a) :
    ∃ n ≤ scanBudget B C cost entries.length, ∃ regs', regs' 7 = false ∧
      Eval (scanCommand load) n (data regs empty seed (encode entries))
        (data regs' empty (HashSelect.best value seed entries) (encode [])) := by
  induction entries generalizing seed regs with
  | nil =>
    obtain ⟨n, hn, regs', hf, ht⟩ := hload.nil seed regs hs
    refine ⟨n + 1, ?_, regs', hf, ?_⟩
    · simp [scanBudget]; omega
    · exact Eval.seq ht (Eval.while_false hf)
  | cons next rest ih =>
    have hn : Fits B C next := hentries next (by simp)
    have hr : ∀ a ∈ rest, Fits B C a := fun a ha => hentries a (by simp [ha])
    obtain ⟨l, hl, r₁, htrue, hread⟩ := hload.cons next rest seed regs hs hn hr
    obtain ⟨u, hu, r₂, hupdate⟩ := update_eval B C next seed (encode rest) r₁
      hn.1 hs.1 hn.2 hs.2
    obtain ⟨t, ht, r₃, hfalse, htail⟩ := ih (pick seed next) r₂ (pick_fits hs hn) hr
    cases htail with
    | seq hnext hloop =>
      rename_i n m middle
      refine ⟨l + (u + n + m + 1), ?_, r₃, hfalse, ?_⟩
      · simp only [scanBudget, List.length_cons] at ht ⊢
        nlinarith
      · change Eval (.seq load (.while 7 (.seq update load))) _ _ _
        simpa only [HashSelect.best, pick] using
          Eval.seq hread (Eval.while_true htrue (Eval.seq hupdate hnext) hloop)

theorem scanBudget_linear (B C cost count : ℕ) :
    scanBudget B C cost count ≤ (count + 1) * (cost + 100 * (B + C + 1) + 1) := by
  unfold scanBudget
  nlinarith

/-- One fixed finite instruction table for each supplied loader command. -/
abbrev program (load : Cmd 8 9) := compiled (scanCommand load) 8 2

/-- The refinement above gives a genuine halted `BitProgram` trace. -/
theorem program_trace (load : Cmd 8 9) (encode : List Entry → List Bool)
    (B C cost : ℕ) (hload : LoaderSpec load encode B C cost)
    (seed : Entry) (entries : List Entry) (regs : Fin 8 → Bool)
    (hs : Fits B C seed) (hentries : ∀ a ∈ entries, Fits B C a) :
    ∃ n ≤ scanBudget B C cost entries.length + 1, ∃ regs',
      Trace (program load) n
        ((data regs empty seed (encode entries)).withPC (some (program load).entry))
        ((data regs' empty (HashSelect.best value seed entries) (encode [])).withPC none) := by
  obtain ⟨n, hn, regs', _, ht⟩ := scan_eval load encode B C cost hload seed entries regs hs hentries
  exact ⟨n + 1, Nat.add_le_add_right hn 1, regs', compiled_halt_trace ht 8 2⟩

/-- The returned payload belongs to the supplied list, and its binary numeric
score is at most the score of every supplied candidate. -/
theorem selected_spec (seed : Entry) (entries : List Entry) :
    HashSelect.best value seed entries ∈ seed :: entries ∧
      ∀ a ∈ seed :: entries, value (HashSelect.best value seed entries) ≤ value a := by
  refine ⟨HashSelect.best_mem value seed entries, ?_⟩
  intro a ha
  rcases List.mem_cons.mp ha with h | ha
  · subst a
    exact HashSelect.best_le_seed value seed entries
  · exact HashSelect.best_le_member value seed entries a ha

end SubexponentialSAT.SqrtLog.BinaryArgmin

end OAI.Algorithms
