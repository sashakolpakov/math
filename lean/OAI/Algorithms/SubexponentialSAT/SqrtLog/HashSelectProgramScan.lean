import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgramCore

namespace OAI.Algorithms

/-! Measured enumeration and binary argmin over unevaluated payloads. The mass
callback is fixed executable syntax and must provide a trace for each payload.
The loop therefore charges every losing candidate as well as the winner. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

variable {r s : ℕ}

def scored (score : List Bool → List Bool) (bits : List Bool) : Entry := ⟨bits, score bits⟩

/-- The caller's exact mass program can use all extra banks but restores them
at this boundary. `frame` includes the encoded current matrix and leaf. -/
abbrev MassSpec (mass : Cmd r s) (p : Ports r s) (frame : State r s)
    (score : List Bool → List Bool) (valid : List Bool → Prop) (_B _C cost : ℕ) : Prop :=
  ∀ bits best queue regs, valid bits →
    ∃ n ≤ cost, ∃ regs',
      Eval mass n (state p frame regs ⟨bits, []⟩ best queue)
        (state p frame regs' (scored score bits) best queue)

def flagProgram := compiled (BinaryArgmin.atom (.set 7 true)) 8 0

abbrev flag (p : Ports r s) : Cmd r s :=
  .call (ProgramLinking.liftProgram flagProgram p.register p.stack)

theorem flag_eval (p : Ports r s) (frame : State r s) (regs : Fin 8 → Bool)
    (next best : Entry) (queue : List Bool) :
    Eval (flag p) 2 (state p frame regs next best queue)
      (state p frame (Function.update regs 7 true) next best queue) := by
  have h : Eval (BinaryArgmin.atom (.set 7 true)) 1
      (BinaryArgmin.data regs next best queue)
      (BinaryArgmin.data (Function.update regs 7 true) next best queue) :=
    .base (.atom _ _)
  exact eval_call_lifted flagProgram p.register p.stack frame
    p.register_injective p.stack_injective (compiled_halt_trace h 8 0)

/-- Only the payload parser runs at end of input. Scores come from `mass`. -/
abbrev load (p : Ports r s) (mass : Cmd r s) : Cmd r s :=
  .seq (parse p) (.ite (p.register 7) (.seq mass (flag p)) (.base .skip))

def loadBudget (C cost : ℕ) : ℕ := 6 * C + cost + 10

theorem load_nil (p : Ports r s) (mass : Cmd r s) (frame : State r s)
    (best : Entry) (regs : Fin 8 → Bool) :
    ∃ regs', regs' 7 = false ∧
      Eval (load p mass) 4 (state p frame regs BinaryArgmin.empty best [false])
        (state p frame regs' BinaryArgmin.empty best []) := by
  obtain ⟨regs', hf, ht⟩ := parse_nil p frame best regs
  refine ⟨regs', hf, ?_⟩
  exact Eval.seq ht (Eval.ite_false (by simpa using hf) (Eval.base (.skip _)))

theorem load_cons (p : Ports r s) (mass : Cmd r s) (frame : State r s)
    (score : List Bool → List Bool) (valid : List Bool → Prop) (B C cost : ℕ)
    (hmass : MassSpec mass p frame score valid B C cost)
    (bits : List Bool) (rest : List (List Bool)) (best : Entry) (regs : Fin 8 → Bool)
    (hv : valid bits) (hlen : bits.length ≤ C) :
    ∃ n ≤ loadBudget C cost, ∃ regs', regs' 7 = true ∧
      Eval (load p mass) n
        (state p frame regs BinaryArgmin.empty best (candidateEncoding (bits :: rest)))
        (state p frame regs' (scored score bits) best (candidateEncoding rest)) := by
  obtain ⟨regs₁, ht, hp⟩ := parse_cons p frame bits rest best regs
  obtain ⟨n, hn, regs₂, he⟩ := hmass bits best (candidateEncoding rest) regs₁ hv
  refine ⟨(6 * bits.length + 7) + ((n + 2) + 1), ?_,
    Function.update regs₂ 7 true, by simp, ?_⟩
  · unfold loadBudget; omega
  · exact Eval.seq hp (Eval.ite_true (by simpa using ht)
      (Eval.seq he (flag_eval p frame regs₂ _ best _)))

/-- Control size does not depend on candidate count, score width or tuple depth. -/
abbrev scan (p : Ports r s) (mass : Cmd r s) : Cmd r s :=
  .seq (load p mass) (.while (p.register 7) (.seq (update p) (load p mass)))

def scanBudget (B C cost count : ℕ) : ℕ :=
  loadBudget C cost * (count + 1) + (100 * (B + C + 1) + 2) * count + 1

theorem scan_eval (p : Ports r s) (mass : Cmd r s) (frame : State r s)
    (score : List Bool → List Bool) (valid : List Bool → Prop) (B C cost : ℕ)
    (hmass : MassSpec mass p frame score valid B C cost)
    (seed : Entry) (payloads : List (List Bool)) (regs : Fin 8 → Bool)
    (hs : BinaryArgmin.Fits B C seed)
    (hp : ∀ bits ∈ payloads, valid bits ∧ bits.length ≤ C ∧ (score bits).length = B) :
    ∃ n ≤ scanBudget B C cost payloads.length, ∃ regs', regs' 7 = false ∧
      Eval (scan p mass) n
        (state p frame regs BinaryArgmin.empty seed (candidateEncoding payloads))
        (state p frame regs' BinaryArgmin.empty
          (HashSelect.best BinaryArgmin.value seed (payloads.map (scored score))) []) := by
  induction payloads generalizing seed regs with
  | nil =>
    obtain ⟨regs', hf, ht⟩ := load_nil p mass frame seed regs
    refine ⟨5, ?_, regs', hf, ?_⟩
    · simp [scanBudget, loadBudget]
    · exact Eval.seq ht (Eval.while_false (by simpa using hf))
  | cons bits rest ih =>
    have hb := hp bits (by simp)
    have hrest : ∀ b ∈ rest, valid b ∧ b.length ≤ C ∧ (score b).length = B :=
      fun b h => hp b (by simp [h])
    have hfit : BinaryArgmin.Fits B C (scored score bits) := ⟨hb.2.2, hb.2.1⟩
    obtain ⟨l, hl, regs₁, ht, he⟩ := load_cons p mass frame score valid B C cost
      hmass bits rest seed regs hb.1 hb.2.1
    obtain ⟨u, hu, regs₂, he₂⟩ := update_eval p frame B C (scored score bits) seed
      (candidateEncoding rest) regs₁ hfit hs
    obtain ⟨t, ht', regs₃, hf, he₃⟩ := ih (BinaryArgmin.pick seed (scored score bits))
      regs₂ (BinaryArgmin.pick_fits hs hfit) hrest
    cases he₃ with
    | @seq first second a b x y z hnext hloop =>
      refine ⟨l + (u + a + b + 1), ?_, regs₃, hf, ?_⟩
      · simp only [scanBudget, List.length_cons] at ht' ⊢
        nlinarith
      · change Eval (.seq (load p mass) (.while (p.register 7)
          (.seq (update p) (load p mass)))) _ _ _
        simpa only [List.map_cons, HashSelect.best, BinaryArgmin.pick] using
          Eval.seq he (Eval.while_true (by simpa using ht) (Eval.seq he₂ hnext) hloop)

theorem scanBudget_linear (B C cost count : ℕ) :
    scanBudget B C cost count ≤
      (count + 1) * (loadBudget C cost + 100 * (B + C + 1) + 2) := by
  unfold scanBudget
  nlinarith

abbrev scanProgram (p : Ports r s) (mass : Cmd r s) :=
  compiled (scan p mass) (p.stack 8) (p.stack 2)

theorem scanProgram_trace (p : Ports r s) (mass : Cmd r s) (frame : State r s)
    (score : List Bool → List Bool) (valid : List Bool → Prop) (B C cost : ℕ)
    (hmass : MassSpec mass p frame score valid B C cost)
    (seed : Entry) (payloads : List (List Bool)) (regs : Fin 8 → Bool)
    (hs : BinaryArgmin.Fits B C seed)
    (hp : ∀ bits ∈ payloads, valid bits ∧ bits.length ≤ C ∧ (score bits).length = B) :
    ∃ n ≤ scanBudget B C cost payloads.length + 1, ∃ regs',
      Trace (scanProgram p mass) n
        ((state p frame regs BinaryArgmin.empty seed (candidateEncoding payloads)).withPC
          (some (scanProgram p mass).entry))
        ((state p frame regs' BinaryArgmin.empty
          (HashSelect.best BinaryArgmin.value seed (payloads.map (scored score))) []).withPC none) := by
  obtain ⟨n, hn, regs', _, ht⟩ := scan_eval p mass frame score valid B C cost
    hmass seed payloads regs hs hp
  exact ⟨n + 1, Nat.add_le_add_right hn 1, regs', compiled_halt_trace ht _ _⟩

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
