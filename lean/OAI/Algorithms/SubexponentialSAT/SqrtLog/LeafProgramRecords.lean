import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.RecordPrograms

namespace OAI.Algorithms

/-!
# Measured physical folds over sparse-hash records

This module specializes the audited framed-record iterator to an accumulator
fold which visits every record. The callback is an actual finite `Cmd`; its
local execution contract remains explicit. `foldProgram_run` concerns primitive
Boolean-register/stack transitions, not an operation counter or semantic oracle.
The same program shape handles clause-literal products, sparse weighted sums,
coefficient-array maps, and support-key dictionary scans.
-/

namespace SubexponentialSAT.SqrtLog.LeafProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.RecordPrograms

variable {r s : ℕ} {A : Type*}

def foldEffect (read : State r s → A) (step : List Bool → A → A)
    (bits : List Bool) (before after : State r s) : Prop :=
  read after = step bits (read before)

theorem visits_fold (read : State r s → A) (step : List Bool → A → A)
    {records : List (List Bool)} {before after : State r s}
    (h : Visits (fun _ => false) (foldEffect read step) records before after) :
    read after = records.foldl (fun a bits => step bits a) (read before) := by
  induction h with
  | nil base => rfl
  | hit ht _ => cases ht
  | miss _ he _ ih =>
      simpa only [List.foldl_cons, foldEffect] using ih.trans (congrArg
        (fun a => List.foldl (fun a bits => step bits a) a _) he)

@[simp] theorem unread_false (records : List (List Bool)) (suffix : List Bool) :
    unread (fun _ => false) records suffix = suffix := by
  induction records with
  | nil => rfl
  | cons bits records ih => simpa only [unread, Bool.false_eq_true, ↓reduceIte] using ih

@[simp] theorem any_false (records : List (List Bool)) :
    records.any (fun _ => false) = false := by
  induction records with
  | nil => rfl
  | cons a records ih => simpa only [List.any_cons, Bool.false_or] using ih

abbrev foldCommand (ports : Ports r s) (step : Cmd r s) : Cmd r s :=
  iterate ports step

abbrev foldProgram (ports : Ports r s) (step : Cmd r s) :
    Program r s (size (foldCommand ports step) + 1) :=
  compiled (foldCommand ports step) ports.source ports.source

/-- Local callbacks are required to operate on encoded records only. The
machine must consume the parsed reversed payload and preserve the unread tail.
The accumulator's semantic decoder is used only in the specification. -/
abbrev FoldContract (ports : Ports r s) (callback : Cmd r s)
    (read : State r s → A) (step : List Bool → A → A)
    (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (validPayload : List Bool → Prop) : Prop :=
  CallbackContractWithOn ports callback (fun _ => false) cost invariant
    (foldEffect read step) validPayload

theorem foldCommand_run (ports : Ports r s) (callback : Cmd r s)
    (read : State r s → A) (step : List Bool → A → A)
    (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (validPayload : List Bool → Prop)
    (contract : FoldContract ports callback read step cost invariant validPayload)
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (hrecords : ∀ bits ∈ records, validPayload bits) (hbase : invariant base)
    (v pr f : Bool) :
    ∃ n next, n ≤ 3 + budget cost records ∧ invariant next ∧
      read next = records.foldl (fun a bits => step bits a) (read base) ∧
      Eval (foldCommand ports callback) n
        (state ports base v pr f (Encoding.encodeList id records ++ suffix) [])
        (state ports next false true false suffix []) := by
  obtain ⟨n, next, hn, hnext, hhistory, hrun⟩ :=
    iterate_run_with_on ports callback (fun _ => false) cost invariant
      (foldEffect read step) validPayload contract records suffix base hrecords hbase v pr f
  refine ⟨n, next, hn, hnext, visits_fold read step hhistory, ?_⟩
  simpa [foldCommand] using hrun

/-- The program has a fixed finite instruction table. Its actual trace bound
includes parsing and the final halt; the callback bounds remain explicit. -/
theorem foldProgram_run (ports : Ports r s) (callback : Cmd r s)
    (read : State r s → A) (step : List Bool → A → A)
    (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (validPayload : List Bool → Prop)
    (contract : FoldContract ports callback read step cost invariant validPayload)
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (hrecords : ∀ bits ∈ records, validPayload bits) (hbase : invariant base)
    (v pr f : Bool) :
    ∃ next, invariant next ∧
      read next = records.foldl (fun a bits => step bits a) (read base) ∧
      RunsIn (foldProgram ports callback) (4 + budget cost records)
        ((state ports base v pr f (Encoding.encodeList id records ++ suffix) []).withPC
          (some (foldProgram ports callback).entry))
        ((state ports next false true false suffix []).withPC none) := by
  obtain ⟨n, next, hn, hnext, hvalue, hrun⟩ :=
    foldCommand_run ports callback read step cost invariant validPayload contract
      records suffix base hrecords hbase v pr f
  exact ⟨next, hnext, hvalue, n + 1, by omega,
    compiled_halt_trace hrun ports.source ports.source⟩

/-- An accumulator stored on a separate physical stack is unchanged by the
iterator's bookkeeping wrapper, so the preceding value statement refers to
the actual final machine state as well as its abstract base state. -/
theorem accumulator_stack (ports : Ports r s) (acc : Fin s)
    (hsource : acc ≠ ports.source) (hpayload : acc ≠ ports.payload)
    (base : State r s) (v pr f : Bool) (src payload : List Bool) :
    (state ports base v pr f src payload).stacks acc = base.stacks acc := by
  simp [state, hsource, hpayload]

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
