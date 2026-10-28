import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram

namespace OAI.Algorithms

/-! Relational execution contracts for the unchanged node collector. Each call
may return different valid bytes; only its actual result is appended. -/
namespace SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.Rel
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

/-- Existential output bytes are selected by the actual worker execution. -/
def WorkerContract (worker : Code) (Valid : (Fin 768 → List Bool) → Prop)
    (nodes : ℕ → List Bool) (Result : ℕ → List Bool → Prop)
    (cost : ℕ → ℕ) (maxJet Q : ℕ) : Prop :=
  ∀ i < Q, ∀ (regs : Fin 40 → Bool) (s : Store), Valid s.frame →
    s.index = List.replicate i true → s.node = nodes i →
    s.jet = [] → s.shape = [] →
    ∃ jet, Result i jet ∧ jet.length ≤ maxJet ∧
      ∃ time ≤ cost i, ∃ rr, RegFrame regs rr ∧
        Eval worker time (state regs s)
          (state rr {s with node := [],jet := jet,shape := []})

def good (Result : ℕ → List Bool → Prop) (maxJet i : ℕ) (jet : List Bool) : Prop :=
  Result i jet ∧ jet.length ≤ maxJet

def nodeSamples (nodes : ℕ → List Bool) (i : ℕ) : Sample :=
  {node := nodes i, jet := [], cost := 0}

def advanceResult (s : Store) (nodes : ℕ → List Bool) (i : ℕ) (jet : List Bool) : Store :=
  advance s {node := nodes i, jet := jet, cost := 0}

def callbackBound (nodes : ℕ → List Bool) (cost : ℕ → ℕ) (maxJet i : ℕ) : ℕ :=
  cost i+10*(nodes i).length+3*maxJet+16

theorem callback_eval (worker : Code) (Valid : (Fin 768 → List Bool) → Prop)
    (nodes : ℕ → List Bool) (Result : ℕ → List Bool → Prop)
    (cost : ℕ → ℕ) (maxJet Q i : ℕ)
    (contract : WorkerContract worker Valid nodes Result cost maxJet Q) (hi : i < Q)
    (regs : Fin 40 → Bool) (s : Store) (hv : Valid s.frame)
    (hx : s.index = List.replicate i true) (hp : s.payload = (nodes i).reverse)
    (hn : s.node = []) (hj : s.jet = []) (hs : s.shape = [])
    (ht : s.temporary = []) :
    ∃ jet, good Result maxJet i jet ∧
      ∃ time ≤ callbackBound nodes cost maxJet i, ∃ rr,
        RegFrame regs rr ∧ Eval (callback worker) time (state regs s)
          (state rr {advanceResult s nodes i jet with payload := []}) := by
  let a := {s with nodesRev := (nodes i).reverse ++ s.nodesRev}
  let b := {a with payload := [],node := nodes i}
  let r1 := readRegs regs 0 1 none
  let r2 := readRegs r1 0 1 none
  have h1 := copy_store regs s a 302 303 (by decide) (by decide) (by decide) ht
    (by simp [copyStacks,hp,a])
  have h2 := transfer_store r1 a b 302 78 (by decide)
    (by simp [transferStacks,a,b,hp,hn])
  obtain ⟨jet,hresult,hjlen,time,hbound,r3,hframe,h3⟩ := contract i hi r2 b hv
    (by simpa [b,a] using hx) rfl (by simpa [b,a] using hj) (by simpa [b,a] using hs)
  let c := {b with node := [],jet := jet,shape := []}
  let d := {c with jet := [],jetsRev := jet.reverse ++ s.jetsRev}
  let e := {d with shape := []}
  let r4 := readRegs r3 0 1 none
  let r5 := readRegs r4 0 1 none
  have h4 := transfer_store r3 c d 102 304 (by decide)
    (by simp [transferStacks,c,d,b,a])
  have h5 := clear_store r4 d e 104 (by simp [e])
  have h6 := increment_store r5 e
  refine ⟨jet,⟨hresult,hjlen⟩,
    7*(tapes s 302).length+5+(3*(tapes a 302).length+3+
      (time+(3*(tapes c 102).length+3+(2*(tapes d 104).length+3+2)))),
      ?_,Function.update r5 0 true,?_,?_⟩
  · simp only [callbackBound,tapes_payload,tapes_jet,tapes_shape,hp,List.length_reverse]
    dsimp [a,b,c,d]
    simp only [hp,List.length_reverse]
    omega
  · exact (readRegs_frame regs).trans ((readRegs_frame r1).trans
      (hframe.trans ((readRegs_frame r3).trans
        ((readRegs_frame r4).trans (update_zero_frame r5 true)))))
  · have he := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))
    simpa [callback,advanceResult,advance,a,b,c,d,e,hn,hj,hs] using he

def loopBound (nodes : ℕ → List Bool) (cost : ℕ → ℕ) (maxJet start : ℕ) : ℕ → ℕ
  | 0 => 1
  | count+1 => 6*(nodes start).length + callbackBound nodes cost maxJet start +
      6 + loopBound nodes cost maxJet (start+1) count

def finishLoop (s : Store) (nodes : ℕ → List Bool) (start : ℕ) : List (List Bool) → Store
  | [] => {s with source := [],payload := []}
  | jet :: jets => finishLoop (advanceResult s nodes start jet) nodes (start+1) jets

theorem finishLoop_eq (s : Store) (nodes : ℕ → List Bool) (start : ℕ)
    (jets : List (List Bool)) :
    finishLoop s nodes start jets =
      {s with source := [],payload := [],index := List.replicate jets.length true ++ s.index, nodesRev := (records (nodeSamples nodes) start jets.length).flatten.reverse ++ s.nodesRev, jetsRev := jets.flatten.reverse ++ s.jetsRev} := by
  induction jets generalizing start s with
  | nil => simp [finishLoop,records]
  | cons jet jets ih =>
    rw [finishLoop,ih]
    simp [advanceResult,advance,records,nodeSamples,List.reverse_append,List.append_assoc,
      List.replicate_succ]
    calc
      List.replicate jets.length true ++ true :: s.index =
          (List.replicate jets.length true ++ [true]) ++ s.index := by simp [List.append_assoc]
      _ = List.replicate (jets.length+1) true ++ s.index := by rw [List.replicate_succ']
      _ = true :: (List.replicate jets.length true ++ s.index) := by
        simp only [List.replicate_succ,List.cons_append]

end SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.Rel

end OAI.Algorithms
