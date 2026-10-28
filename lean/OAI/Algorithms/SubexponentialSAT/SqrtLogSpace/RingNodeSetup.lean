import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace

/-! Paid traversal of the actual framed node table. The remaining cursor and
unary index are physical stacks, and the decoded node is transferred to the
original factor port. No list of semantic nodes is manufactured by the machine. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeSetup

open OAI BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram

/-- Project every named field without changing any other caller stack. -/
def storeOf (a : Data) : Store where
  frame := a.stacks
  source := a.stacks 301
  payload := a.stacks 302
  nodesRev := a.stacks 303
  jetsRev := a.stacks 304
  temporary := a.stacks 305
  index := a.stacks 307
  node := a.stacks 78
  jet := a.stacks 102
  shape := a.stacks 104
  nodesOut := a.stacks 256
  jetsOut := a.stacks 265

theorem state_storeOf (a : Data) : state a.regs (storeOf a) = a := by
  have hs : tapes (storeOf a) = a.stacks := by
    funext i
    have choose (j : Fin 768) {tail : List Bool} (ht : tail = a.stacks i) :
        (if i = j then a.stacks j else tail) = a.stacks i := by
      split
      · rename_i h
        exact congrArg a.stacks h.symm
      · exact ht
    unfold tapes
    apply choose 301
    apply choose 302
    apply choose 303
    apply choose 304
    apply choose 305
    apply choose 307
    apply choose 78
    apply choose 102
    apply choose 104
    apply choose 256
    apply choose 265
    rfl
  change ⟨a.regs, tapes (storeOf a)⟩ = a
  rw [hs]

/-- Initial cursor setup includes clearing stale parser buffers and index. -/
def initNodes : Code :=
  .seq (clear 301) (.seq (clear 302) (.seq (clear 305)
    (.seq (clear 307) (.seq (clear 78) (copy 300 301)))))

def initialized (s : Store) : Store :=
  {s with source := s.frame 300, payload := [], temporary := [], index := [], node := []}

def initializeCost (s : Store) : ℕ :=
  2*(s.source.length+s.payload.length+s.temporary.length+s.index.length+s.node.length)+
    7*(s.frame 300).length+20

theorem initialize_eval (regs : Fin 40 → Bool) (s : Store) :
    Eval initNodes (initializeCost s) (state regs s)
      (state (readRegs regs 0 1 none) (initialized s)) := by
  let a := {s with source := []}
  let b := {a with payload := []}
  let c := {b with temporary := []}
  let d := {c with index := []}
  let e := {d with node := []}
  let rr := readRegs regs 0 1 none
  have hrr : readRegs rr 0 1 none = rr := by
    funext i
    by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
      simp [rr, readRegs, h0, h1]
  have h1 := clear_store regs s a 301 (by simp [a])
  have h2 := clear_store rr a b 302 (by simp [b])
  have h3 := clear_store rr b c 305 (by simp [c])
  have h4 := clear_store rr c d 307 (by simp [d])
  have h5 := clear_store rr d e 78 (by simp [e])
  have h6 := copy_store rr e (initialized s) 300 301
    (by decide) (by decide) (by decide) rfl
    (by simp [copyStacks, initialized, e, d, c, b, a, tapes])
  rw [hrr] at h2 h3 h4 h5 h6
  convert h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6)))) using 1
  · simp [initNodes]
  · simp [initializeCost, a, b, c, d, e, tapes]
    omega

/-- Consume one outer list tag, read its frame, and put the whole node at78. -/
def readNode : Code := .seq pop (.seq reader (transfer 302 78))

def nodeRead (s : Store) (bits : List Bool) (tail : List (List Bool)) : Store :=
  {s with source := Encoding.encodeList id tail, payload := [], node := bits}

def nodeRegs (regs : Fin 40 → Bool) : Fin 40 → Bool :=
  readRegs (parserRegs regs false true (regs 39)) 0 1 none

theorem readNode_eval (regs : Fin 40 → Bool) (s : Store)
    (bits : List Bool) (tail : List (List Bool))
    (hs : s.source = Encoding.encodeList id (bits :: tail))
    (hp : s.payload = []) (hn : s.node = []) :
    Eval readNode (9*bits.length+8) (state regs s)
      (state (nodeRegs regs) (nodeRead s bits tail)) := by
  let a := {s with source := Encoding.frame bits ++ Encoding.encodeList id tail}
  let b := {s with source := Encoding.encodeList id tail, payload := bits.reverse}
  let r1 := parserRegs regs true true (regs 39)
  let r2 := parserRegs regs false true (regs 39)
  have h1 := pop_store regs s true a.source (by simpa [Encoding.encodeList, a] using hs)
  have h2 := reader_store r1 a bits (Encoding.encodeList id tail) rfl hp
  have hr : parserRegs r1 false true (r1 39) = r2 := by
    funext i
    by_cases h37 : i = 37 <;> by_cases h38 : i = 38 <;> by_cases h39 : i = 39 <;>
      simp [r1, r2, parserRegs, h37, h38, h39]
  have h3 := transfer_store r2 b (nodeRead s bits tail) 302 78 (by decide)
    (by simp [transferStacks, b, nodeRead, hn])
  rw [hr] at h2
  convert h1.seq (h2.seq h3) using 1
  · simp [readNode]
  · simp [b, tapes]
    omega
  · simp [r2, nodeRegs]

/-- The supplied native index advance is two real instructions. -/
theorem advance_eval (regs : Fin 40 → Bool) (s : Store) :
    Eval increment 2 (state regs s)
      (state (Function.update regs 0 true) {s with index := true :: s.index}) :=
  increment_store regs s

/-- The node reader has no hidden persistent writes. -/
theorem nodeRead_frame (s : Store) (bits : List Bool) (tail : List (List Bool))
    (i : Fin 768) (h301 : i ≠ 301) (h302 : i ≠ 302) (h78 : i ≠ 78) :
    tapes (nodeRead s bits tail) i = tapes s i := by
  simp [nodeRead, tapes, h301, h302, h78]

/-- A fixed entry bound is restored at the reader boundary. Its temporary
prefix bound must not be fed back as the next node's entry bound. -/
theorem nodeRead_boundary (s : Store) (bits : List Bool) (tail : List (List Bool))
    (B : ℕ) (hentry : ∀ i, (tapes s i).length ≤ B)
    (hbits : bits.length ≤ B) (htail : (Encoding.encodeList id tail).length ≤ B) :
    ∀ i, (tapes (nodeRead s bits tail) i).length ≤ B := by
  intro i
  by_cases h301 : i = 301
  · subst i; simpa [nodeRead] using htail
  by_cases h302 : i = 302
  · subst i; simp [nodeRead]
  by_cases h78 : i = 78
  · subst i; simpa [nodeRead] using hbits
  rw [nodeRead_frame s bits tail i h301 h302 h78]
  exact hentry i

/-- Each local loader trace bounds all stacks and includes the compiled halt.
The caller must restore a fixed boundary between nodes; this lemma does not
charge all completed node invocations as live storage. -/
theorem eval_resources {cmd : Code} {steps : ℕ} {a b : Data}
    (he : Eval cmd steps a b) (input output : Fin 768) :
    Trace (compiled cmd input output) (steps+1)
      (a.withPC (some (compiled cmd input output).entry)) (b.withPC none) ∧
    ∀ prefixSteps intermediate, prefixSteps ≤ steps+1 →
      Trace (compiled cmd input output) prefixSteps
        (a.withPC (some (compiled cmd input output).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ stackBits a.stacks+steps := by
  refine ⟨compiled_halt_trace he input output, ?_⟩
  apply StructuredSpace.compiled_halt_stack_bound he input output
  intro prefixSteps intermediate hprefix hp
  exact StructuredSpace.local_stack_bound _ (by rfl) prefixSteps intermediate hprefix hp

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeSetup
