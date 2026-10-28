import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramRow
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramStream

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

def matrixSuffix {D t : ℕ} (Q : Fin t → Fin D → SparseCode.F3) (i : ℕ) : List Bool :=
  ((List.ofFn fun a => CodeSearchProgram.scalarFrames (List.ofFn (Q a))).drop i).flatten

def checkRows {r D t : ℕ} (m : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r) :
    List (List (Fin m × SparseCode.F3)) := List.ofFn (slots m shifts Q side v)

structure CheckInvariant {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (b i : ℕ) (d : Data) : Prop where
  registers : ∀ j : Fin 16, 12 ≤ j.val → d.regs j=base.regs j
  source : d.stacks 0=matrixSuffix Q i
  output : d.stacks 12=collectedRows b ((checkRows m shifts Q side v).take i) (base.stacks 12)
  other : ∀ j : Fin 64, j≠0 → j≠12 → j≠16 → d.stacks j=base.stacks j

theorem CheckInvariant.popped {r D t m : ℕ} {base : Data} {shifts : Fin D → Cayley.Cube r}
    {Q : Fin t → Fin D → SparseCode.F3} {side : Bool} {v : Cayley.Cube r}
    {b i : ℕ} {d : Data} (h : CheckInvariant (m:=m) base shifts Q side v b i d) :
    CheckInvariant (m:=m) base shifts Q side v b i (UnaryForPrograms.popped rowLoop d) := by
  constructor
  · intro j hj
    have h10 : j≠10 := by intro hne; have hv := congrArg Fin.val hne; change j.val=10 at hv; omega
    have h11 : j≠11 := by intro hne; have hv := congrArg Fin.val hne; change j.val=11 at hv; omega
    simpa [UnaryForPrograms.popped,rowLoop,readRegs,h10,h11] using h.registers j hj
  · simpa [UnaryForPrograms.popped,rowLoop] using h.source
  · simpa [UnaryForPrograms.popped,rowLoop] using h.output
  · intro j h0 h12 h16
    simpa [UnaryForPrograms.popped,rowLoop,h16] using h.other j h0 h12 h16

theorem checkStep_eval {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (b : ℕ) (ready : LocalReady base D m b side v)
    (hs : base.stacks 9=shiftRows (List.ofFn shifts)) (hD : (base.stacks 6).length=D)
    (h1 : base.stacks 1=[]) (h13 : base.stacks 13=[])
    (h14 : base.stacks 14=[]) (h15 : base.stacks 15=[])
    (i : ℕ) (hi : i < t) (d : Data) (inv : CheckInvariant (m:=m) base shifts Q side v b i d) :
    ∃ n e, n ≤ rowCost base D b ∧ Eval rowStep n d e ∧
      e.stacks rowLoop.counter=d.stacks rowLoop.counter ∧
      CheckInvariant (m:=m) base shifts Q side v b (i+1) e := by
  let a : Fin t := ⟨i,hi⟩
  have preserved (j : Fin 64) (h0 : j≠0) (h12 : j≠12) (h16 : j≠16) :
      d.stacks j=base.stacks j := inv.other j h0 h12 h16
  have rd : LocalReady d D m b side v := by
    constructor
    · exact (inv.registers 12 (by decide)).trans ready.mode
    · rw [preserved 2 (by decide) (by decide) (by decide)]; exact ready.vertex
    · rw [preserved 3 (by decide) (by decide) (by decide)]; exact ready.degree
    · rw [preserved 4 (by decide) (by decide) (by decide)]; exact ready.modulus
    · rw [preserved 5 (by decide) (by decide) (by decide)]; exact ready.width
    · exact ready.capacity
    · intro j hj hk
      have h0 : j≠0 := by intro hne; have hv := congrArg Fin.val hne; change j.val=0 at hv; omega
      have h12 : j≠12 := by intro hne; have hv := congrArg Fin.val hne; change j.val=12 at hv; omega
      have h16 : j≠16 := by intro hne; have hv := congrArg Fin.val hne; change j.val=16 at hv; omega
      rw [preserved j h0 h12 h16]; exact ready.work j hj hk
  have source : d.stacks 0=CodeSearchProgram.scalarFrames (List.ofFn (Q a))++matrixSuffix Q (i+1) := by
    rw [inv.source]
    unfold matrixSuffix
    rw [List.drop_eq_getElem_cons (by simpa using hi)]
    simp [a]
  obtain ⟨n,rf,he,hn,hr⟩ := rowStep_eval d shifts Q side v a b (matrixSuffix Q (i+1)) rd source
    (by rw [preserved 9 (by decide) (by decide) (by decide)]; exact hs)
    (by rw [preserved 6 (by decide) (by decide) (by decide)]; exact hD)
    (by rw [preserved 1 (by decide) (by decide) (by decide)]; exact h1)
    (by rw [preserved 13 (by decide) (by decide) (by decide)]; exact h13)
    (by rw [preserved 14 (by decide) (by decide) (by decide)]; exact h14)
    (by rw [preserved 15 (by decide) (by decide) (by decide)]; exact h15)
  let e : Data := ⟨rf,rowStacks d (matrixSuffix Q (i+1)) (rowPayload b m (slots m shifts Q side v a))⟩
  have costeq : rowCost d D b=rowCost base D b := by
    unfold rowCost portWidth
    rw [preserved 6 (by decide) (by decide) (by decide),
      preserved 9 (by decide) (by decide) (by decide),
      preserved 2 (by decide) (by decide) (by decide),
      preserved 3 (by decide) (by decide) (by decide),
      preserved 4 (by decide) (by decide) (by decide),
      preserved 5 (by decide) (by decide) (by decide),
      preserved 14 (by decide) (by decide) (by decide)]
  refine ⟨n,e,by simpa [costeq] using hn,he,?_,?_⟩
  · simp [e,rowStacks,rowLoop]
  · constructor
    · intro j hj; exact (hr j hj).trans (inv.registers j hj)
    · simp [e,rowStacks]
    · have ht : (checkRows m shifts Q side v).take (i+1)=
          (checkRows m shifts Q side v).take i++[slots m shifts Q side v a] := by
        rw [List.take_succ_eq_append_getElem (by simpa [checkRows] using hi)]
        simp [checkRows,a]
      simp [e,rowStacks,ht,collectedRows_snoc,inv.output]
    · intro j h0 h12 h16
      simpa [e,rowStacks,h0,h12] using inv.other j h0 h12 h16

theorem checkLoop_eval {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (b : ℕ) (ready : LocalReady base D m b side v)
    (hq : base.stacks 0=matrixSuffix Q 0)
    (hs : base.stacks 9=shiftRows (List.ofFn shifts)) (hD : (base.stacks 6).length=D)
    (h1 : base.stacks 1=[]) (h13 : base.stacks 13=[])
    (h14 : base.stacks 14=[]) (h15 : base.stacks 15=[])
    (ht : (base.stacks 16).length=t) :
    ∃ n e, Eval (UnaryForPrograms.forCmd rowLoop rowStep) n base e ∧
      CheckInvariant (m:=m) base shifts Q side v b t e ∧ e.stacks 16=[] ∧
      n ≤ t*(rowCost base D b+2)+2 := by
  apply bounded_for_eval rowLoop rowStep
    (CheckInvariant (m:=m) base shifts Q side v b) t (rowCost base D b)
  · intro i d inv; exact inv.popped
  · exact checkStep_eval base shifts Q side v b ready hs hD h1 h13 h14 h15
  · exact ht
  · constructor
    · intros; rfl
    · exact hq
    · simp
    · intros; rfl

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
