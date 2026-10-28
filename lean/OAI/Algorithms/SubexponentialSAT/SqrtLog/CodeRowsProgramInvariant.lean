import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramPortSemantic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramFor

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

structure LocalInvariant {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (b : ℕ) (qt st : List Bool) (i : ℕ) (d : Data) : Prop where
  position : i ≤ D
  registers : ∀ j : Fin 16, 12 ≤ j.val → d.regs j=base.regs j
  source : d.stacks 0=CodeSearchProgram.scalarFrames ((List.ofFn (Q a)).drop i)++qt
  shiftSource : d.stacks 1=shiftRows ((List.ofFn shifts).drop i)++st
  accum : d.stacks 13=(rowPayload b m (prefixSlots m shifts Q side v a i)).reverse++base.stacks 13
  index : BinaryArithmetic.toNat (d.stacks 14)=i
  indexLength : (d.stacks 14).length ≤ i
  other : ∀ j : Fin 64, j≠0 → j≠1 → j≠13 → j≠14 → j≠15 → d.stacks j=base.stacks j

theorem LocalInvariant.popped {r D t m : ℕ} {base : Data} {shifts : Fin D → Cayley.Cube r}
    {Q : Fin t → Fin D → SparseCode.F3} {side : Bool} {v : Cayley.Cube r}
    {a : Fin t} {b : ℕ} {qt st : List Bool} {i : ℕ} {d : Data}
    (h : LocalInvariant (m:=m) base shifts Q side v a b qt st i d) :
    LocalInvariant (m:=m) base shifts Q side v a b qt st i (UnaryForPrograms.popped portLoop d) := by
  constructor
  · exact h.position
  · intro j hj
    have h10 : j≠10 := by intro hne; have hv := congrArg Fin.val hne; change j.val=10 at hv; omega
    have h11 : j≠11 := by intro hne; have hv := congrArg Fin.val hne; change j.val=11 at hv; omega
    simpa [UnaryForPrograms.popped,portLoop,readRegs,h10,h11] using h.registers j hj
  · simpa [UnaryForPrograms.popped,portLoop] using h.source
  · simpa [UnaryForPrograms.popped,portLoop] using h.shiftSource
  · simpa [UnaryForPrograms.popped,portLoop] using h.accum
  · simpa [UnaryForPrograms.popped,portLoop] using h.index
  · simpa [UnaryForPrograms.popped,portLoop] using h.indexLength
  · intro j h0 h1 h13 h14 h15
    simpa [UnaryForPrograms.popped,portLoop,h15] using h.other j h0 h1 h13 h14 h15

theorem LocalInvariant.width {r D t m : ℕ} {base : Data} {shifts : Fin D → Cayley.Cube r}
    {Q : Fin t → Fin D → SparseCode.F3} {side : Bool} {v : Cayley.Cube r}
    {a : Fin t} {b : ℕ} {qt st : List Bool} {i : ℕ} {d : Data}
    (h : LocalInvariant (m:=m) base shifts Q side v a b qt st i d) :
    portWidth d ≤ portWidth base+D := by
  have h2 := h.other 2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h3 := h.other 3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h4 := h.other 4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h5 := h.other 5 (by decide) (by decide) (by decide) (by decide) (by decide)
  simp only [portWidth,h2,h3,h4,h5]
  have hp := h.position
  have hl := h.indexLength
  omega

theorem localInvariant_initial {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (b : ℕ) (qt st : List Bool)
    (hq : base.stacks 0=CodeSearchProgram.scalarFrames (List.ofFn (Q a))++qt)
    (hs : base.stacks 1=shiftRows (List.ofFn shifts)++st) (hp : base.stacks 14=[]) :
    LocalInvariant (m:=m) base shifts Q side v a b qt st 0 base := by
  constructor
  · omega
  · intro j hj; rfl
  · simpa using hq
  · simpa using hs
  · simp [rowPayload]
  · simp [hp]
  · simp [hp]
  · intros; rfl

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
