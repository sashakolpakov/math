import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramVertexStep
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramRows

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

private theorem zeroWord_value (r : ℕ) : BinaryArithmetic.toNat (List.replicate r false)=0 := by
  induction r with
  | zero => rfl
  | succ r ih => simp [List.replicate_succ,toNat_cons,bitVal,ih]

private theorem word_eq (xs ys : List Bool) (hlen : xs.length=ys.length)
    (hv : BinaryArithmetic.toNat xs=BinaryArithmetic.toNat ys) : xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have hxy : x=y := by
        cases x <;> cases y <;> simp_all [toNat_cons,bitVal] <;> omega
      subst y
      congr 1
      apply ih ys (by simpa using hlen)
      cases x <;> simp_all [toNat_cons,bitVal]

def vertexPrefix {r D t : ℕ} (m : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (i : ℕ) : List (List (Fin m × SparseCode.F3)) :=
  ((List.finRange (2^r)).take i).flatMap fun j =>
    vertexRows m shifts Q (WalshExistence.cubeEquiv r j)

theorem vertexPrefix_succ {r D t : ℕ} (m : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (i : ℕ) (hi : i < 2^r) :
    vertexPrefix m shifts Q (i+1)=vertexPrefix m shifts Q i++
      vertexRows m shifts Q (WalshExistence.cubeEquiv r ⟨i,hi⟩) := by
  unfold vertexPrefix
  rw [List.take_succ_eq_append_getElem (by simpa using hi),List.flatMap_append]
  simp

theorem vertexPrefix_full {r D t : ℕ} (m : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) :
    vertexPrefix m shifts Q (2^r)=chronologicalRows m shifts Q := by
  unfold vertexPrefix
  rw [List.take_of_length_le (by simp)]
  rfl

structure VertexInvariant {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (b i : ℕ) (d : Data) : Prop where
  position : i ≤ 2^r
  value : BinaryArithmetic.toNat (d.stacks 2)=i
  width : i < 2^r → (d.stacks 2).length=r
  length : (d.stacks 2).length ≤ r+1
  output : d.stacks 12=collectedRows b (vertexPrefix m shifts Q i) (base.stacks 12)
  other : ∀ j : Fin 64, j≠2 → j≠8 → j≠12 → d.stacks j=base.stacks j

theorem VertexInvariant.popped {r D t m : ℕ} {base : Data} {shifts : Fin D → Cayley.Cube r}
    {Q : Fin t → Fin D → SparseCode.F3} {b i : ℕ} {d : Data}
    (h : VertexInvariant (m:=m) base shifts Q b i d) :
    VertexInvariant (m:=m) base shifts Q b i (UnaryForPrograms.popped vertexLoop d) := by
  constructor
  · exact h.position
  · simpa [UnaryForPrograms.popped,vertexLoop] using h.value
  · simpa [UnaryForPrograms.popped,vertexLoop] using h.width
  · simpa [UnaryForPrograms.popped,vertexLoop] using h.length
  · simpa [UnaryForPrograms.popped,vertexLoop] using h.output
  · intro j h2 h8 h12
    simpa [UnaryForPrograms.popped,vertexLoop,h8] using h.other j h2 h8 h12

theorem vertexIteration_eval {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (b : ℕ)
    (ready : LocalReady base D m b (base.regs 12) (0 : Cayley.Cube r))
    (hq : base.stacks 10=CodeSearchProgram.matrixFrames Q)
    (hs : base.stacks 9=shiftRows (List.ofFn shifts))
    (hD : (base.stacks 6).length=D) (ht : (base.stacks 7).length=t)
    (h0 : base.stacks 0=[]) (h1 : base.stacks 1=[]) (h13 : base.stacks 13=[])
    (h14 : base.stacks 14=[]) (h15 : base.stacks 15=[]) (h16 : base.stacks 16=[])
    (i : ℕ) (hi : i < 2^r) (d : Data) (inv : VertexInvariant (m:=m) base shifts Q b i d) :
    ∃ n e, n ≤ vertexCost base D t b ∧ Eval vertexStep n d e ∧
      e.stacks vertexLoop.counter=d.stacks vertexLoop.counter ∧
      VertexInvariant (m:=m) base shifts Q b (i+1) e := by
  let v := WalshExistence.cubeEquiv r ⟨i,hi⟩
  have hv : d.stacks 2=vertexBits v := by
    apply word_eq
    · simpa using inv.width hi
    · simpa [v,vertexBits_value] using inv.value
  have preserved (j : Fin 64) (h2 : j≠2) (h8 : j≠8) (h12 : j≠12) :
      d.stacks j=base.stacks j := inv.other j h2 h8 h12
  have rd : LocalReady d D m b (d.regs 12) v := by
    constructor
    · rfl
    · exact hv
    · rw [preserved 3 (by decide) (by decide) (by decide)]; exact ready.degree
    · rw [preserved 4 (by decide) (by decide) (by decide)]; exact ready.modulus
    · rw [preserved 5 (by decide) (by decide) (by decide)]; exact ready.width
    · exact ready.capacity
    · intro j hj hk
      have h2 : j≠2 := by intro hne; have hv := congrArg Fin.val hne; change j.val=2 at hv; omega
      have h8 : j≠8 := by intro hne; have hv := congrArg Fin.val hne; change j.val=8 at hv; omega
      have h12 : j≠12 := by intro hne; have hv := congrArg Fin.val hne; change j.val=12 at hv; omega
      rw [preserved j h2 h8 h12]; exact ready.work j hj hk
  obtain ⟨n,rf,he,hn,hr⟩ := vertexStep_eval d shifts Q v b rd
    (by rw [preserved 10 (by decide) (by decide) (by decide)]; exact hq)
    (by rw [preserved 9 (by decide) (by decide) (by decide)]; exact hs)
    (by rw [preserved 6 (by decide) (by decide) (by decide)]; exact hD)
    (by rw [preserved 7 (by decide) (by decide) (by decide)]; exact ht)
    (by rw [preserved 0 (by decide) (by decide) (by decide)]; exact h0)
    (by rw [preserved 1 (by decide) (by decide) (by decide)]; exact h1)
    (by rw [preserved 13 (by decide) (by decide) (by decide)]; exact h13)
    (by rw [preserved 14 (by decide) (by decide) (by decide)]; exact h14)
    (by rw [preserved 15 (by decide) (by decide) (by decide)]; exact h15)
    (by rw [preserved 16 (by decide) (by decide) (by decide)]; exact h16)
  let e : Data := ⟨rf,Function.update (Function.update d.stacks 12
    (collectedRows b (vertexRows m shifts Q v) (d.stacks 12))) 2
      (CounterPrograms.ripple true (d.stacks 2))⟩
  have costeq : vertexCost d D t b=vertexCost base D t b := by
    unfold vertexCost sideCost rowCost portWidth
    rw [preserved 10 (by decide) (by decide) (by decide),
      preserved 7 (by decide) (by decide) (by decide),
      preserved 6 (by decide) (by decide) (by decide),
      preserved 9 (by decide) (by decide) (by decide),
      preserved 3 (by decide) (by decide) (by decide),
      preserved 4 (by decide) (by decide) (by decide),
      preserved 5 (by decide) (by decide) (by decide),
      preserved 14 (by decide) (by decide) (by decide),hv,ready.vertex]
    simp
  refine ⟨n,e,by simpa [costeq] using hn,he,?_,?_⟩
  · simp [e,vertexLoop]
  · constructor
    · omega
    · simpa [e,CounterPrograms.value_eq_toNat,inv.value] using
        CounterPrograms.value_increment (d.stacks 2)
    · intro hj
      simpa [e] using increment_vertex_width (d.stacks 2) r (inv.width hi)
        (by simpa [CounterPrograms.value_eq_toNat,inv.value] using hj)
    · have hlen := CounterPrograms.ripple_length_le true (d.stacks 2)
      have old := inv.width hi
      simp only [e,Function.update_same]
      omega
    · simp [e,vertexPrefix_succ m shifts Q i hi,v,inv.output,collectedRows_append]
    · intro j h2 h8 h12
      simpa [e,h2,h12] using inv.other j h2 h8 h12

theorem vertexLoop_eval {r D t m : ℕ} (base : Data) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (b : ℕ)
    (ready : LocalReady base D m b (base.regs 12) (0 : Cayley.Cube r))
    (hq : base.stacks 10=CodeSearchProgram.matrixFrames Q)
    (hs : base.stacks 9=shiftRows (List.ofFn shifts))
    (hD : (base.stacks 6).length=D) (ht : (base.stacks 7).length=t)
    (hN : (base.stacks 8).length=2^r)
    (h0 : base.stacks 0=[]) (h1 : base.stacks 1=[]) (h13 : base.stacks 13=[])
    (h14 : base.stacks 14=[]) (h15 : base.stacks 15=[]) (h16 : base.stacks 16=[]) :
    ∃ n e, Eval (UnaryForPrograms.forCmd vertexLoop vertexStep) n base e ∧
      VertexInvariant (m:=m) base shifts Q b (2^r) e ∧ e.stacks 8=[] ∧
      n ≤ 2^r*(vertexCost base D t b+2)+2 := by
  apply bounded_for_eval vertexLoop vertexStep (VertexInvariant (m:=m) base shifts Q b)
    (2^r) (vertexCost base D t b)
  · intro i d inv; exact inv.popped
  · exact vertexIteration_eval base shifts Q b ready hq hs hD ht h0 h1 h13 h14 h15 h16
  · exact hN
  · constructor
    · omega
    · rw [ready.vertex]
      simp [vertexBits,zeroWord_value]
    · intro hi; rw [ready.vertex]; simp
    · rw [ready.vertex]; simp
    · simp [vertexPrefix]
    · intros; rfl

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
