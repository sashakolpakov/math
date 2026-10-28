import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCoefficientFrames

namespace OAI.Algorithms

/-! Composition of the actual coefficient callback around a supplied finite
matrix program. The matrix hypothesis is an execution contract for that code;
all copying, zero tests, classification, and cleanup are proved here. -/

namespace SubexponentialSAT.Subexp.BlockCoefficientAssembly

open BitProgram StackRoutines StructuredCalls
open BlockCoefficientFrames

abbrev Data := StructuredProgram.State 24 42

def ParentFrame (a b : Data) : Prop :=
  ∀ j : Fin 24, 8 ≤ j.val → j.val ≤ 13 → b.regs j = a.regs j

theorem ParentFrame.trans {a b c : Data} (hab : ParentFrame a b) (hbc : ParentFrame b c) :
    ParentFrame a c := fun j hj hk => (hbc j hj hk).trans (hab j hj hk)

private theorem parent_ne {j k : Fin 24} (hj : 8 ≤ j.val) (hk : j.val ≤ 13)
    (hout : k.val < 8 ∨ 13 < k.val) : j ≠ k := by
  intro he
  subst j
  omega

def transferState (a : Data) (src dst : Fin 42) : Data :=
  ⟨readRegs a.regs 21 22 none, transferStacks src dst a.stacks⟩

theorem transfer_eval (a : Data) (src dst : Fin 42) (hne : src ≠ dst) :
    Eval (BlockSearchLoop.transfer src dst) (3 * (a.stacks src).length + 3)
      a (transferState a src dst) := by
  apply Eval.call
  have h := halt_after_trace _
    (transferProgram_trace src dst (21 : Fin 24) 22 hne (by decide) a.regs a.stacks) 3 rfl rfl
  simpa [BlockSearchLoop.transfer, transferState, transferResult, transferProgram,
    StructuredProgram.State.withPC, Nat.add_assoc] using h

def clearState (a : Data) (src : Fin 42) : Data :=
  ⟨readRegs a.regs 21 22 none, clearStacks src a.stacks⟩

theorem clear_eval (a : Data) (src : Fin 42) :
    Eval (BlockSearchLoop.clear src) (2 * (a.stacks src).length + 3)
      a (clearState a src) := by
  apply Eval.call
  have h := halt_after_trace _
    (clearProgram_trace src (21 : Fin 24) 22 a.regs a.stacks) 2 rfl rfl
  simpa [BlockSearchLoop.clear, clearState, clearResult, clearProgram,
    StructuredProgram.State.withPC, Nat.add_assoc] using h

def prepared (a : Data) : Data :=
  copyState (copyState (transferState a 7 34) 41 33) 10 37

def matrixStacks (bank : Fin 42 → List Bool)
    (y coeff z : List (List Bool)) : Fin 42 → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update bank 33 []) 37 []) 34 (BlockZeroProgram.frames y))
    30 (BlockZeroProgram.frames z)) 40 (BlockZeroProgram.frames coeff)

def result (split : List Bool) (y coeff z : List (List Bool)) : Bool :=
  BlockZeroProgram.classifyResult (BlockZeroProgram.isZero y)
    (BlockZeroProgram.isZero coeff) (BlockZeroProgram.isZero (coeff.drop split.length))
    (BlockZeroProgram.isZero z)

abbrev suffix : Cmd 24 42 := BlockSearchLoop.sequence
  [BlockSearchLoop.zeroFrom 34 17, BlockSearchLoop.zeroFrom 40 18,
    BlockSearchLoop.tailZero, BlockSearchLoop.zeroFrom 30 20, BlockSearchLoop.classify,
    BlockSearchLoop.clear 30, BlockSearchLoop.clear 34, BlockSearchLoop.clear 40,
    BlockSearchLoop.atom (.set 14 false), BlockSearchLoop.atom (.set 15 true)]

def suffixCost (split : List Bool) (y coeff z : List (List Bool)) : ℕ :=
  12 * (BlockZeroProgram.frames y).length + 23 * (BlockZeroProgram.frames coeff).length +
    12 * (BlockZeroProgram.frames z).length + 7 * split.length + 65

theorem suffix_eval (a : Data) (split : List Bool) (y coeff z : List (List Bool))
    (hy : a.stacks 34 = BlockZeroProgram.frames y)
    (hc : a.stacks 40 = BlockZeroProgram.frames coeff)
    (hz : a.stacks 30 = BlockZeroProgram.frames z)
    (hsplit : a.stacks 8 = split) (hlen : split.length ≤ coeff.length)
    (h9 : a.stacks 9 = []) (h22 : a.stacks 22 = []) (h23 : a.stacks 23 = []) :
    ∃ n b, n ≤ suffixCost split y coeff z ∧ Eval suffix n a b ∧
      b.stacks = Function.update (Function.update (Function.update a.stacks 30 []) 34 []) 40 [] ∧
      b.regs 14 = false ∧ b.regs 15 = true ∧ b.regs 16 = result split y coeff z ∧
      ParentFrame a b := by
  obtain ⟨n1, d1, hn1, t1, hs1, hv1, hr1⟩ :=
    zeroFrom_eval a 34 17 y (by decide) (by decide) h9 h22 hy
  obtain ⟨n2, d2, hn2, t2, hs2, hv2, hr2⟩ :=
    zeroFrom_eval d1 40 18 coeff (by decide) (by decide)
      (by simpa only [hs1] using h9) (by simpa only [hs1] using h22)
      (by simpa only [hs1] using hc)
  obtain ⟨n3, d3, hn3, t3, hs3, hv3, hr3⟩ :=
    tailZero_eval d2 (coeff.take split.length) (coeff.drop split.length)
      (by simp [hs2, hs1, hsplit, List.length_take, Nat.min_eq_left hlen])
      (by simpa only [List.take_append_drop, hs2, hs1] using hc)
      (by simpa only [hs2, hs1] using h9)
      (by simpa only [hs2, hs1] using h22)
      (by simpa only [hs2, hs1] using h23)
  obtain ⟨n4, d4, hn4, t4, hs4, hv4, hr4⟩ :=
    zeroFrom_eval d3 30 20 z (by decide) (by decide)
      (by simpa only [hs3, hs2, hs1] using h9)
      (by simpa only [hs3, hs2, hs1] using h22)
      (by simpa only [hs3, hs2, hs1] using hz)
  obtain ⟨n5, hn5, t5⟩ := classify_eval d4
  let d5 := classified d4
  let d6 := clearState d5 30
  let d7 := clearState d6 34
  let d8 := clearState d7 40
  let d9 := (StructuredProgram.Atom.set (14 : Fin 24) false).eval d8
  let b := (StructuredProgram.Atom.set (15 : Fin 24) true).eval d9
  have t6 := clear_eval d5 30
  have t7 := clear_eval d6 34
  have t8 := clear_eval d7 40
  have t9 : Eval (BlockSearchLoop.atom (.set 14 false)) 1 d8 d9 := .base (.atom _ _)
  have t10 : Eval (BlockSearchLoop.atom (.set 15 true)) 1 d9 b := .base (.atom _ _)
  have trace : Eval suffix
      (n1 + (n2 + (n3 + (n4 + (n5 + ((2 * (d5.stacks 30).length + 3) +
        ((2 * (d6.stacks 34).length + 3) + ((2 * (d7.stacks 40).length + 3) +
          (1 + (1 + 0)))))))))) a b :=
    t1.seq (t2.seq (t3.seq (t4.seq (t5.seq (t6.seq (t7.seq (t8.seq
      (t9.seq (t10.seq (.base (.skip _)))))))))))
  have h17 : d4.regs 17 = BlockZeroProgram.isZero y := by
    rw [hr4 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hr3 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hr2 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hv1]
  have h18 : d4.regs 18 = BlockZeroProgram.isZero coeff := by
    rw [hr4 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hr3 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hv2]
  have h19 : d4.regs 19 = BlockZeroProgram.isZero (coeff.drop split.length) := by
    rw [hr4 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hv3]
  have hparent1 : ParentFrame a d1 := by
    intro j hj hk; apply hr1 <;> exact parent_ne hj hk (by decide)
  have hparent2 : ParentFrame d1 d2 := by
    intro j hj hk; apply hr2 <;> exact parent_ne hj hk (by decide)
  have hparent3 : ParentFrame d2 d3 := by
    intro j hj hk; apply hr3 <;> exact parent_ne hj hk (by decide)
  have hparent4 : ParentFrame d3 d4 := by
    intro j hj hk; apply hr4 <;> exact parent_ne hj hk (by decide)
  refine ⟨_, b, ?_, trace, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hs2, hs1, hsplit, List.take_append_drop] at hn3
    have h30 : d5.stacks 30 = BlockZeroProgram.frames z := by
      simpa only [d5, classified_stacks, hs4, hs3, hs2, hs1] using hz
    have h34 : d6.stacks 34 = BlockZeroProgram.frames y := by
      simpa [d6, d5, clearState, clearStacks, hs4, hs3, hs2, hs1] using hy
    have h40 : d7.stacks 40 = BlockZeroProgram.frames coeff := by
      simpa [d7, d6, d5, clearState, clearStacks, hs4, hs3, hs2, hs1] using hc
    rw [h30, h34, h40]
    unfold suffixCost
    omega
  · simp [b, d9, d8, d7, d6, d5, clearState, clearStacks, hs4, hs3, hs2, hs1,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]
  · simp [b, d9, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]
  · simp [b, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]
  · simp [b, d9, d8, d7, d6, d5, clearState, readRegs, classified,
      h17, h18, h19, hv4, result, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]
  · apply (hparent1.trans (hparent2.trans (hparent3.trans hparent4))).trans
    intro j hj hk
    have h14 : j ≠ 14 := parent_ne hj hk (by decide)
    have h15 : j ≠ 15 := parent_ne hj hk (by decide)
    have h16 : j ≠ 16 := parent_ne hj hk (by decide)
    have h21 : j ≠ 21 := parent_ne hj hk (by decide)
    have h22' : j ≠ 22 := parent_ne hj hk (by decide)
    simp [b, d9, d8, d7, d6, d5, clearState, readRegs, classified,
      h14, h15, h16, h21, h22', StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]

def callbackCost (matrixCost : ℕ) (ctx : BlockSearchLoop.Context)
    (table split bits : List Bool) (y coeff z : List (List Bool)) : ℕ :=
  matrixCost + 3 * bits.length + 7 * table.length + 7 * ctx.dimension.length +
    suffixCost split y coeff z + 13

/-- The matrix assumption is an actual execution of a supplied finite
command. Its output consumes the two copied matrix/dimension buffers and
returns the three encoded vectors on the fixed work ports. -/
theorem coefficient_eval (matrixPair : Cmd 24 42) (ctx : BlockSearchLoop.Context)
    (table split bits tail : List Bool) (base : Data)
    (hentry : BlockSearchLoop.CoefficientEntry ctx table split base)
    (y coeff z : List (List Bool)) (hlen : split.length ≤ coeff.length)
    (matrixCost : ℕ)
    (hmatrix : ∃ n b, n ≤ matrixCost ∧
      Eval matrixPair n
        (prepared (RecordPrograms.state BlockSearchLoop.coefficientPorts.toPorts
          base false true false tail bits.reverse)) b ∧
      b.stacks = matrixStacks
        (prepared (RecordPrograms.state BlockSearchLoop.coefficientPorts.toPorts
          base false true false tail bits.reverse)).stacks y coeff z ∧
      ParentFrame
        (prepared (RecordPrograms.state BlockSearchLoop.coefficientPorts.toPorts
          base false true false tail bits.reverse)) b) :
    ∃ n next, n ≤ callbackCost matrixCost ctx table split bits y coeff z ∧
      next.stacks = base.stacks ∧ ParentFrame base next ∧
      Eval (BlockSearchLoop.coefficientCallback matrixPair) n
        (RecordPrograms.state BlockSearchLoop.coefficientPorts.toPorts
          base false true false tail bits.reverse)
        (RecordPrograms.state BlockSearchLoop.coefficientPorts.toPorts
          next false true (result split y coeff z) tail []) := by
  rcases hentry with ⟨h27, h36, h38, h39, h10, h41, h8, h9, hwork⟩
  have h22 := hwork 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h23 := hwork 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h30 := hwork 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h33 := hwork 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h34 := hwork 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h37 := hwork 37 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h40 := hwork 40 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  let a := RecordPrograms.state BlockSearchLoop.coefficientPorts.toPorts
    base false true false tail bits.reverse
  let a1 := transferState a 7 34
  let a2 := copyState a1 41 33
  let a3 := copyState a2 10 37
  have t0 := transfer_eval a 7 34 (by decide)
  have t1 := copy_eval a1 41 33 (by decide) (by decide) (by decide)
    (by simp [a1, a, transferState, transferStacks, RecordPrograms.state,
      BlockSearchLoop.coefficientPorts, h9])
  have t2 := copy_eval a2 10 37 (by decide) (by decide) (by decide)
    (by simp [a2, a1, a, copyState, copyStacks, transferState, transferStacks,
      RecordPrograms.state, BlockSearchLoop.coefficientPorts, h9])
  obtain ⟨nm, m, hnm, tm, hms, hmr⟩ := hmatrix
  change Eval matrixPair nm a3 m at tm
  change m.stacks = matrixStacks a3.stacks y coeff z at hms
  change ParentFrame a3 m at hmr
  have hm34 : m.stacks 34 = BlockZeroProgram.frames y := by simp [hms, matrixStacks]
  have hm40 : m.stacks 40 = BlockZeroProgram.frames coeff := by simp [hms, matrixStacks]
  have hm30 : m.stacks 30 = BlockZeroProgram.frames z := by simp [hms, matrixStacks]
  have hm8 : m.stacks 8 = split := by
    simp [hms, matrixStacks, a3, a2, a1, a, copyState, copyStacks, transferState,
      transferStacks, RecordPrograms.state, BlockSearchLoop.coefficientPorts, h8]
  have hm9 : m.stacks 9 = [] := by
    simp [hms, matrixStacks, a3, a2, a1, a, copyState, copyStacks, transferState,
      transferStacks, RecordPrograms.state, BlockSearchLoop.coefficientPorts, h9]
  have hm22 : m.stacks 22 = [] := by
    simp [hms, matrixStacks, a3, a2, a1, a, copyState, copyStacks, transferState,
      transferStacks, RecordPrograms.state, BlockSearchLoop.coefficientPorts, h22]
  have hm23 : m.stacks 23 = [] := by
    simp [hms, matrixStacks, a3, a2, a1, a, copyState, copyStacks, transferState,
      transferStacks, RecordPrograms.state, BlockSearchLoop.coefficientPorts, h23]
  obtain ⟨ns, b, hns, ts, hbs, hb14, hb15, hb16, hbr⟩ :=
    suffix_eval m split y coeff z hm34 hm40 hm30 hm8 hlen hm9 hm22 hm23
  let next : Data := ⟨b.regs, base.stacks⟩
  have hstacks : b.stacks = Function.update (Function.update base.stacks 6 tail) 7 [] := by
    rw [hbs, hms]
    funext j
    fin_cases j <;> simp [matrixStacks, a3, a2, a1, a, copyState, copyStacks,
      transferState, transferStacks, RecordPrograms.state, BlockSearchLoop.coefficientPorts,
      h30, h33, h34, h37, h40]
  have hfinish : RecordPrograms.state BlockSearchLoop.coefficientPorts.toPorts
      next false true (result split y coeff z) tail [] = b := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      fin_cases j <;> simp [BlockSearchLoop.coefficientPorts,
        next, hb14, hb15, hb16]
    · exact hstacks.symm
  have hprep : ParentFrame base a3 := by
    intro j hj hk
    fin_cases j <;> norm_num at hj <;> norm_num at hk <;>
      simp [a3, a2, a1, a, copyState, transferState, readRegs, RecordPrograms.state,
        BlockSearchLoop.coefficientPorts]
  have trace : Eval (BlockSearchLoop.coefficientCallback matrixPair)
      ((3 * (a.stacks 7).length + 3) +
        ((7 * (a1.stacks 41).length + 5) + ((7 * (a2.stacks 10).length + 5) + (nm + ns))))
      a b := t0.seq (t1.seq (t2.seq (tm.seq ts)))
  refine ⟨_, next, ?_, rfl, hprep.trans (hmr.trans hbr),
    by simpa only [hfinish] using trace⟩
  have ha7 : (a.stacks 7).length = bits.length := by
    simp [a, RecordPrograms.state, BlockSearchLoop.coefficientPorts]
  have ha41 : a1.stacks 41 = table := by
    simp [a1, a, transferState, transferStacks, RecordPrograms.state,
      BlockSearchLoop.coefficientPorts, h41]
  have ha10 : a2.stacks 10 = ctx.dimension := by
    simp [a2, a1, a, copyState, copyStacks, transferState, transferStacks,
      RecordPrograms.state, BlockSearchLoop.coefficientPorts, h10]
  rw [ha7, ha41, ha10]
  unfold callbackCost
  omega

/-- Package the concrete composition into the enclosing record iterator's
callback contract. Only the actual matrix execution and its independently
proved arithmetic interpretation are supplied by the caller. -/
theorem coefficientContract (matrixPair : Cmd 24 42) (ctx : BlockSearchLoop.Context)
    (table split : List Bool) (valid : List Bool → Prop)
    (y coeff z : List Bool → List (List Bool)) (test : List Bool → Bool)
    (matrixCost : List Bool → ℕ)
    (hlen : ∀ bits, valid bits → split.length ≤ (coeff bits).length)
    (hresult : ∀ bits, valid bits → result split (y bits) (coeff bits) (z bits) = test bits)
    (hmatrix : ∀ bits tail base, valid bits →
      BlockSearchLoop.CoefficientEntry ctx table split base →
      ∃ n b, n ≤ matrixCost bits ∧
        Eval matrixPair n
          (prepared (RecordPrograms.state BlockSearchLoop.coefficientPorts.toPorts
            base false true false tail bits.reverse)) b ∧
        b.stacks = matrixStacks
          (prepared (RecordPrograms.state BlockSearchLoop.coefficientPorts.toPorts
            base false true false tail bits.reverse)).stacks (y bits) (coeff bits) (z bits) ∧
        ParentFrame
          (prepared (RecordPrograms.state BlockSearchLoop.coefficientPorts.toPorts
            base false true false tail bits.reverse)) b) :
    BlockSearchLoop.CoefficientContract matrixPair ctx table split test
      (fun bits => callbackCost (matrixCost bits) ctx table split bits (y bits) (coeff bits) (z bits))
      valid := by
  intro bits tail base hv hb
  obtain ⟨n, next, hn, hs, hr, he⟩ := coefficient_eval matrixPair ctx table split bits tail
    base hb (y bits) (coeff bits) (z bits) (hlen bits hv) (matrixCost bits)
    (hmatrix bits tail base hv hb)
  rw [hresult bits hv] at he
  exact ⟨n, next, hn, hs, hr, he⟩

theorem callbackCost_encoded (matrixCost : ℕ) (ctx : BlockSearchLoop.Context)
    (table split : List Bool) (y coeff z : List (List Bool)) :
    callbackCost matrixCost ctx table split (BlockZeroProgram.frames coeff) y coeff z =
      matrixCost + 26 * (BlockZeroProgram.frames coeff).length +
        12 * (BlockZeroProgram.frames y).length + 12 * (BlockZeroProgram.frames z).length +
        7 * table.length + 7 * ctx.dimension.length + 7 * split.length + 78 := by
  unfold callbackCost suffixCost
  omega

end SubexponentialSAT.Subexp.BlockCoefficientAssembly

end OAI.Algorithms
