import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafStartup
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode

/-! Actual physical preparation of the streamed greedy selector. The final
suffix clears the argmin bank, preserves the serialized code history, and
constructs the single retained zero candidate using the runtime depth word. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram
open HashGreedyProgram

/-- This runs after actual serialization, while the saved modulus and round
words are still intact. It neither repeats parameter arithmetic nor searches. -/
def afterCode : Cmd 40 896 :=
  .seq Initialize.finishSetup
    (.seq Initialize.zeroCommand (.call (StackRoutines.clearProgram 779 0 1)))

def finishTime (depth L : ℕ) : ℕ :=
  29 * L + 41 + 100 * (depth + 1) * (3 * L + 1)

/-- Complete physical store after the final preparation suffix. -/
def finishedWords (a : Data) : Fin 896 → List Bool :=
  Function.update (Function.update (Initialize.finishedStacks a) 778 (Initialize.zeroWord a)) 779 []

theorem finished_frame (a : Data) (i : Fin 896)
    (hcore : i ∉ Initialize.corePorts) (h778 : i ≠ 778) (h779 : i ≠ 779) (h818 : i ≠ 818) :
    finishedWords a i = a.stacks i := by
  simp [finishedWords, Initialize.finishedStacks, BankRoutines.clearBankStacks,
    hcore, h778, h779, h818]

private theorem core_ge (i : Fin 896) (hi : i ∈ Initialize.corePorts) : 768 ≤ i.val := by
  simp only [Initialize.corePorts, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem finished_core (a : Data) (i : Fin 896) (hi : i ∈ Initialize.corePorts) :
    finishedWords a i = [] := by
  by_cases h779 : i = 779
  · subst i
    simp [finishedWords]
  have hne : i ≠ 778 := by
    intro h
    subst i
    simp [Initialize.corePorts] at hi
  simp [finishedWords, Initialize.finishedStacks, BankRoutines.clearBankStacks, hi, hne, h779]

theorem finished_low (a : Data) (he : WorkerEmpty a) :
    ∀ i : Fin 896, i.val < 768 → finishedWords a i = [] := by
  intro i hi
  have hneq (j : Fin 896) (hj : 768 ≤ j.val) : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    omega
  rw [finished_frame a i (fun h => (Nat.not_le_of_lt hi) (core_ge i h))
    (hneq 778 (by decide)) (hneq 779 (by decide)) (hneq 818 (by decide))]
  exact NativeCodeAssembly.worker_empty a he i hi

/-- The final suffix has one actual execution, exact full-store readback,
a fixed local polynomial cost, and an all-port bound on that same trace. -/
theorem afterCode_eval (a : Data) (depth L : ℕ)
    (he : WorkerEmpty a) (ha : ∀ i, (a.stacks i).length ≤ L)
    (hd : BinaryArithmetic.toNat (a.stacks 817) = depth) :
    ∃ steps b, steps ≤ finishTime depth L ∧ Eval afterCode steps a b ∧
      b.stacks = finishedWords a ∧
      (∀ i, (b.stacks i).length ≤ max L (2 * (depth * (a.stacks 780).length) + 3)) ∧
      ∀ k c, k ≤ steps → Trace (compiled afterCode 784 788) k
        (a.withPC (some (compiled afterCode 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ L + finishTime depth L := by
  have hlo := NativeCodeAssembly.worker_empty a he
  obtain ⟨nf, hnf, f, hef, hf⟩ := Initialize.finishSetup_eval a L ha (hlo 767 (by decide))
  have hff (i : Fin 896) (hc : i ∉ Initialize.corePorts) (h818 : i ≠ 818) :
      f.stacks i = a.stacks i := by
    simp [hf, Initialize.finishedStacks, BankRoutines.clearBankStacks, hc, h818]
  have hfl (i : Fin 896) (hi : i.val < 768) : f.stacks i = [] := by
    have hn (j : Fin 896) (hj : 768 ≤ j.val) : i ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      omega
    rw [hff i (fun h => (Nat.not_le_of_lt hi) (core_ge i h)) (hn 818 (by decide))]
    exact hlo i hi
  have hfb : ∀ i, (f.stacks i).length ≤ L := by
    intro i
    by_cases hc : i ∈ Initialize.corePorts
    · simp [hf, Initialize.finishedStacks, BankRoutines.clearBankStacks, hc]
    by_cases hi : i = 818
    · subst i
      simpa [hf, Initialize.finishedStacks, BankRoutines.clearBankStacks,
        Initialize.corePorts] using ha 781
    simpa [hf, Initialize.finishedStacks, BankRoutines.clearBankStacks, hc, hi] using ha i
  obtain ⟨nz, hnz, b, hez, hz⟩ := Initialize.zero_eval f
    (hfl 0 (by decide)) (hfl 1 (by decide)) (hfl 2 (by decide))
    (hfl 3 (by decide)) (hfl 767 (by decide))
  have hf817 : f.stacks 817 = a.stacks 817 := hff 817 (by decide) (by decide)
  have hf780 : f.stacks 780 = a.stacks 780 := hff 780 (by decide) (by decide)
  have hfd : CounterPrograms.value (f.stacks 817) = depth := by
    rw [CounterPrograms.value_eq_toNat, hf817, hd]
  have hzero : Initialize.zeroWord f = Initialize.zeroWord a := by
    simp only [Initialize.zeroWord, hf817, hf780]
  have hnz' : nz ≤ 100 * (depth + 1) * (3 * L + 1) := by
    rw [hfd] at hnz
    apply hnz.trans
    apply Nat.mul_le_mul_left
    have := hfb 780
    have := hfb 817
    have := hfb 778
    omega
  have hz779 : b.stacks 779 = a.stacks 779 := by
    rw [hz, Function.update_of_ne (by decide), hff 779 (by decide) (by decide)]
  let out : Data := ⟨readRegs b.regs 0 1 none, StackRoutines.clearStacks 779 b.stacks⟩
  have heclear := Subexp.TupleProgram.clear_eval (779 : Fin 896) (0 : Fin 40) 1 b
  have hsteps : nf + (nz + (2 * (b.stacks 779).length + 3)) ≤ finishTime depth L := by
    have h779 := ha 779
    rw [hz779]
    dsimp only [finishTime]
    omega
  have heval : Eval afterCode (nf + (nz + (2 * (b.stacks 779).length + 3))) a out :=
    hef.seq (hez.seq heclear)
  have hwords : out.stacks = finishedWords a := by
    dsimp only [out, StackRoutines.clearStacks]
    rw [hz, hzero, hf]
    rfl
  refine ⟨_, out, hsteps, heval, hwords, ?_, ?_⟩
  · intro i
    by_cases hi779 : i = 779
    · subst i
      simp [out, StackRoutines.clearStacks]
    change ((StackRoutines.clearStacks 779 b.stacks) i).length ≤ _
    rw [StackRoutines.clearStacks, Function.update_of_ne hi779]
    by_cases hi : i = 778
    · subst i
      rw [hz, Function.update_self, Initialize.zeroWord_length, hfd, hf780]
      exact Nat.le_max_right _ _
    rw [hz, Function.update_of_ne hi]
    exact (hfb i).trans (Nat.le_max_left _ _)
  · intro k c hk hc i
    have hg : (c.stacks i).length ≤ (a.stacks i).length + k := by
      simpa [selectedStackBits] using trace_selectedStackBits _ {i} hc
    have hi := ha i
    omega

/-- The concrete final preparation changes no formula, count, or saved
parameter word; it preserves the history produced by the actual serializer. -/
theorem finished_parameters (a : Data) :
    finishedWords a 777 = a.stacks 777 ∧
    finishedWords a 780 = a.stacks 780 ∧
    finishedWords a 781 = a.stacks 781 ∧
    finishedWords a 782 = a.stacks 782 ∧
    finishedWords a 783 = a.stacks 783 ∧
    finishedWords a 784 = a.stacks 784 ∧
    finishedWords a 785 = a.stacks 785 ∧
    finishedWords a 786 = a.stacks 786 ∧
    finishedWords a 788 = a.stacks 788 ∧
    finishedWords a 817 = a.stacks 817 ∧
    finishedWords a 818 = a.stacks 781 ∧
    finishedWords a 778 = Initialize.zeroWord a ∧ finishedWords a 779 = [] := by
  simp [finishedWords, Initialize.finishedStacks, BankRoutines.clearBankStacks,
    Initialize.corePorts]

/-- Physical entry condition for the streamed selector. Every field records
an actual stack word; none supplies an evaluator, trace, or resource oracle. -/
structure Ready (n m B : ℕ) (initial : List (List Bool)) (a : Data) : Prop where
  worker : WorkerEmpty a
  core : ∀ i ∈ Initialize.corePorts, a.stacks i = []
  history : a.stacks 777 = encodedHistory initial
  counter : a.stacks 778 = Encoding.encodeList id
    [List.replicate (HashCandidates.payloadWidth m (SparseCode.distanceDenom m B)) false]
  scratch : a.stacks 779 = []
  modulus : BinaryArithmetic.toNat (a.stacks 780) = 3 * m
  modulus_length : (a.stacks 780).length = HashCandidates.digitWidth m
  rounds : a.stacks 781 = List.replicate (HashSelect.loopCap n m) true
  clauses : BinaryArithmetic.toNat (a.stacks 782) = m
  width : a.stacks 783 = a.stacks 780
  depth : BinaryArithmetic.toNat (a.stacks 817) = SparseCode.distanceDenom m B
  shape : a.stacks 818 = List.replicate (HashSelect.loopCap n m) true

/-- This exact store implication is used with the actual suffix execution,
so no readiness field is left as an implementation assumption. -/
theorem finished_ready (a b : Data) {n m B : ℕ} (initial : List (List Bool))
    (he : WorkerEmpty a) (hb : b.stacks = finishedWords a)
    (hh : a.stacks 777 = encodedHistory initial)
    (hm : BinaryArithmetic.toNat (a.stacks 780) = 3 * m)
    (hl : (a.stacks 780).length = HashCandidates.digitWidth m)
    (hr : a.stacks 781 = List.replicate (HashSelect.loopCap n m) true)
    (hc : BinaryArithmetic.toNat (a.stacks 782) = m)
    (hw : a.stacks 783 = a.stacks 780)
    (hd : BinaryArithmetic.toNat (a.stacks 817) = SparseCode.distanceDenom m B) :
    Ready n m B initial b := by
  have hp := finished_parameters a
  rcases hp with ⟨h777,h780,h781,h782,h783,_h784,_h785,_h786,_h788,h817,h818,h778,h779⟩
  constructor
  · intro i
    rw [hb]
    exact finished_low a he (workerStack i) (by simp [workerStack])
  · intro i hi
    rw [hb]
    exact finished_core a i hi
  · exact (congrFun hb 777).trans (h777.trans hh)
  · rw [hb, h778]
    exact Initialize.zeroWord_of_parameters a m (SparseCode.distanceDenom m B)
      (by rw [CounterPrograms.value_eq_toNat]; exact hd) hl
  · exact (congrFun hb 779).trans h779
  · simpa only [hb, h780] using hm
  · simpa only [hb, h780] using hl
  · exact (congrFun hb 781).trans (h781.trans hr)
  · simpa only [hb, h782] using hc
  · simpa only [hb, h783, h780] using hw
  · simpa only [hb, h817] using hd
  · exact (congrFun hb 818).trans (h818.trans hr)

/-- Actual code searches and row serialization followed by paid selector
initialization. The code matrices are produced by the searches themselves. -/
def afterCanonical : Cmd 40 896 := .seq NativeCodeAssembly.command afterCode

/-- Code construction and initialization expose their actual intermediate
metadata state for the fixed numerical envelopes, never an assumed layout. -/
theorem afterCanonical_eval (a : Data) {n m B L : ℕ}
    (hm : 0 < m) (hB : 0 < B) (he : WorkerEmpty a)
    (ha : ∀ i, (a.stacks i).length ≤ L)
    (hc : BinaryArithmetic.toNat (a.stacks 782) = m)
    (hBword : BinaryArithmetic.toNat (a.stacks 786) = B)
    (hwidth : a.stacks 768 = a.stacks 780)
    (hmod : BinaryArithmetic.toNat (a.stacks 780) = 3 * m)
    (hmodlen : (a.stacks 780).length = HashCandidates.digitWidth m)
    (h783 : a.stacks 783 = a.stacks 780)
    (hdepth : BinaryArithmetic.toNat (a.stacks 817) = SparseCode.distanceDenom m B)
    (hrounds : a.stacks 781 = List.replicate (HashSelect.loopCap n m) true) :
    ∃ (steps : ℕ) (prepared out : Data)
      (shifts : SparseCode.SuppliedShifts m B) (Q : SparseCode.SuppliedLocal m B),
      let P := NativeLeafSetup.parameterTime m B L (a.stacks 782).length (a.stacks 786).length
      let A := L + P
      let R := NativeCodeAssembly.afterBoundary A m B
        (prepared.stacks 801) (a.stacks 782) (a.stacks 768)
      steps ≤ P + NativeCodeAssembly.afterTime A m B (prepared.stacks 800).length
        (prepared.stacks 801) (a.stacks 782) (a.stacks 768) +
          finishTime (SparseCode.distanceDenom m B) R ∧
      Eval afterCanonical steps a out ∧
      Metadata m B prepared ∧ (∀ i, (prepared.stacks i).length ≤ A) ∧
      Ready n m B (HashGreedyCode.initial shifts Q) out ∧
      WalshExistence.Good (SparseCode.gapDenom m B) shifts ∧
      SparseCode.HasDistance Q (SparseCode.degree m B / (100 * B * SparseCode.logSize m) + 1) ∧
      (∀ i : Fin 896, 784 ≤ i.val → (i.val < 800 ∨ 818 < i.val) →
        out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ max R
        (2 * (SparseCode.distanceDenom m B * HashCandidates.digitWidth m) + 3)) ∧
      ∀ k c, k ≤ steps → Trace (compiled afterCanonical 784 788) k
        (a.withPC (some (compiled afterCanonical 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤
          max (max (A + 1) (NativeCodeAssembly.afterSpace A m B
            (prepared.stacks 800).length (prepared.stacks 801) (a.stacks 782) (a.stacks 768)))
            (R + finishTime (SparseCode.distanceDenom m B) R) := by
  have hv : BinaryArithmetic.toNat (a.stacks 768) = 3 * m := hwidth ▸ hmod
  obtain ⟨nc,p,c,shifts,Q,hnc,hec,hmeta,hp,_hq,_hD,hrows,hgood,hdist,hce,hcf,hcb,hcs⟩ :=
    NativeCodeAssembly.command_eval hm hB a he ha hc hBword hv
  have frame (i : Fin 896) (hi : 768 ≤ i.val) (h777 : i ≠ 777)
      (hr : i.val < 800 ∨ 816 < i.val) : c.stacks i = a.stacks i := hcf i hi h777 hr
  have cd : BinaryArithmetic.toNat (c.stacks 817) = SparseCode.distanceDenom m B := by
    rw [frame 817 (by decide) (by decide) (Or.inr (by decide))]
    exact hdepth
  obtain ⟨nf,out,hnf,hef,hwords,hout,hfs⟩ := afterCode_eval c _ _ hce hcb cd
  have history : c.stacks 777 = encodedHistory (HashGreedyCode.initial shifts Q) := by
    rw [hrows, hwidth, hmodlen]
    exact (HashGreedyCode.initial_encoding shifts Q).symm
  have hready := finished_ready c out (HashGreedyCode.initial shifts Q) hce hwords history
    (by rw [frame 780 (by decide) (by decide) (Or.inl (by decide))]; exact hmod)
    (by rw [frame 780 (by decide) (by decide) (Or.inl (by decide))]; exact hmodlen)
    (by rw [frame 781 (by decide) (by decide) (Or.inl (by decide))]; exact hrounds)
    (by rw [frame 782 (by decide) (by decide) (Or.inl (by decide))]; exact hc)
    (by rw [frame 783 (by decide) (by decide) (Or.inl (by decide)),
      frame 780 (by decide) (by decide) (Or.inl (by decide))]; exact h783) cd
  refine ⟨nc+nf,p,out,shifts,Q,Nat.add_le_add hnc hnf,hec.seq hef,hmeta,hp,
    hready,hgood,hdist,?_,?_,?_⟩
  · intro i hi hr
    have hn (j : Fin 896) (hj : j.val < 784) : i ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      omega
    have hi818 : i ≠ 818 := by
      intro h
      subst i
      change 818 < 800 ∨ 818 < 818 at hr
      omega
    rw [hwords, finished_frame c i (by
      intro hm
      simp only [Initialize.corePorts, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      (hn 778 (by decide)) (hn 779 (by decide)) hi818]
    exact frame i (by omega) (hn 777 (by decide)) (by omega)
  · simpa only [frame 780 (by decide) (by decide) (Or.inl (by decide)), hmodlen] using hout
  · exact StructuredSpace.sequence_stack_bound hec hef 784 788
      (fun k c hk ht i => (hcs k c hk ht i).trans (Nat.le_max_left _ _))
      (fun k c hk ht i => (hfs k c hk ht i).trans (Nat.le_max_right _ _))
      (compiled afterCanonical 784 788) (siteAddress afterCanonical) (exitAddress afterCanonical)
      (compiled_site afterCanonical 784 788)

/-- The executable preparation is fixed before its input. Numeric parameters
occur only in the correctness and resource statements. -/
def command : Cmd 40 896 := .seq NativeLeafSetup.canonicalStart afterCanonical

def continuationTime (m B L : ℕ) (a prepared : Data) : ℕ :=
  let P := NativeLeafSetup.parameterTime m B L (a.stacks 782).length (a.stacks 786).length
  let A := L + P
  let R := NativeCodeAssembly.afterBoundary A m B
    (prepared.stacks 801) (a.stacks 782) (a.stacks 768)
  P + NativeCodeAssembly.afterTime A m B (prepared.stacks 800).length
    (prepared.stacks 801) (a.stacks 782) (a.stacks 768) +
      finishTime (SparseCode.distanceDenom m B) R

def continuationSpace (m B L : ℕ) (a prepared : Data) : ℕ :=
  let P := NativeLeafSetup.parameterTime m B L (a.stacks 782).length (a.stacks 786).length
  let A := L + P
  let R := NativeCodeAssembly.afterBoundary A m B
    (prepared.stacks 801) (a.stacks 782) (a.stacks 768)
  max (max (A + 1) (NativeCodeAssembly.afterSpace A m B (prepared.stacks 800).length
    (prepared.stacks 801) (a.stacks 782) (a.stacks 768)))
      (R + finishTime (SparseCode.distanceDenom m B) R)

def retainedBound (m B L : ℕ) (a prepared : Data) : ℕ :=
  let P := NativeLeafSetup.parameterTime m B L (a.stacks 782).length (a.stacks 786).length
  let A := L + P
  let R := NativeCodeAssembly.afterBoundary A m B
    (prepared.stacks 801) (a.stacks 782) (a.stacks 768)
  max R (2 * (SparseCode.distanceDenom m B * HashCandidates.digitWidth m) + 3)

/-- From the actually loaded nonterminal formula, the native preparation
produces the selector's physical entry state and its attained initial code.
The same execution carries the time and every-prefix all-stack bounds.
The retained bound is independent of the exponential search runtime. -/
theorem command_eval (a : Data) {n B W : ℕ} (records : List (List Bool))
    (ha : ∀ i, (a.stacks i).length ≤ W)
    (he : ∀ i : Fin 896, i.val ≤ 782 → a.stacks i = [])
    (hformula : a.stacks 784 = Encoding.encodeList id records)
    (hm : records ≠ []) (hB : 0 < B)
    (hn : BinaryArithmetic.toNat (a.stacks 785) = n)
    (hBword : BinaryArithmetic.toNat (a.stacks 786) = B) :
    ∃ (steps : ℕ) (started prepared out : Data)
      (shifts : SparseCode.SuppliedShifts records.length B)
      (Q : SparseCode.SuppliedLocal records.length B),
      let L := W + NativeLeafSetup.canonicalStartTime n records.length W
      steps ≤ NativeLeafSetup.canonicalStartTime n records.length W +
        continuationTime records.length B L started prepared ∧
      Eval command steps a out ∧
      (∀ i, (started.stacks i).length ≤ L) ∧
      BinaryArithmetic.toNat (started.stacks 782) = records.length ∧
      BinaryArithmetic.toNat (started.stacks 768) = 3 * records.length ∧
      Metadata records.length B prepared ∧
      (∀ i, (prepared.stacks i).length ≤ L + NativeLeafSetup.parameterTime records.length B L
        (started.stacks 782).length (started.stacks 786).length) ∧
      Ready n records.length B (HashGreedyCode.initial shifts Q) out ∧
      WalshExistence.Good (SparseCode.gapDenom records.length B) shifts ∧
      SparseCode.HasDistance Q (SparseCode.degree records.length B /
        (100 * B * SparseCode.logSize records.length) + 1) ∧
      (∀ i : Fin 896, 784 ≤ i.val → (i.val < 800 ∨ 818 < i.val) →
        out.stacks i = a.stacks i) ∧
      (∀ i, (out.stacks i).length ≤ retainedBound records.length B L started prepared) ∧
      ∀ k c, k ≤ steps → Trace (compiled command 784 788) k
        (a.withPC (some (compiled command 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤
          max (L + 1) (continuationSpace records.length B L started prepared) := by
  obtain ⟨ns,s,hns,hes,hse,hw,h783,hmod,hml,hd,hr,hmc,hsf,hsb,_hst,hss⟩ :=
    NativeLeafSetup.canonicalStart_eval a records ha he hformula hm hn hBword
  have hsB : BinaryArithmetic.toNat (s.stacks 786) = B := by
    rw [hsf 786 (by decide) (by decide)]
    exact hBword
  obtain ⟨nc,p,out,shifts,Q,hnc,hec,hmeta,hp,hready,hgood,hdist,hframe,hbound,hspace⟩ :=
    afterCanonical_eval s (List.length_pos_iff.mpr hm) hB hse hsb hmc hsB hw hmod hml h783 hd hr
  change nc ≤ continuationTime records.length B
    (W + NativeLeafSetup.canonicalStartTime n records.length W) s p at hnc
  refine ⟨ns+nc,s,p,out,shifts,Q,Nat.add_le_add hns hnc,hes.seq hec,hsb,hmc,
    hw ▸ hmod,hmeta,hp,hready,hgood,hdist,?_,hbound,?_⟩
  · intro i hi hregion
    rw [hframe i hi hregion]
    apply hsf i hi
    intro heq
    subst i
    change 817 < 800 ∨ 818 < 817 at hregion
    omega
  · exact StructuredSpace.sequence_stack_bound hes hec 784 788
      (fun k c hk ht i => (hss k c (Nat.le_succ_of_le hk) ht i).trans (Nat.le_max_left _ _))
      (fun k c hk ht i => (hspace k c hk ht i).trans (Nat.le_max_right _ _))
      (compiled command 784 788) (siteAddress command) (exitAddress command)
      (compiled_site command 784 788)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation
