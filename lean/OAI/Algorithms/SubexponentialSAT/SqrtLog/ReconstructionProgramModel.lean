import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramModelMiddle
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramState
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramResult

namespace OAI.Algorithms

/-! Complete execution of the fixed native CRT table in the actual searched
ring model. The hypotheses describe input bytes and clean workspace only. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram
open SubexpLiftRing SubexpQuarticRing
open DensePolynomialProgram

private theorem localBudget_index_mono (Q q t d J i j : ℕ) (h : i ≤ j) :
    CRTLocalProgram.Native.budget Q i q t d J ≤ CRTLocalProgram.Native.budget Q j q t d J := by
  unfold CRTLocalProgram.Native.budget CRTLocalProgram.localBudget
    CRTLocalProgram.initializationBudget CRTLocalProgram.preparationBudget
  gcongr

def middleBudget (Q J t d : ℕ) : ℕ :=
  Middle.budget Q J (d*baseWidth 3 t)
    (HornerProgram.Services.mulBudget (baseWidth 3 t) d)
    (HornerProgram.Services.addBudget (baseWidth 3 t) d)
    (CRTLocalProgram.Native.budget Q Q (3^d) t d J)

def budget (Q J t d modulusBits widthTokens : ℕ) : ℕ :=
  Entry.budget modulusBits widthTokens +
    controllerBudget (d*baseWidth 3 t) J Q (middleBudget Q J t d)

theorem command_value (t : ℕ) (ht : 0 < t) {d Q : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hcanon : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (hzbits : cache.zero.val = List.replicate (baseWidth 3 t) false)
    (J : ℕ) (hJpos : 0 < J) (hB : 0 < baseWidth 3 t)
    (nodes : Fin Q → Coeff t d) (jets : Fin Q → CRTLocalProgram.Model.Poly (baseWidth 3 t) d J)
    (minusOne : Coeff t d)
    (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (input : SubexpCRTOuterProgram.Data)
    (hscalar : HornerProgram.Services.NativeReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (NativeState.arithmeticBase input))
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (hpoly : PairSpec.BaseReady 3 t M cache (HornerProgram.modelTable t a M cache)
      (NativeState.arithmeticBase input) scalarWidth frame)
    (hclean : ∀ j ∈ NativeState.cleanPorts, input.stacks j = [])
    (hzero : input.stacks 280 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hone : input.stacks 207 = RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1)
    (hneg : input.stacks 211 = RingProgram.flat minusOne)
    (hJ : input.stacks 243 = List.replicate J true)
    (hnodes : input.stacks 256 = (List.finRange Q).flatMap (fun i => RingProgram.flat (nodes i)))
    (hjets : input.stacks 265 = (List.finRange Q).flatMap (fun i => Fixed.encode (jets i)))
    (hexponent : (input.stacks 209).length = 3^d-2)
    (hprecision : (input.stacks 212).length = t) :
    let ops := RingProgram.modelRing t ht hd a M cache
    let theta := fun i => ops.decode (nodes i)
    ∃ n ≤ budget Q J t d (input.stacks 194).length (input.stacks 202).length,
      ∃ (out : Data) (b : Coeff t d), Eval command n input out ∧
      out.stacks = Function.update (Entry.prepared input.stacks) 261 (RingProgram.flat b) ∧
      ops.decode b = SubexpCRTAtZero.value theta J (LocalValue.inverse theta (3^d) t J)
        (fun i => CRTLocalProgram.Model.denote ops.decode (jets i)) := by
  let ops := RingProgram.modelRing t ht hd a M cache
  obtain ⟨r0, hentry⟩ := Entry.prepare_run input
    (hclean 5 (by simp [NativeState.cleanPorts]))
    (hclean 10 (by simp [NativeState.cleanPorts]))
    (hclean 318 (by simp [NativeState.cleanPorts, initialCleanPorts]))
  let initial : Data := ⟨r0, Entry.prepared input.stacks⟩
  have hw : (initial.stacks 280).length = d*baseWidth 3 t := by
    simp [initial, Entry.prepared, hzero, RingProgram.flat_length]
  have hmiddle : ∀ exponent, BinaryArithmetic.toNat exponent = J → exponent.length ≤ J →
      ∀ processed remaining i acc, List.finRange Q = processed.reverse ++ i :: remaining →
      ∀ rr, ∃ n ≤ middleBudget Q J t d, ∃ rf b,
        Eval middle n
          (sweepState rr (initializedStacks initial J exponent)
            (loadedReady (fun i => RingProgram.flat (nodes i)) (fun i => Fixed.encode (jets i))
              RingProgram.flat processed remaining i acc))
          (sweepState rf (initializedStacks initial J exponent)
            (loadedReady (fun i => RingProgram.flat (nodes i)) (fun i => Fixed.encode (jets i))
              RingProgram.flat processed remaining i b)) ∧
        ops.decode b = ops.decode acc + term t ht hd a M cache nodes J jets i := by
    intro exponent he hl processed remaining i acc hfull rr
    let f := initializedStacks initial J exponent
    let w := loadedReady (fun i => RingProgram.flat (nodes i)) (fun i => Fixed.encode (jets i))
      RingProgram.flat processed remaining i acc
    let current := sweepState rr f w
    have hbase : ((Function.update initial.stacks 104 (initial.stacks 280)) ∘ localPorts) =
        NativeState.arithmeticBase input := by
      simp [NativeState.arithmeticBase, initial, Entry.prepared]
    have hf : CRTLocalProgram.LowFrame (NativeState.arithmeticBase input) (current.stacks ∘ localPorts) := by
      intro j hj
      have h1 := loaded_low f (fun i => RingProgram.flat (nodes i)) (fun i => Fixed.encode (jets i))
        RingProgram.flat processed remaining i acc j hj
      have h2 := NativeState.initialized_low initial J exponent j hj
      rw [hbase] at h2
      exact h1.trans h2
    have hc := NativeState.workingClean_frame initial J exponent
      (fun i => RingProgram.flat (nodes i)) (fun i => Fixed.encode (jets i)) RingProgram.flat
      processed remaining i acc (NativeState.entry_workingClean input hclean)
    have hcMiddle : ∀ j ∈ Middle.cleanPorts, current.stacks j = [] := by
      intro j hj; exact hc j (by simp [NativeState.workingClean, hj])
    have hcLocal : ∀ j ∈ CRTLocalProgram.localWork, current.stacks (localPorts j) = [] := by
      intro j hj
      have hm : localPorts j ∈ CRTLocalProgram.localWork.map localPorts :=
        List.mem_map.mpr ⟨j, hj, rfl⟩
      exact hc _ (by simp only [NativeState.workingClean, List.mem_append, hm, or_true, true_or])
    have hcBuffers : ∀ j, current.stacks (localPorts (SubexpConvolutionControl.bufferPorts j)) = [] := by
      intro j
      have hm : localPorts (SubexpConvolutionControl.bufferPorts j) ∈
          (List.ofFn fun i => localPorts (SubexpConvolutionControl.bufferPorts i)) :=
        List.mem_ofFn.mpr ⟨j, rfl⟩
      exact hc _ (by simp only [NativeState.workingClean, List.mem_append, hm, or_true])
    have hidx := traversal_index processed remaining i hfull
    obtain ⟨n, hn, rf, b, heval, hvalue⟩ := middle_run t ht hd a M cache hcanon hzbits J hJpos hB
      nodes jets minusOne acc hminus processed remaining i hfull current
      (hscalar.frame hf) scalarWidth frame
      (PairSpec.BaseReady.frame 3 t M cache (HornerProgram.modelTable t a M cache) hpoly hf)
      hcBuffers hcMiddle hcLocal
      (by simp [current, f, initial, Entry.prepared, sweepState, sweepStore, initializedStacks, hzero])
      (by simp [current, f, initial, Entry.prepared, sweepState, sweepStore, initializedStacks, hone])
      (by simp [current, f, initial, Entry.prepared, sweepState, sweepStore, initializedStacks, hneg])
      (by simp [current, w, sweepState, loadedReady, loadedWords, readyWords])
      (by simp [current, f, initial, Entry.prepared, sweepState, sweepStore, initializedStacks,
        hnodes, List.ofFn_eq_map, List.flatMap_map])
      (by simpa [current, w, sweepState, loadedReady, loadedWords, readyWords] using hidx)
      (by simp [current, w, sweepState, loadedReady, loadedWords, readyWords])
      (by simp [current, f, initial, Entry.prepared, sweepState, sweepStore, initializedStacks, hJ])
      (by simp [current, w, sweepState, loadedReady, loadedWords, readyWords, List.flatMap_map])
      (by simp [current, w, sweepState, loadedReady, loadedWords, readyWords, List.flatMap_map])
      (by simp [current, w, sweepState, loadedReady, loadedWords, readyWords])
      (by simp [current, w, sweepState, loadedReady, loadedWords, readyWords])
      (by simp [current, f, initial, Entry.prepared, sweepState, sweepStore, initializedStacks,
        hzero, Subexp.BlockCopyProgram.copies, DensePolynomialProgram.encode])
      (by simpa [current, f, initial, Entry.prepared, sweepState, sweepStore, initializedStacks] using hexponent)
      (by simpa [current, f, initial, Entry.prepared, sweepState, sweepStore, initializedStacks] using hprecision)
    have hbound := middleBudget_mono (Q:=Q) (J:=J) (W:=d*baseWidth 3 t)
      (Km:=HornerProgram.Services.mulBudget (baseWidth 3 t) d)
      (Ka:=HornerProgram.Services.addBudget (baseWidth 3 t) d)
      le_rfl le_rfl le_rfl le_rfl le_rfl
      (localBudget_index_mono Q (3^d) t d J i.val Q (Nat.le_of_lt i.isLt))
    refine ⟨n, hn.trans hbound, rf, b, ?_, hvalue⟩
    have hout : Function.update current.stacks 261 (RingProgram.flat b) =
        (sweepState rf f (loadedReady (fun i => RingProgram.flat (nodes i))
          (fun i => Fixed.encode (jets i)) RingProgram.flat processed remaining i b)).stacks :=
      loaded_update_acc f _ _ _ processed remaining i acc b
    have hstate : (⟨rf, Function.update current.stacks 261 (RingProgram.flat b)⟩ : Data) =
        sweepState rf f (loadedReady (fun i => RingProgram.flat (nodes i))
          (fun i => Fixed.encode (jets i)) RingProgram.flat processed remaining i b) :=
      SubexpScanPrimitives.state_ext rfl hout
    rw [hstate] at heval
    exact heval
  obtain ⟨n, hn, out, b, hrun, hout, hvalue⟩ := controller_run_framed
    (fun i => RingProgram.flat (nodes i)) (fun i => Fixed.encode (jets i)) RingProgram.flat
    ops.decode (term t ht hd a M cache nodes J jets) middle initial J (middleBudget Q J t d)
    (List.finRange Q) ops.zeroRun.1
    (by simp [initial, Entry.prepared, hJ]) (NativeState.entry_initialClean input hclean)
    (by intro i; simp [hw, RingProgram.flat_length])
    (by intro i; simp [hw, Fixed.encode_length]) (by rw [hw]; exact Nat.mul_pos hd hB)
    (by simpa [initial, Entry.prepared] using hnodes)
    (by simpa [initial, Entry.prepared] using hjets)
    (by simp [initial, Entry.prepared, hzero, ops]; rfl) ops.zero_correct hmiddle
  refine ⟨_, ?_, out, b, hentry.seq hrun, hout, ?_⟩
  · simpa only [budget, hw, List.length_finRange] using Nat.add_le_add_left hn
      (Entry.budget (input.stacks 194).length (input.stacks 202).length)
  · have hsum := Middle.sum_node_terms
      (fun i => ops.decode (nodes i)) J (LocalValue.inverse (fun i => ops.decode (nodes i)) (3^d) t J)
      (fun i => CRTLocalProgram.Model.denote ops.decode (jets i))
    apply hvalue.trans
    change (List.map (fun i =>
      (JetCRT.cofactor (fun i => ops.decode (nodes i)) J i).eval 0 *
        (TruncatedInverse.correction (fun i => ops.decode (nodes i)) J
          (LocalValue.inverse (fun i => ops.decode (nodes i)) (3 ^ d) t J)
          (fun i => CRTLocalProgram.Model.denote ops.decode (jets i)) i).eval
            (-(ops.decode (nodes i)))) (List.finRange Q)).sum = _
    exact hsum

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

end OAI.Algorithms
