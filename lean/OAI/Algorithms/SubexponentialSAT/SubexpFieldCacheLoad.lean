import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFieldCacheCall

namespace OAI.Algorithms

/-! Charged loading of the setup-produced exponent and static cache wiring. -/

namespace SubexponentialSAT.SubexpFieldCacheLoad

open BitProgram StructuredCalls StackRoutines SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing SubexpCRTCofactorControl
open SubexpQuarticFlatMul (flat)
open SubexpFieldCacheNodeLoop (PowerValue negativeBytes)
open SubexpFieldCachePairLoop (PairValue)
open SubexpFieldCacheProgram (negativeWords budget)
open SubexpFieldCacheCall (callAt resultStacks)

/-- Ordinary workspace ports. Input134 is framed; output134 is unframed.
Source zero131 is outside the image and remains untouched. -/
def ordinaryPort (i : Fin 110) : Fin 138 :=
  if i = 66 then 128 else if i = 73 then 130 else if i = 74 then 129 else
  if i = 92 then 133 else if i = 93 then 132 else if i = 97 then 134 else
  if i = 98 then 135 else if i = 100 then 136 else if i = 103 then 137 else
  ⟨i.val, by omega⟩

def ordinaryPorts : Fin 110 ↪ Fin 138 := ⟨ordinaryPort, by decide⟩

theorem source_zero_framed : ∀ i, ordinaryPorts i ≠ 131 := by decide

abbrev command {r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 110 ↪ Fin s)
    (source : Fin s) : Cmd r s :=
  .seq (.call (copyProgram source (ports 91) (ports 0) (registers 0) (registers 1)))
    (.seq (callAt registers ports)
      (.call (clearProgram (ports 91) (registers 0) (registers 1))))

def program {r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 110 ↪ Fin s)
    (source : Fin s) := compiled (command registers ports source) source (ports 103)

theorem program_trace {r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 110 ↪ Fin s)
    (source : Fin s) {n : ℕ} {a b : State r s}
    (h : Eval (command registers ports source) n a b) :
    Trace (program registers ports source) (n + 1)
      (a.withPC (some (program registers ports source).entry)) (b.withPC none) :=
  compiled_halt_trace h source (ports 103)

noncomputable def resultRegs {r : ℕ} (registers : Fin 8 ↪ Fin r)
    (rf : Fin 8 → Bool) (ri : Fin r → Bool) : Fin r → Bool :=
  readRegs (Function.extend registers rf (readRegs ri (registers 0) (registers 1) none))
    (registers 0) (registers 1) none

theorem resultRegs_frame {r : ℕ} (registers : Fin 8 ↪ Fin r)
    (rf : Fin 8 → Bool) (ri : Fin r → Bool) (j : Fin r)
    (hj : ¬ ∃ i, registers i = j) : resultRegs registers rf ri j = ri j := by
  have h0 : j ≠ registers 0 := fun h => hj ⟨0, h.symm⟩
  have h1 : j ≠ registers 1 := fun h => hj ⟨1, h.symm⟩
  rw [resultRegs, readRegs_frame _ _ _ _ _ h0 h1,
    Function.extend_apply' _ _ _ hj, readRegs_frame _ _ _ _ _ h0 h1]

theorem update_store_exponent (frame : Fin 110 → List Bool) (w : Words) (bits : List Bool) :
    Function.update (store frame w) 91 bits = store frame {w with exponent := bits} := by
  funext j
  by_cases hj : j = 91
  · subst j; simp
  · simp [store, nativeStore, hj]

private theorem clear_eval {r s : ℕ} (d : State r s) (src : Fin s) (v p : Fin r) :
    Eval (.call (clearProgram src v p)) (2 * (d.stacks src).length + 3) d
      ⟨readRegs d.regs v p none, Function.update d.stacks src []⟩ := by
  apply Eval.call
  simpa only [ListRegisterProgram.Run, clearStacks, StructuredProgram.State.withPC] using
    ListRegisterProgram.clear_run src v p d.regs d.stacks

theorem loaded_stacks {s : ℕ} (ports : Fin 110 ↪ Fin s) (stk : Fin s → List Bool)
    (frame : Fin 110 → List Bool) (base : Words) (bits : List Bool)
    (hstore : ∀ i, stk (ports i) = store frame (SubexpFieldCacheNodeLoop.ready base [] []) i) :
    ∀ i, Function.update stk (ports 91) bits (ports i) =
      store frame (SubexpFieldCacheNodeLoop.ready {base with exponent := bits} [] []) i := by
  intro i
  have hu := congrArg (fun f => f i)
    (update_store_exponent frame (SubexpFieldCacheNodeLoop.ready base [] []) bits)
  by_cases hi : i = 91
  · subst i
    simpa only [Function.update_same, SubexpFieldCacheNodeLoop.ready] using hu
  · have he : ports i ≠ ports 91 := fun h => hi (ports.injective h)
    rw [Function.update_of_ne he, hstore]
    simpa only [Function.update_of_ne hi, SubexpFieldCacheNodeLoop.ready] using hu

theorem clear_loaded_results {s : ℕ} (ports : Fin 110 ↪ Fin s)
    (stk : Fin s → List Bool) (bits nodes inverses negatives differences : List Bool)
    (hz : stk (ports 91) = []) :
    Function.update (resultStacks ports nodes inverses negatives differences
      (Function.update stk (ports 91) bits)) (ports 91) [] =
      resultStacks ports nodes inverses negatives differences stk := by
  funext j
  by_cases hj : j = ports 91
  · subst j
    simp only [Function.update_same]
    symm
    exact (SubexpFieldCacheCall.resultStacks_frame ports _ _ _ _ stk (ports 91)
      (fun h => (by decide : (91 : Fin 110) ≠ 97) (ports.injective h))
      (fun h => (by decide : (91 : Fin 110) ≠ 98) (ports.injective h))
      (fun h => (by decide : (91 : Fin 110) ≠ 100) (ports.injective h))
      (fun h => (by decide : (91 : Fin 110) ≠ 103) (ports.injective h))).trans hz
  · simp only [resultStacks, Function.update_apply, hj, ite_false]

/-- The setup-produced exponent is copied from its preserved source, used by
every actual power call, and cleared from the private workspace on return. -/
theorem command_value {r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 110 ↪ Fin s)
    (source : Fin s) (hsourcePort : ∀ i, source ≠ ports i)
    (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (c : Fin 4 → ZMod (p^μ))
    (t unit : Quad (Word (baseWidth p μ))) (minusOne : Word (baseWidth p μ))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (unit.map (wordValue p μ)) = 1)
    (base : Words) (hm : base.modulus = M.bits) (hr : base.reduction = flat t)
    (hone : base.unit = flat unit) (hmone : base.minusOne = minusOne.val)
    (hw : base.width.length = baseWidth p μ) (hblock : base.blockWidth = [])
    (hexponent : base.exponent = []) (hB : 0 < baseWidth p μ)
    (xs : List (Quad (Word (baseWidth p μ)))) (d : State r s)
    (frame : Fin 110 → List Bool)
    (hsource : frame 97 = ProgramEncoding.encodeRecords (xs.map flat))
    (hnegative : frame 100 = []) (hdifference : frame 103 = []) (houter : frame 106 = [])
    (hstore : ∀ i, d.stacks (ports i) =
      store frame (SubexpFieldCacheNodeLoop.ready base [] []) i) :
    ∃ n rf ys rows,
      n ≤ budget (baseWidth p μ) (d.stacks source) xs.length + 9 * (d.stacks source).length + 9 ∧
      List.Forall₂ (PowerValue p μ c (d.stacks source)) xs ys ∧
      List.Forall₂ (fun node row => List.Forall₂ (PairValue p μ c (d.stacks source) node)
        (negativeWords p μ M minusOne xs) row) xs rows ∧
      Eval (command registers ports source) n d
        ⟨resultRegs registers rf d.regs, resultStacks ports (xs.flatMap flat) (ys.flatMap flat)
          (negativeBytes p μ M minusOne xs) (rows.flatten.flatMap flat) d.stacks⟩ := by
  have hz : d.stacks (ports 91) = [] := by
    rw [hstore]
    exact hexponent
  have htmp : d.stacks (ports 0) = [] := by rw [hstore]; rfl
  have hcopy := copy_eval d source (ports 91) (ports 0) (registers 0) (registers 1)
    (hsourcePort 91) (hsourcePort 0)
    (fun h => (by decide : (0 : Fin 110) ≠ 91) (ports.injective h))
    (fun h => (by decide : (0 : Fin 8) ≠ 1) (registers.injective h)) htmp
  let d1 := afterCopy d source (ports 91) (registers 0) (registers 1)
  have hd1 : d1.stacks = Function.update d.stacks (ports 91) (d.stacks source) := by
    simp only [d1, afterCopy, copyStacks, hz, List.append_nil]
  have hloaded : ∀ i, d1.stacks (ports i) =
      store frame (SubexpFieldCacheNodeLoop.ready {base with exponent := d.stacks source} [] []) i := by
    rw [hd1]
    exact loaded_stacks ports d.stacks frame base (d.stacks source) hstore
  obtain ⟨nb, rb, ys, rows, hnb, hys, hrows, hb⟩ := SubexpFieldCacheCall.callAt_value
    registers ports p μ M c t unit minusOne ht hu {base with exponent := d.stacks source}
    hm hr hone hmone hw hblock hB xs d1 frame hsource hnegative hdifference houter hloaded
  let d2 : State r s := ⟨Function.extend registers rb d1.regs,
    resultStacks ports (xs.flatMap flat) (ys.flatMap flat)
      (negativeBytes p μ M minusOne xs) (rows.flatten.flatMap flat) d1.stacks⟩
  have h91 : d2.stacks (ports 91) = d.stacks source := by
    dsimp only [d2]
    rw [SubexpFieldCacheCall.resultStacks_frame ports _ _ _ _ d1.stacks (ports 91)
      (fun h => (by decide : (91 : Fin 110) ≠ 97) (ports.injective h))
      (fun h => (by decide : (91 : Fin 110) ≠ 98) (ports.injective h))
      (fun h => (by decide : (91 : Fin 110) ≠ 100) (ports.injective h))
      (fun h => (by decide : (91 : Fin 110) ≠ 103) (ports.injective h)), hd1,
      Function.update_same]
  have hc := clear_eval d2 (ports 91) (registers 0) (registers 1)
  have he := hcopy.seq (hb.seq hc)
  refine ⟨7 * (d.stacks source).length + 5 +
      (nb + (2 * (d2.stacks (ports 91)).length + 3)),
    rb, ys, rows, ?_, hys, hrows, ?_⟩
  · rw [h91]
    change nb ≤ budget (baseWidth p μ) (d.stacks source) xs.length + 1 at hnb
    omega
  · simpa only [command, d2, resultRegs, d1, afterCopy, copyStacks, hz, List.append_nil,
      clear_loaded_results ports d.stacks (d.stacks source) _ _ _ _ hz] using he

end SubexponentialSAT.SubexpFieldCacheLoad

end OAI.Algorithms
