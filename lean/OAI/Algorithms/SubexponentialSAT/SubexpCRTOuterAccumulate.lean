import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterSetup
import OAI.Algorithms.SubexponentialSAT.SubexpCRTWeightedMachine

namespace OAI.Algorithms

/-!
# Physical weighted update for the outer CRT controller

The stored accumulator at 261, cofactor at 262, and evaluated correction at
264 are moved/copied into the actual scalar service. The final accumulator
returns to 261; the consumed cofactor, negative point, and evaluation stacks
are cleared. Every other stack, including all native arithmetic work, is
restored. The command has no parameter-dependent instruction table.
-/

namespace SubexponentialSAT.SubexpCRTOuterAccumulate

open BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram
open SubexpLiftRing SubexpQuarticRing
open SubexpCRTCofactorControl (Words store)
open SubexpQuarticFlatMul (flat)

def command : Code :=
  .seq (move 261 226) (.seq (copy 262 222) (.seq (move 264 223)
    (.seq (SubexpCRTWeightedMachine.callAt registers scalarPorts)
      (.seq (move 226 261) (clearMany [222,223,262,263])))))

abbrev program : Program 16 320 (size command + 1) := compiled command 261 261

def idleWords (w : Words) : Words :=
  { w with accumulator := [], node := [], negative := [], left := [], right := [], result := [] }

def loadedWords {B : ℕ} (w : Words) (a factor value : Quad (Word B)) : Words :=
  { idleWords w with accumulator := flat a, node := flat factor, negative := flat value }

def resultStacks (s : Fin 320 → List Bool) (out : List Bool) : Fin 320 → List Bool :=
  Function.update (Function.update (Function.update (Function.update s 261 out)
    262 []) 263 []) 264 []

def runtimeBound (B : ℕ) : ℕ :=
  SubexpCRTWeightedMachine.runtimeBound B + 132 * B + 35

private theorem loaded_store {B : ℕ} (frame : Fin 110 → List Bool) (w : Words)
    (a factor value : Quad (Word B)) :
    store frame (loadedWords w a factor value) =
      Function.update (Function.update (Function.update (store frame (idleWords w))
        98 (flat a)) 94 (flat factor)) 95 (flat value) := by
  rw [SubexpCRTCofactorControl.update_store_accumulator,
    SubexpCRTCofactorControl.update_store_node,
    SubexpCRTCofactorControl.update_store_negative]
  all_goals rfl

/-- The service is called with actual stored arithmetic data. The result is
the exact prepared binary addition of the prepared binary product. -/
theorem command_eval (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ)
    (t a factor value : Quad (Word (baseWidth p μ)))
    (frame : Fin 110 → List Bool) (w : Words)
    (hm : w.modulus = M.bits) (ht : w.reduction = flat t)
    (hw : w.width.length = baseWidth p μ) (d : Data)
    (ha : d.stacks 261 = flat a) (hf : d.stacks 262 = flat factor)
    (hv : d.stacks 264 = flat value)
    (hnegative : (d.stacks 263).length = 4 * baseWidth p μ)
    (h318 : d.stacks 318 = []) (h319 : d.stacks 319 = [])
    (hstore : ∀ i, d.stacks (scalarPorts i) = store frame (idleWords w) i) :
    ∃ (n : ℕ) (rf : Fin 16 → Bool), n ≤ runtimeBound (baseWidth p μ) ∧
      Eval command n d
        ⟨rf, resultStacks d.stacks
          (flat (SubexpCRTWeightedMachine.stepValue p μ M t a factor value))⟩ := by
  let B := baseWidth p μ
  let output := SubexpCRTWeightedMachine.stepValue p μ M t a factor value
  have h222 : d.stacks 222 = [] := by
    change d.stacks (scalarPorts 94) = []
    simpa [idleWords] using hstore 94
  have h223 : d.stacks 223 = [] := by
    change d.stacks (scalarPorts 95) = []
    simpa [idleWords] using hstore 95
  have h226 : d.stacks 226 = [] := by
    change d.stacks (scalarPorts 98) = []
    simpa [idleWords] using hstore 98
  let d1 := moved d 261 226
  have h1 : Eval (move 261 226) (24 * B + 6) d d1 := by
    simpa [d1, ha, SubexpQuarticFlatMul.flat_length, B, ← Nat.mul_assoc] using
      move_run d 261 226 (by decide) (by decide) (by decide) h319 h226
  let d2 := afterCopy d1 262 222 0 1
  have h2 : Eval (copy 262 222) (28 * B + 5) d1 d2 := by
    have h := copy_run d1 262 222 (by decide) (by decide) (by decide)
      (by simpa [d1, moved] using h318)
    simpa [d2, d1, moved, hf, SubexpQuarticFlatMul.flat_length, B, ← Nat.mul_assoc] using h
  let d3 := moved d2 264 223
  have h3 : Eval (move 264 223) (24 * B + 6) d2 d3 := by
    have h := move_run d2 264 223 (by decide) (by decide) (by decide)
      (by simpa [d2, d1, moved, afterCopy, StackRoutines.copyStacks] using h319)
      (by simpa [d2, d1, moved, afterCopy, StackRoutines.copyStacks] using h223)
    simpa [d3, d2, d1, moved, afterCopy, StackRoutines.copyStacks,
      hv, SubexpQuarticFlatMul.flat_length, B, ← Nat.mul_assoc] using h
  have hprepared : d3.stacks =
      Function.update (Function.update (Function.update (Function.update
        (Function.update d.stacks 261 []) 226 (flat a)) 222 (flat factor))
          264 []) 223 (flat value) := by
    simp [d3, d2, d1, afterCopy, StackRoutines.copyStacks, ha, hf, hv, h222]
  have hlocal : ∀ i, d3.stacks (scalarPorts i) =
      store frame (loadedWords w a factor value) i := by
    intro i
    have h94 : scalarPorts i = (222 : Fin 320) ↔ i = 94 := by
      change scalarPorts i = scalarPorts (94 : Fin 110) ↔ i = 94
      exact scalarPorts.injective.eq_iff
    have h95 : scalarPorts i = (223 : Fin 320) ↔ i = 95 := by
      change scalarPorts i = scalarPorts (95 : Fin 110) ↔ i = 95
      exact scalarPorts.injective.eq_iff
    have h98 : scalarPorts i = (226 : Fin 320) ↔ i = 98 := by
      change scalarPorts i = scalarPorts (98 : Fin 110) ↔ i = 98
      exact scalarPorts.injective.eq_iff
    have h261 : scalarPorts i ≠ (261 : Fin 320) := by
      intro h
      have hv' := congrArg Fin.val h
      change 128 + i.val = 261 at hv'
      have hi := i.isLt
      omega
    have h264 : scalarPorts i ≠ (264 : Fin 320) := by
      intro h
      have hv' := congrArg Fin.val h
      change 128 + i.val = 264 at hv'
      have hi := i.isLt
      omega
    rw [hprepared, loaded_store]
    simp only [Function.update_apply, h94, h95, h98, h261, h264, ite_false, hstore]
  obtain ⟨n, rf, hn, he⟩ := SubexpCRTWeightedMachine.callAt_eval registers scalarPorts
    p μ M t a factor value frame (loadedWords w a factor value)
    hm ht rfl rfl rfl rfl rfl rfl hw d3 hlocal
  let d4 : Data := ⟨Function.extend registers rf d3.regs,
    Function.update d3.stacks 226 (flat output)⟩
  have h4 : Eval (SubexpCRTWeightedMachine.callAt registers scalarPorts) n d3 d4 := by
    simpa only [d4, output, show scalarPorts 98 = (226 : Fin 320) from rfl] using he
  let d5 := moved d4 226 261
  have h5 : Eval (move 226 261) (24 * B + 6) d4 d5 := by
    have h := move_run d4 226 261 (by decide) (by decide) (by decide)
      (by simpa [d4, hprepared] using h319)
      (by simp [d4, hprepared])
    simpa [d5, d4, SubexpQuarticFlatMul.flat_length, B, ← Nat.mul_assoc] using h
  let d6 := SubexpSetupStorage.clearManyState [222,223,262,263] d5
  have h6 : Eval (clearMany [222,223,262,263]) (32 * B + 12) d5 d6 := by
    have h := clearMany_run d5 [222,223,262,263]
    have hc : SubexpSetupStorage.clearManyCost [222,223,262,263] d5 = 32 * B + 12 := by
      simp [d5, d4, hprepared, SubexpSetupStorage.clearManyCost,
        SubexpSetupStorage.clearState, hf, hnegative, SubexpQuarticFlatMul.flat_length,
        B, ← Nat.mul_assoc]
      all_goals omega
    simpa only [hc] using h
  have hout : d6.stacks = resultStacks d.stacks (flat output) := by
    funext i
    by_cases h222' : i = 222
    · subst i
      simp [d6, d5, d4, hprepared, SubexpSetupStorage.clearManyState,
        SubexpSetupStorage.clearState, resultStacks, h222]
    by_cases h223' : i = 223
    · subst i
      simp [d6, d5, d4, hprepared, SubexpSetupStorage.clearManyState,
        SubexpSetupStorage.clearState, resultStacks, h223]
    by_cases h226' : i = 226
    · subst i
      simp [d6, d5, d4, hprepared, SubexpSetupStorage.clearManyState,
        SubexpSetupStorage.clearState, resultStacks, h226]
    by_cases h261' : i = 261
    · subst i
      simp [d6, d5, d4, hprepared, SubexpSetupStorage.clearManyState,
        SubexpSetupStorage.clearState, resultStacks]
    by_cases h262' : i = 262
    · subst i
      simp [d6, d5, d4, hprepared, SubexpSetupStorage.clearManyState,
        SubexpSetupStorage.clearState, resultStacks]
    by_cases h263' : i = 263
    · subst i
      simp [d6, d5, d4, hprepared, SubexpSetupStorage.clearManyState,
        SubexpSetupStorage.clearState, resultStacks]
    by_cases h264' : i = 264
    · subst i
      simp [d6, d5, d4, hprepared, SubexpSetupStorage.clearManyState,
        SubexpSetupStorage.clearState, resultStacks]
    simp [d6, d5, d4, hprepared, SubexpSetupStorage.clearManyState,
      SubexpSetupStorage.clearState, resultStacks,
      h222', h223', h226', h261', h262', h263', h264']
  have hfinal : d6 = (⟨d6.regs, resultStacks d.stacks (flat output)⟩ : Data) :=
    state_ext rfl hout
  have hrun := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))
  rw [hfinal] at hrun
  refine ⟨_, d6.regs, ?_, hrun⟩
  change n ≤ SubexpCRTWeightedMachine.runtimeBound B at hn
  change _ ≤ SubexpCRTWeightedMachine.runtimeBound B + 132 * B + 35
  omega

/-- The final halt is included in this standalone machine interface. -/
theorem program_run (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ)
    (t a factor value : Quad (Word (baseWidth p μ)))
    (frame : Fin 110 → List Bool) (w : Words)
    (hm : w.modulus = M.bits) (ht : w.reduction = flat t)
    (hw : w.width.length = baseWidth p μ) (d : Data)
    (ha : d.stacks 261 = flat a) (hf : d.stacks 262 = flat factor)
    (hv : d.stacks 264 = flat value)
    (hnegative : (d.stacks 263).length = 4 * baseWidth p μ)
    (h318 : d.stacks 318 = []) (h319 : d.stacks 319 = [])
    (hstore : ∀ i, d.stacks (scalarPorts i) = store frame (idleWords w) i) :
    ∃ rf : Fin 16 → Bool,
      RunsIn program (runtimeBound (baseWidth p μ) + 1)
        (d.withPC (some program.entry))
        ((⟨rf, resultStacks d.stacks
          (flat (SubexpCRTWeightedMachine.stepValue p μ M t a factor value))⟩ : Data).withPC none) := by
  obtain ⟨n, rf, hn, he⟩ := command_eval p μ M t a factor value frame w hm ht hw d
    ha hf hv hnegative h318 h319 hstore
  exact ⟨rf, n + 1, Nat.add_le_add_right hn 1, compiled_halt_trace he 261 261⟩

end SubexponentialSAT.SubexpCRTOuterAccumulate

end OAI.Algorithms
