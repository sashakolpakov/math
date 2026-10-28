import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTCofactorLoop
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticFlatNeg
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticPowerProgram
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticFlatLift

namespace OAI.Algorithms

/-! Actual streaming scalar CRT cofactor: negate each supplied node, raise it
to the runtime exponent, and multiply into a fixed-width accumulator. The
supplied node stream omits the current CRT node; the outer traversal constructs
that stream from its processed and remaining node lists.
-/

namespace SubexponentialSAT.SubexpCRTCofactorMachine

open BitProgram StructuredCalls StackRoutines SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing SubexpCRTCofactorControl
open SubexpQuarticFlatMul (flat)

abbrev negate : Cmd 8 110 :=
  SubexpQuarticFlatNeg.callAt registers negPorts

abbrev power : Cmd 8 110 :=
  SubexpQuarticPowerProgram.callAt powerPorts

abbrev multiply : Cmd 8 110 :=
  .call (SubexpQuarticFlatLift.programAt registers mulPorts)

abbrev iteration : Cmd 8 110 :=
  SubexpCRTCofactorControl.iteration negate power multiply

abbrev command : Cmd 8 110 :=
  SubexpCRTCofactorControl.command negate power multiply

abbrev program : Program 8 110 (size command + 1) := compiled command 99 98

theorem neg_flat_eq {B : ℕ} (a : Quad (Word B)) :
    SubexpQuarticFlatNeg.flat a = flat a := rfl

theorem negate_eval (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (a : Quad (Word (baseWidth p μ))) (minusOne : Word (baseWidth p μ))
    (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool) (w : Words)
    (hm : w.modulus = M.bits) (ha : w.node = flat a)
    (hone : w.minusOne = minusOne.val) (hn : w.negative = [])
    (hw : w.width.length = baseWidth p μ) :
    ∃ n rf, n ≤ 25000 * (baseWidth p μ + 1)^2 ∧
      Eval negate n (state regs frame w)
        (state rf frame {w with negative := flat (SubexpQuarticNegMachine.negateWords p μ M minusOne a)}) := by
  have hlocal : ∀ i, (state regs frame w).stacks (negPorts i) =
      SubexpQuarticFlatNeg.initialStore a minusOne M.bits w.width i := by
    intro i
    fin_cases i <;> simp [state, negPorts, negPort, store, nativeStore,
      SubexpQuarticFlatMul.bankStore, SubexpQuarticFlatNeg.initialStore,
      SubexpQuarticFlatNeg.bankStore, SubexpQuarticFlatNeg.emptyBank,
      hm, ha, hone, hn, neg_flat_eq, Fin.coe_ofNat_eq_mod]
  obtain ⟨n, rf, hb, ht⟩ := SubexpQuarticFlatNeg.callAt_eval registers negPorts
    p μ M a minusOne w.width hw (state regs frame w) hlocal
  refine ⟨n, rf, hb, ?_⟩
  simpa only [negate, registers, Function.Embedding.coeFn_mk,
    ProgramLinking.extend_id, state, show negPorts 19 = (95 : Fin 110) from rfl,
    neg_flat_eq, update_store_negative] using ht

@[simp] theorem powerPorts_native (i : Fin 77) :
    powerPorts (SubexpQuarticPowerProgram.native i) = mulPorts i := by
  have hn (j : Fin 110) (hj : 77 ≤ j.val) : mulPorts i ≠ j := by
    intro h
    have hv := congrArg (fun x : Fin 110 => x.val) h
    change i.val = j.val at hv
    omega
  change powerRelabel (mulPorts i) = mulPorts i
  simp [powerRelabel, Equiv.swap_apply_def,
    hn 77 (by decide), hn 95 (by decide), hn 78 (by decide), hn 91 (by decide),
    hn 79 (by decide), hn 93 (by decide), hn 80 (by decide), hn 96 (by decide)]

@[simp] theorem powerPorts_base : powerPorts 77 = (95 : Fin 110) := by decide
@[simp] theorem powerPorts_exponent : powerPorts 78 = (91 : Fin 110) := by decide
@[simp] theorem powerPorts_unit : powerPorts 79 = (93 : Fin 110) := by decide
@[simp] theorem powerPorts_output : powerPorts 80 = (96 : Fin 110) := by decide
@[simp] theorem powerPorts_counter : powerPorts 81 = (81 : Fin 110) := by decide
@[simp] theorem powerPorts_scratch : powerPorts 82 = (82 : Fin 110) := by decide

theorem power_eval (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (c : Fin 4 → ZMod (p^μ)) (t a unit : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (unit.map (wordValue p μ)) = 1)
    (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool) (w : Words)
    (hm : w.modulus = M.bits) (hr : w.reduction = flat t)
    (ha : w.negative = flat a) (hone : w.unit = flat unit)
    (hleft : w.left = []) (hright : w.right = []) (hresult : w.result = [])
    (hout : w.power = []) (hw : w.width.length = baseWidth p μ) :
    ∃ n rf b, Eval power n (state regs frame w) (state rf frame {w with power := flat b}) ∧
      quotientDenote c (b.map (wordValue p μ)) =
        quotientDenote c (a.map (wordValue p μ)) ^ BinaryArithmetic.toNat w.exponent ∧
      n ≤ SubexpQuarticPowerProgram.runtimeBound (baseWidth p μ) w.exponent := by
  have hnative : ∀ i, (state regs frame w).stacks
      (powerPorts (SubexpQuarticPowerProgram.native i)) =
        SubexpQuarticPowerProgram.cleanNative M.bits (flat t) w.width i := by
    intro i
    simp only [powerPorts_native, state, store_native]
    by_cases hi70 : i = 70
    · subst i
      simp [nativeStore, SubexpQuarticPowerProgram.cleanNative,
        SubexpQuarticPowerCore.cleanNative, SubexpQuarticFlatMul.bankStore, hleft, hright]
    · by_cases hi71 : i = 71
      · subst i
        simp [nativeStore, SubexpQuarticPowerProgram.cleanNative,
          SubexpQuarticPowerCore.cleanNative, SubexpQuarticFlatMul.bankStore, hright]
      · simp [nativeStore, SubexpQuarticPowerProgram.cleanNative,
          SubexpQuarticPowerCore.cleanNative, hi70, hi71, hm, hr, hresult]
  obtain ⟨n, rf, b, he, hv, hb⟩ := SubexpQuarticPowerProgram.callAt_eval powerPorts
    p μ M c t a unit ht hu w.width hw (state regs frame w) hnative
    (by simpa [state] using ha) (by simpa [state] using hone)
    (by simpa [state] using hout) (by simp [state]) (by simp [state])
  refine ⟨n, rf, b, ?_, ?_, ?_⟩
  · simpa only [power, powerPorts_output, state, update_store_power] using he
  · simpa only [powerPorts_exponent, state, store_exponent] using hv
  · simpa only [powerPorts_exponent, state, store_exponent] using hb


theorem multiply_eval (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (t a b : Quad (Word (baseWidth p μ)))
    (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool) (w : Words)
    (hm : w.modulus = M.bits) (hr : w.reduction = flat t)
    (ha : w.left = flat a) (hb : w.right = flat b) (hz : w.result = [])
    (hw : w.width.length = baseWidth p μ) :
    ∃ n rf, n ≤ 400000 * (baseWidth p μ + 1)^2 ∧
      Eval multiply n (state regs frame w)
        (state rf frame {w with
          left := []
          right := []
          result := flat (SubexpPreparedQuartic.binaryMul p μ M t a b).1}) := by
  have hlocal : ∀ i, (state regs frame w).stacks (mulPorts i) =
      SubexpQuarticFlatMul.initialStore M.bits w.width t a b i := by
    intro i
    simp only [state, store_native, nativeStore, SubexpQuarticFlatMul.initialStore,
      hm, hr, ha, hb, hz]
  obtain ⟨n, rf, hn, he⟩ := SubexpQuarticFlatLift.programAt_eval registers mulPorts
    p μ M t a b w.width hw regs (store frame w) hlocal
  refine ⟨n, rf, hn, ?_⟩
  simpa only [multiply, SubexpQuarticFlatLift.resultRegs, registers, Function.Embedding.coeFn_mk,
    ProgramLinking.extend_id, SubexpQuarticFlatLift.resultStacks,
    show mulPorts 70 = (70 : Fin 110) from rfl,
    show mulPorts 71 = (71 : Fin 110) from rfl,
    show mulPorts 72 = (72 : Fin 110) from rfl,
    update_store_left, update_store_right, update_store_result, state] using he

def iterationBudget (B : ℕ) (exponent : List Bool) : ℕ :=
  25000 * (B + 1)^2 + SubexpQuarticPowerProgram.runtimeBound B exponent +
    400000 * (B + 1)^2 + 144 * B + 35

def runtimeBound (B : ℕ) (exponent : List Bool) (nodes : ℕ) : ℕ :=
  28 * B + nodes * (iterationBudget B exponent + 2) + 8

def polynomialBound (W : ℕ) : ℕ :=
  28 * W + W * (425000 * (W + 1)^2 + 500000 * (W + 1)^3 + 144 * W + 37) + 8

/-- The actual instruction bound is quartic in one bound for node count,
coefficient width, exponent bit length, and the numerical exponent D. -/
theorem runtimeBound_le (B : ℕ) (exponent : List Bool) (nodes W : ℕ)
    (hB : B ≤ W) (hE : exponent.length ≤ W)
    (hD : BinaryArithmetic.toNat exponent ≤ W) (hN : nodes ≤ W) :
    runtimeBound B exponent nodes ≤ polynomialBound W := by
  have hp := SubexpQuarticPowerProgram.runtimeBound_le B exponent W hB hE hD
  have hs := Nat.pow_le_pow_left (Nat.add_le_add_right hB 1) 2
  have h25 := Nat.mul_le_mul_left 25000 hs
  have h400 := Nat.mul_le_mul_left 400000 hs
  have h144 := Nat.mul_le_mul_left 144 hB
  have hi : iterationBudget B exponent + 2 ≤
      425000 * (W + 1)^2 + 500000 * (W + 1)^3 + 144 * W + 37 := by
    unfold iterationBudget
    omega
  have hn := Nat.mul_le_mul hN hi
  have h28 := Nat.mul_le_mul_left 28 hB
  unfold runtimeBound polynomialBound
  omega

noncomputable def decode (p μ : ℕ) [Fact p.Prime] (c : Fin 4 → ZMod (p^μ))
    (a : Quad (Word (baseWidth p μ))) :=
  quotientDenote c (a.map (wordValue p μ))

/-- One actual node iteration: consume its four words, negate, exponentiate,
multiply, and clear all transient operands. -/
theorem iteration_value (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (c : Fin 4 → ZMod (p^μ)) (t unit : Quad (Word (baseWidth p μ)))
    (minusOne : Word (baseWidth p μ))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : decode p μ c unit = 1) (hminus : wordValue p μ minusOne = -1)
    (base : Words) (frame : Fin 110 → List Bool)
    (hm : base.modulus = M.bits) (hr : base.reduction = flat t)
    (hunit : base.unit = flat unit) (hminusWord : base.minusOne = minusOne.val)
    (hw : base.width.length = baseWidth p μ)
    (hblock : base.blockWidth.length = 4 * baseWidth p μ)
    (cs : List (Quad (Word (baseWidth p μ))))
    (a node : Quad (Word (baseWidth p μ))) (regs : Fin 8 → Bool) :
    ∃ n ≤ iterationBudget (baseWidth p μ) base.exponent, ∃ rf b,
      Eval iteration n
        (state regs frame (SubexpCRTCofactorLoop.readyWords flat base (node :: cs) a))
        (state rf frame (SubexpCRTCofactorLoop.readyWords flat base cs b)) ∧
      decode p μ c b = decode p μ c a *
        (-decode p μ c node) ^ BinaryArithmetic.toNat base.exponent := by
  let w := SubexpCRTCofactorLoop.readyWords flat base (node :: cs) a
  let rest := cs.flatMap flat
  let wn := SubexpCRTCofactorLoop.takenWords w (flat node) rest
  let neg := SubexpQuarticNegMachine.negateWords p μ M minusOne node
  obtain ⟨nn, rn, hnn, hn⟩ := negate_eval p μ M node minusOne
    (readRegs regs 0 1 none) frame wn hm rfl hminusWord rfl hw
  obtain ⟨np, rp, powered, hp, hpv, hnp⟩ := power_eval p μ M c t neg unit ht hu
    rn frame {wn with negative := flat neg} hm hr rfl hunit rfl rfl rfl rfl hw
  let wp := SubexpCRTCofactorLoop.poweredWords w (flat node) rest (flat neg) (flat powered)
  let wo := SubexpCRTCofactorLoop.operandWords wp
  let result := (SubexpPreparedQuartic.binaryMul p μ M t a powered).1
  obtain ⟨nm, rm, hnm, hmul⟩ := multiply_eval p μ M t a powered
    (readRegs rp 0 1 none) frame wo hm hr rfl rfl rfl hw
  have he := SubexpCRTCofactorLoop.iteration_eval negate power multiply
    regs rn rp rm frame w (flat node) rest (flat neg) (flat powered) (flat result)
    nn np nm rfl (by simpa [w, SubexpCRTCofactorLoop.readyWords,
      SubexpQuarticFlatMul.flat_length] using hblock)
    rfl rfl rfl hn hp hmul
  let n := 16 * (flat node).length + 6 * w.accumulator.length +
    6 * (flat powered).length + 6 * (flat result).length + 2 * (flat neg).length +
    nn + np + nm + 35
  refine ⟨n, ?_, readRegs rm 0 1 none, result, ?_, ?_⟩
  · simp only [n, w, SubexpCRTCofactorLoop.readyWords,
      SubexpQuarticFlatMul.flat_length, iterationBudget]
    change np ≤ SubexpQuarticPowerProgram.runtimeBound (baseWidth p μ) base.exponent at hnp
    omega
  · exact he
  · change decode p μ c (SubexpPreparedQuartic.binaryMul p μ M t a powered).1 = _
    rw [decode, SubexpPreparedQuartic.binaryMul_quotient p μ M c t a powered ht]
    rw [hpv, SubexpQuarticNegMachine.negateWords_quotient p μ M minusOne node hminus c]
    rfl

/-- A fixed finite program computes the scalar cofactor on a supplied stream
of all other CRT nodes. Only the runtime stream and exponent vary. -/
theorem command_value (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (c : Fin 4 → ZMod (p^μ)) (t unit : Quad (Word (baseWidth p μ)))
    (minusOne : Word (baseWidth p μ))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : decode p μ c unit = 1) (hminus : wordValue p μ minusOne = -1)
    (base : Words) (frame : Fin 110 → List Bool)
    (hm : base.modulus = M.bits) (hr : base.reduction = flat t)
    (hunit : base.unit = flat unit) (hminusWord : base.minusOne = minusOne.val)
    (hw : base.width.length = baseWidth p μ)
    (hblock : base.blockWidth.length = 4 * baseWidth p μ)
    (hB : 0 < baseWidth p μ)
    (cs : List (Quad (Word (baseWidth p μ)))) (regs : Fin 8 → Bool) :
    ∃ n rf b,
      Eval command n
        (state regs frame (SubexpCRTCofactorLoop.initialWords flat base cs))
        (state rf frame (SubexpCRTCofactorLoop.readyWords flat base [] b)) ∧
      decode p μ c b =
        (cs.map (fun node => (-decode p μ c node) ^ BinaryArithmetic.toNat base.exponent)).prod ∧
      n + 1 ≤ runtimeBound (baseWidth p μ) base.exponent cs.length := by
  have hne (a : Quad (Word (baseWidth p μ))) : flat a ≠ [] := by
    intro h
    have hl := congrArg List.length h
    simp only [SubexpQuarticFlatMul.flat_length, List.length_nil] at hl
    omega
  obtain ⟨n, hn, rf, b, he, hv⟩ := SubexpCRTCofactorLoop.command_eval flat
    (decode p μ c) (fun node => (-decode p μ c node) ^ BinaryArithmetic.toNat base.exponent)
    base frame negate power multiply (iterationBudget (baseWidth p μ) base.exponent)
    hne unit hu hunit
    (fun regs cs a node => iteration_value p μ M c t unit minusOne ht hu hminus
      base frame hm hr hunit hminusWord hw hblock cs a node regs) cs regs
  refine ⟨n, rf, b, he, hv, ?_⟩
  simp only [SubexpQuarticFlatMul.flat_length] at hn
  unfold runtimeBound
  omega

theorem program_run (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (c : Fin 4 → ZMod (p^μ)) (t unit : Quad (Word (baseWidth p μ)))
    (minusOne : Word (baseWidth p μ))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : decode p μ c unit = 1) (hminus : wordValue p μ minusOne = -1)
    (base : Words) (frame : Fin 110 → List Bool)
    (hm : base.modulus = M.bits) (hr : base.reduction = flat t)
    (hunit : base.unit = flat unit) (hminusWord : base.minusOne = minusOne.val)
    (hw : base.width.length = baseWidth p μ)
    (hblock : base.blockWidth.length = 4 * baseWidth p μ)
    (hB : 0 < baseWidth p μ)
    (cs : List (Quad (Word (baseWidth p μ)))) (regs : Fin 8 → Bool) :
    ∃ rf b, decode p μ c b =
        (cs.map (fun node => (-decode p μ c node) ^ BinaryArithmetic.toNat base.exponent)).prod ∧
      RunsIn program (runtimeBound (baseWidth p μ) base.exponent cs.length)
        ((state regs frame (SubexpCRTCofactorLoop.initialWords flat base cs)).withPC
          (some program.entry))
        ((state rf frame (SubexpCRTCofactorLoop.readyWords flat base [] b)).withPC none) := by
  obtain ⟨n, rf, b, he, hv, hn⟩ := command_value p μ M c t unit minusOne ht hu hminus
    base frame hm hr hunit hminusWord hw hblock hB cs regs
  exact ⟨rf, b, hv, n + 1, hn, compiled_halt_trace he 99 98⟩

abbrev programAt {r s : ℕ} (regs : Fin 8 ↪ Fin r) (ports : Fin 110 ↪ Fin s) :
    Program r s (size command + 1) :=
  ProgramLinking.liftProgram program regs ports

abbrev callAt {r s : ℕ} (regs : Fin 8 ↪ Fin r) (ports : Fin 110 ↪ Fin s) : Cmd r s :=
  .call (programAt regs ports)

theorem final_store_updates {C : Type*} (encode : C → List Bool)
    (frame : Fin 110 → List Bool) (base : Words) (cs : List C) (b : C) :
    store frame (SubexpCRTCofactorLoop.readyWords encode base [] b) =
      Function.update (Function.update
        (store frame (SubexpCRTCofactorLoop.initialWords encode base cs)) 99 []) 98 (encode b) := by
  rw [update_store_stream, update_store_accumulator]
  rfl

private theorem extend_agree {α β γ : Type*} (f : α ↪ β) (values : α → γ)
    (frame : β → γ) (h : ∀ i, frame (f i) = values i) :
    Function.extend f values frame = frame := by
  classical
  funext j
  by_cases hj : ∃ i, f i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [f.injective.extend_apply, h]
  · exact Function.extend_apply' _ _ _ hj

/-- Generic physical relocation into the 16-register outer CRT controller.
The source stream is consumed and the cofactor output is written; all other
caller stacks, including the polynomial producer's persistent data, survive. -/
theorem callAt_eval {r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 110 ↪ Fin s)
    (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (c : Fin 4 → ZMod (p^μ)) (t unit : Quad (Word (baseWidth p μ)))
    (minusOne : Word (baseWidth p μ))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : decode p μ c unit = 1) (hminus : wordValue p μ minusOne = -1)
    (base : Words) (frame : Fin 110 → List Bool)
    (hm : base.modulus = M.bits) (hr : base.reduction = flat t)
    (hunit : base.unit = flat unit) (hminusWord : base.minusOne = minusOne.val)
    (hw : base.width.length = baseWidth p μ)
    (hblock : base.blockWidth.length = 4 * baseWidth p μ)
    (hB : 0 < baseWidth p μ) (cs : List (Quad (Word (baseWidth p μ))))
    (d : State r s)
    (hstore : ∀ i, d.stacks (ports i) =
      store frame (SubexpCRTCofactorLoop.initialWords flat base cs) i) :
    ∃ n rf b, n ≤ runtimeBound (baseWidth p μ) base.exponent cs.length ∧
      Eval (callAt registers ports) n d
        ⟨Function.extend registers rf d.regs,
          Function.update (Function.update d.stacks (ports 99) []) (ports 98) (flat b)⟩ ∧
      decode p μ c b =
        (cs.map (fun node => (-decode p μ c node) ^ BinaryArithmetic.toNat base.exponent)).prod := by
  obtain ⟨rf, b, hv, n, hn, he⟩ := program_run p μ M c t unit minusOne ht hu hminus
    base frame hm hr hunit hminusWord hw hblock hB cs (fun i => d.regs (registers i))
  have hl := ProgramLinking.liftProgram_trace program registers ports
    (⟨none, d.regs, d.stacks⟩ : Cfg r s (size command + 1))
    registers.injective ports.injective he
  have hregs := extend_agree registers (fun i => d.regs (registers i)) d.regs (fun _ => rfl)
  have hi := extend_agree ports
    (store frame (SubexpCRTCofactorLoop.initialWords flat base cs)) d.stacks hstore
  have ho : Function.extend ports
      (store frame (SubexpCRTCofactorLoop.readyWords flat base [] b)) d.stacks =
      Function.update (Function.update d.stacks (ports 99) []) (ports 98) (flat b) := by
    rw [final_store_updates flat frame base cs b,
      ProgramLinking.extend_update ports.injective,
      ProgramLinking.extend_update ports.injective, hi]
  refine ⟨n, rf, b, hn, Eval.call _ ?_, hv⟩
  simpa only [callAt, programAt, ProgramLinking.embedCfg, ProgramLinking.relocatePc,
    id_eq, hregs, hi, ho, state, StructuredProgram.State.withPC] using hl

end SubexponentialSAT.SubexpCRTCofactorMachine

end OAI.Algorithms
