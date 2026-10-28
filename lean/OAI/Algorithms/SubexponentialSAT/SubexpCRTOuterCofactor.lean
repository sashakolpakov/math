import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterSetup
import OAI.Algorithms.SubexponentialSAT.SubexpCRTCofactorMachine

namespace OAI.Algorithms

/-! The concrete outer cofactor call, including construction of the omitted
node stream and all preparation, output transport, and cleanup costs. -/

namespace SubexponentialSAT.SubexpCRTOuterCofactor

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing
open SubexpQuarticFlatMul (flat)
open SubexpCRTOuterProgram (Code Data registers scalarPorts copy move clearMany moved)

def copies : List (Fin 320 × Fin 320) :=
  [(268,219),(211,220),(207,221),(104,232),(258,227),(257,227)]

def prepare : Code := SubexpSetupStorage.copyMany 318 copies
def prepared (d : Data) : Data := SubexpSetupStorage.copyManyState copies d

def command : Code := .seq prepare
  (.seq (SubexpCRTCofactorMachine.callAt registers scalarPorts)
    (.seq (move 226 262) (clearMany [219,220,221,232])))

def prepareBudget (d : Data) : ℕ :=
  7 * ((d.stacks 268).length + (d.stacks 211).length + (d.stacks 207).length +
    (d.stacks 104).length + (d.stacks 258).length + (d.stacks 257).length) + 30

theorem prepare_run (d : Data) (ht : d.stacks 318 = []) :
    Eval prepare (prepareBudget d) d (prepared d) := by
  have hp : ∀ q ∈ copies, q.1 ≠ q.2 ∧ q.1 ≠ (318 : Fin 320) ∧ (318 : Fin 320) ≠ q.2 := by
    intro q hq
    simp only [copies, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h := SubexpSetupStorage.copyMany_eval 318 copies d hp ht
  have hcost : SubexpSetupStorage.copyManyCost copies d = prepareBudget d := by
    simp [copies, SubexpSetupStorage.copyManyCost, SubexpSetupStorage.copyState,
      StackRoutines.copyStacks, prepareBudget]
    ring
  simpa only [prepare, prepared, hcost] using h

theorem prepared_stacks (d : Data) : (prepared d).stacks =
    Function.update (Function.update (Function.update (Function.update
      (Function.update d.stacks 219 (d.stacks 268 ++ d.stacks 219))
        220 (d.stacks 211 ++ d.stacks 220))
        221 (d.stacks 207 ++ d.stacks 221))
        232 (d.stacks 104 ++ d.stacks 232))
        227 (d.stacks 257 ++ d.stacks 258 ++ d.stacks 227) := by
  simp [prepared, copies, SubexpSetupStorage.copyManyState, SubexpSetupStorage.copyState,
    StackRoutines.copyStacks, List.append_assoc]

def cleanPorts : List (Fin 320) := [219,220,221,232,227,226,262,318,319]

noncomputable def called (d : Data) (rf : Fin 8 → Bool) (bits : List Bool) : Data :=
  ⟨Function.extend registers rf (prepared d).regs,
    Function.update (Function.update (prepared d).stacks 227 []) 226 bits⟩

noncomputable def result (d : Data) (rf : Fin 8 → Bool) (bits : List Bool) : Data :=
  SubexpSetupStorage.clearManyState [219,220,221,232] (moved (called d rf bits) 226 262)

theorem result_stacks (d : Data) (rf : Fin 8 → Bool) (bits : List Bool)
    (hc : ∀ j ∈ cleanPorts, d.stacks j = []) :
    (result d rf bits).stacks = Function.update d.stacks 262 bits := by
  have h219 := hc 219 (by decide)
  have h220 := hc 220 (by decide)
  have h221 := hc 221 (by decide)
  have h232 := hc 232 (by decide)
  have h227 := hc 227 (by decide)
  have h226 := hc 226 (by decide)
  funext j
  by_cases hj : j ∈ ([219,220,221,232,227,226,262] : List (Fin 320))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [result, SubexpSetupStorage.clearManyState, SubexpSetupStorage.clearState,
        called, prepared_stacks, h219, h220, h221, h232, h227, h226]
  · have hne : j ≠ 219 ∧ j ≠ 220 ∧ j ≠ 221 ∧ j ≠ 232 ∧ j ≠ 227 ∧ j ≠ 226 ∧ j ≠ 262 := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using hj
    rcases hne with ⟨h1,h2,h3,h4,h5,h6,h7⟩
    simp [result, SubexpSetupStorage.clearManyState, SubexpSetupStorage.clearState,
      called, prepared_stacks, h1,h2,h3,h4,h5,h6,h7]

def budget (B : ℕ) (exponent : List Bool) (nodes : ℕ) (d : Data) : ℕ :=
  prepareBudget d + SubexpCRTCofactorMachine.runtimeBound B exponent nodes + 24 * B + 18 +
    2 * ((d.stacks 268).length + (d.stacks 211).length +
      (d.stacks 207).length + (d.stacks 104).length)

/-- Every arithmetic step is the already checked finite cofactor machine.
The state premise describes its prepared physical input, including the
remaining ++ processed stream; it contains no asserted arithmetic answer. -/
theorem command_eval (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (c : Fin 4 → ZMod (p^μ)) (t unit : Quad (Word (baseWidth p μ)))
    (minusOne : Word (baseWidth p μ))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : SubexpCRTCofactorMachine.decode p μ c unit = 1)
    (hminus : wordValue p μ minusOne = -1)
    (base : SubexpCRTCofactorControl.Words) (frame : Fin 110 → List Bool)
    (hm : base.modulus = M.bits) (hr : base.reduction = flat t)
    (hunit : base.unit = flat unit) (hminusWord : base.minusOne = minusOne.val)
    (hw : base.width.length = baseWidth p μ)
    (hblock : base.blockWidth.length = 4 * baseWidth p μ)
    (hB : 0 < baseWidth p μ) (cs : List (Quad (Word (baseWidth p μ))))
    (d : Data) (hc : ∀ j ∈ cleanPorts, d.stacks j = [])
    (hstore : ∀ i, (prepared d).stacks (scalarPorts i) =
      SubexpCRTCofactorControl.store frame (SubexpCRTCofactorLoop.initialWords flat base cs) i) :
    ∃ n rf b, n ≤ budget (baseWidth p μ) base.exponent cs.length d ∧
      Eval command n d ⟨rf, Function.update d.stacks 262 (flat b)⟩ ∧
      SubexpCRTCofactorMachine.decode p μ c b =
        (cs.map (fun node => (-SubexpCRTCofactorMachine.decode p μ c node) ^
          BinaryArithmetic.toNat base.exponent)).prod := by
  have hp := prepare_run d (hc 318 (by decide))
  obtain ⟨n, rf, b, hn, hcall, hvalue⟩ := SubexpCRTCofactorMachine.callAt_eval registers scalarPorts
    p μ M c t unit minusOne ht hu hminus base frame hm hr hunit hminusWord hw hblock hB
    cs (prepared d) hstore
  change Eval _ n (prepared d) (called d rf (flat b)) at hcall
  have ht' : (called d rf (flat b)).stacks 319 = [] := by
    simpa [called, prepared_stacks] using hc 319 (by decide)
  have ho : (called d rf (flat b)).stacks 262 = [] := by
    simpa [called, prepared_stacks] using hc 262 (by decide)
  have hmove := SubexpCRTOuterProgram.move_run (called d rf (flat b)) 226 262
    (by decide) (by decide) (by decide) ht' ho
  have hclear := SubexpCRTOuterProgram.clearMany_run (moved (called d rf (flat b)) 226 262)
    [219,220,221,232]
  have hrun := hp.seq (hcall.seq (hmove.seq hclear))
  change Eval command _ d (result d rf (flat b)) at hrun
  have hresult : result d rf (flat b) =
      (⟨(result d rf (flat b)).regs, Function.update d.stacks 262 (flat b)⟩ : Data) :=
    state_ext rfl (result_stacks d rf (flat b) hc)
  rw [hresult] at hrun
  refine ⟨_, _, b, ?_, hrun, hvalue⟩
  have h219 := hc 219 (by decide)
  have h220 := hc 220 (by decide)
  have h221 := hc 221 (by decide)
  have h232 := hc 232 (by decide)
  simp [budget, called, prepared_stacks, SubexpSetupStorage.clearManyCost,
    SubexpSetupStorage.clearState, h219, h220, h221, h232,
    SubexpQuarticFlatMul.flat_length]
  omega

end SubexponentialSAT.SubexpCRTOuterCofactor

end OAI.Algorithms
