import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFieldCacheLoop
import OAI.Algorithms.SubexponentialSAT.SubexpCRTCofactorMachine
import OAI.Algorithms.SubexponentialSAT.SubexpFlatAddCall

namespace OAI.Algorithms

/-! Concrete arithmetic callbacks for the physical source-field cache loops. -/

namespace SubexponentialSAT.SubexpFieldCacheMachine

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SubexpCRTCofactorControl SubexpFieldCacheControl SubexpFieldCacheLoop
open SubexpQuarticFlatMul (flat)

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev negate : Cmd 8 110 := SubexpCRTCofactorMachine.negate
abbrev power : Cmd 8 110 := SubexpCRTCofactorMachine.power

def addPort (i : Fin 20) : Fin 110 :=
  if i = 5 then 66 else if i = 8 then 70 else if i = 9 then 95 else
    if i = 10 then 74 else ⟨i.val, by omega⟩

def addPorts : Fin 20 ↪ Fin 110 := ⟨addPort, by decide⟩

abbrev add : Cmd 8 110 := SubexpFlatAddCall.callAt registers addPorts

abbrev command : Cmd 8 110 := SubexpFieldCacheControl.command negate add power
def program := compiled command 97 103

theorem add_encode_eq_flat {B : ℕ} (a : Quad (Word B)) :
    SubexpFlatAdd.encode a = flat a := by
  simp [SubexpFlatAdd.encode, SubexpFlatAdd.flatten, SubexpFlatAdd.quadWords,
    SubexpQuarticFlatMul.flat, SubexpQuarticFlatMul.wordLists,
    FourWordPrograms.flatWords, Quad.toFn]

theorem add_eval (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (a b : Quad (Word (baseWidth p μ))) (regs : Fin 8 → Bool)
    (frame : Fin 110 → List Bool) (w : Words)
    (hm : w.modulus = M.bits) (ha : w.left = flat a) (hb : w.negative = flat b)
    (hw : w.width.length = baseWidth p μ) :
    ∃ n rf, n ≤ 25000 * (baseWidth p μ + 1)^2 ∧
      Eval add n (state regs frame w)
        (state rf frame {w with
          left := flat (SubexpPreparedQuartic.binaryAdd p μ M a b).1
          negative := []}) := by
  have hlocal : ∀ i, (state regs frame w).stacks (addPorts i) =
      (SubexpFlatAdd.ready regs M.bits (SubexpFlatAdd.encode a) (SubexpFlatAdd.encode b)
        w.width [] (fun _ => [])).stacks i := by
    intro i
    fin_cases i <;> simp [state, addPorts, addPort, store, nativeStore,
      SubexpQuarticFlatMul.bankStore, SubexpFlatAdd.ready, SubexpFlatAdd.state,
      SubexpFlatAdd.stacks, Fin.addCases, hm, ha, hb, add_encode_eq_flat]
  obtain ⟨n, rf, hn, he⟩ := SubexpFlatAddCall.callAt_eval registers addPorts
    p μ M a b w.width hw (state regs frame w) (fun _ => []) hlocal
  refine ⟨n, rf, hn, ?_⟩
  simpa only [add, registers, Function.Embedding.coeFn_mk,
    ProgramLinking.extend_id, SubexpFlatAddCall.resultStacks,
    show addPorts 8 = (70 : Fin 110) from rfl,
    show addPorts 9 = (95 : Fin 110) from rfl,
    update_store_left, update_store_negative, state, add_encode_eq_flat] using he

def nodeIterationBudget (B : ℕ) (exponent : List Bool) : ℕ :=
  SubexpQuarticPowerProgram.runtimeBound B exponent + 25000 * (B + 1)^2 + 124 * B + 28

/-- A full node iteration runs the actual bounded-width power and negation
programs, and emits their actual four-word outputs into the two packed arrays. -/
theorem nodeIteration_value (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (c : Fin 4 → ZMod (p^μ))
    (t unit node : Quad (Word (baseWidth p μ))) (minusOne : Word (baseWidth p μ))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (unit.map (wordValue p μ)) = 1)
    (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool) (w : Words) (rest : List Bool)
    (hm : w.modulus = M.bits) (hr : w.reduction = flat t) (hone : w.unit = flat unit)
    (hmone : w.minusOne = minusOne.val) (hs : w.stream = flat node ++ rest)
    (hw : w.width.length = baseWidth p μ) (hblock : w.blockWidth.length = 4 * baseWidth p μ)
    (hnode : w.node = []) (hneg : w.negative = []) (hpow : w.power = [])
    (hleft : w.left = []) (hright : w.right = []) (hresult : w.result = []) :
    ∃ n rf inverse,
      n ≤ nodeIterationBudget (baseWidth p μ) w.exponent ∧
      Eval (nodeIteration negate power) n (state regs frame w)
        (state rf
          (Function.update frame 100
            ((flat (SubexpQuarticNegMachine.negateWords p μ M minusOne node)).reverse ++ frame 100))
          (nodeOutput w rest (flat inverse))) ∧
      quotientDenote c (inverse.map (wordValue p μ)) =
        quotientDenote c (node.map (wordValue p μ)) ^ BinaryArithmetic.toNat w.exponent := by
  let w2 := nodePowerInput w (flat node) rest
  obtain ⟨np, rp, inverse, hp, hv, hnp⟩ := SubexpCRTCofactorMachine.power_eval
    p μ M c t node unit ht hu (readRegs regs 0 1 none) frame w2
    hm hr rfl hone hleft hright hresult hpow hw
  let w3 := nodeNegationInput w (flat node) rest (flat inverse)
  obtain ⟨nn, rn, hnn, hn⟩ := SubexpCRTCofactorMachine.negate_eval
    p μ M node minusOne (readRegs rp 0 1 none) frame w3 hm rfl hmone rfl hw
  have he := nodeIteration_eval negate power regs rp rn frame w
    (flat node) rest (flat inverse) (flat (SubexpQuarticNegMachine.negateWords p μ M minusOne node))
    np nn hs (by simpa only [SubexpQuarticFlatMul.flat_length] using hblock)
    hnode hneg hp hn
  refine ⟨_, readRegs rn 0 1 none, inverse, ?_, he, hv⟩
  simp only [SubexpQuarticFlatMul.flat_length]
  unfold nodeIterationBudget
  change np ≤ SubexpQuarticPowerProgram.runtimeBound (baseWidth p μ) w.exponent at hnp
  omega

def pairIterationBudget (B : ℕ) (exponent : List Bool) : ℕ :=
  SubexpQuarticPowerProgram.runtimeBound B exponent + 25000 * (B + 1)^2 + 128 * B + 28

/-- A genuine sum-and-power call for one ordered pair, with all temporary
operands restored empty and the current row node preserved. -/
theorem pairIteration_value (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (c : Fin 4 → ZMod (p^μ))
    (t unit node negative : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (unit.map (wordValue p μ)) = 1)
    (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool) (w : Words) (rest : List Bool)
    (hm : w.modulus = M.bits) (hr : w.reduction = flat t) (hone : w.unit = flat unit)
    (hn : w.node = flat node) (hs : w.stream = flat negative ++ rest)
    (hw : w.width.length = baseWidth p μ) (hblock : w.blockWidth.length = 4 * baseWidth p μ)
    (hneg : w.negative = []) (hpow : w.power = [])
    (hleft : w.left = []) (hright : w.right = []) (hresult : w.result = []) :
    ∃ n rf inverse,
      n ≤ pairIterationBudget (baseWidth p μ) w.exponent ∧
      Eval (pairIteration add power) n (state regs frame w)
        (state rf (Function.update frame 103 ((flat inverse).reverse ++ frame 103))
          (pairOutput w rest)) ∧
      quotientDenote c (inverse.map (wordValue p μ)) =
        (quotientDenote c (node.map (wordValue p μ)) +
          quotientDenote c (negative.map (wordValue p μ))) ^ BinaryArithmetic.toNat w.exponent := by
  let wa := pairAddInput w (flat negative) rest
  let sum := (SubexpPreparedQuartic.binaryAdd p μ M node negative).1
  obtain ⟨na, ra, hna, ha⟩ := add_eval p μ M node negative
    (readRegs regs 0 1 none) frame wa hm hn rfl hw
  let wp := pairPowerInput w rest (flat sum)
  obtain ⟨np, rp, inverse, hp, hv, hnp⟩ := SubexpCRTCofactorMachine.power_eval
    p μ M c t sum unit ht hu (readRegs ra 0 1 none) frame wp
    hm hr rfl hone rfl hright hresult hpow hw
  have he := pairIteration_eval add power regs ra rp frame w
    (flat negative) rest (flat sum) (flat inverse) na np hs
    (by simpa only [SubexpQuarticFlatMul.flat_length] using hblock) hneg hleft ha hp
  refine ⟨_, readRegs rp 0 1 none, inverse, ?_, he, ?_⟩
  · rw [hn]
    simp only [SubexpQuarticFlatMul.flat_length]
    unfold pairIterationBudget
    change np ≤ SubexpQuarticPowerProgram.runtimeBound (baseWidth p μ) w.exponent at hnp
    omega
  · rw [hv, SubexpPreparedQuartic.binaryAdd_quotient]
    rfl

end SubexponentialSAT.SubexpFieldCacheMachine

end OAI.Algorithms
