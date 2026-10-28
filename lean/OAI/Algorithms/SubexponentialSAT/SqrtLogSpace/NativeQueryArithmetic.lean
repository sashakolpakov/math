import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryArithmetic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryWidthArithmetic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryDegreeRing
import OAI.Algorithms.SubexponentialSAT.BitProgramSelectedSpace

/-! Actual query arithmetic with fixed ordinary polynomial time and space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query CostAssembly.Polynomial

/-- The arithmetic suffix is the original ring, interpolation and denominator
program, with no residual evaluator or node-loop argument. -/
def arithmeticCommand : Cmd 40 768 := arithmetic

/-- Exact degree bytes follow from the actual searched producer and survive
the interpolation and denominator stages. This is the source proof from
LeafProgramQueryDegree.arithmetic_degree without its unrelated query constructor. -/
theorem arithmetic_degree (base out : Data) (n : ℕ)
    (he : Eval arithmeticCommand n base out)
    (m : Circuit.Model) (w : Bank.Words) (r : Bank.Regs) (hs : Circuit.Shape m w)
    (ha : projectState (LeafRingSetupProgram.registers 8 (by decide)) LeafRingSetupProgram.parameters
      (projectState LeafRingSetupProgram.wideRegisters LeafRingSetupProgram.wideStacks base) = Bank.state r w)
    (S : ℕ) (hinit : ∀ i, (base.stacks i).length ≤ S)
    (hv : ∀ i, (Circuit.result Serialization.code m).val i ≤ S)
    (hw : ∀ i, (Circuit.result Serialization.code m).len i ≤ S)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (hexp : (Circuit.result Serialization.code m).val 44 = 3 ^ (m.val 34) - 2)
    (h728 : base.stacks 728 = []) : out.stacks 204 = List.replicate (m.val 34) true := by
  obtain ⟨nr, hnr, e, M, cache, u, b, hr, hp, hlow, h713, h714, h715, h716,
    h717, hprivate, hhigh, hcollector, hregs, hlowBlank, hdegree⟩ :=
    LeafProgram.Query.Ring.command_eval_degree base m w r hs ha S S S hinit hv hw ht hd hexp
  have hf728 : b.stacks 728 = base.stacks 728 :=
    hhigh _ (by decide) (by decide) (by decide)
  have hbwidth : ∀ i, (b.stacks i).length ≤ S + LeafProgram.Query.Ring.budget m S S S + 1 := by
    intro i
    have hi := LeafRingSetupProgram.Interpolation.eval_width hr hinit i
    omega
  obtain ⟨nd, hnd, last, he', hout, hinv, hdregs⟩ :=
    LayoutDenominatorProgramQuery.produced_command_eval b m ht hd M cache u e hp hlow
      (fun i hi hj => hprivate i hi (by omega)) (hf728.trans h728) _ hbwidth
  have heq := SubexpPrimeProgram.eval_result_unique he (hr.seq he') 0 0
  rw [heq, hout, Function.update_of_ne (by decide : (204 : Fin 768) ≠ 728)]
  exact hdegree

/-- Every parked layout master survives actual arithmetic preparation. -/
theorem arithmetic_parked {base out : Data} {m : Circuit.Model} {hd : 0 < m.val 34}
    {M : SubexpPreparedQuartic.Modulus 3 (m.val 33)}
    {cache : RingProgram.ScalarCache 3 (m.val 33)} {u : RingProgram.ScalarCode 3 (m.val 33)}
    {e : LeafRingSetupProgram.Data} (h : ArithmeticOutput base out m hd M cache u e)
    (i : Fin 768) (hlo : 730 ≤ i.val) (_hhi : i.val < 744) :
    out.stacks i = base.stacks i := by
  apply h.highFrame i (by omega)
  · intro hi
    have hv := congrArg Fin.val hi
    change i.val = 699 at hv
    omega
  · intro hi
    have hv : i.val ≤ 728 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    omega

/-- Exact retained interpolation-cache lengths read from the actual arithmetic
output. These are independent of the preceding search runtime and caller frame. -/
theorem arithmetic_cache_lengths {base out : Data} {m : Circuit.Model} {hd : 0 < m.val 34}
    {M : SubexpPreparedQuartic.Modulus 3 (m.val 33)}
    {cache : RingProgram.ScalarCache 3 (m.val 33)} {u : RingProgram.ScalarCode 3 (m.val 33)}
    {e : LeafRingSetupProgram.Data} (h : ArithmeticOutput base out m hd M cache u e) :
    (out.stacks 713).length = m.val 21 * (m.val 34 * SubexpLiftRing.baseWidth 3 (m.val 33)) ∧
    (out.stacks 714).length = m.val 21 * (m.val 34 * SubexpLiftRing.baseWidth 3 (m.val 33)) ∧
    (out.stacks 715).length = m.val 21 * (m.val 21 * (m.val 34 * SubexpLiftRing.baseWidth 3 (m.val 33))) ∧
    (out.stacks 716).length = m.val 21 * (m.val 34 * SubexpLiftRing.baseWidth 3 (m.val 33)) ∧
    (out.stacks 717).length = m.val 34 * SubexpLiftRing.baseWidth 3 (m.val 33) := by
  rw [h.inverse, h.negative, h.difference, h.nodesLength, h.width]
  simp [LeafRingSetupProgram.nodeWords]

/-- The inverse denominator occupies exactly one actual ring coefficient. -/
theorem arithmetic_denominator_length {base out : Data} {m : Circuit.Model} {hd : 0 < m.val 34}
    {M : SubexpPreparedQuartic.Modulus 3 (m.val 33)}
    {cache : RingProgram.ScalarCache 3 (m.val 33)} {u : RingProgram.ScalarCode 3 (m.val 33)}
    {e : LeafRingSetupProgram.Data} (h : ArithmeticOutput base out m hd M cache u e) :
    (out.stacks 728).length = m.val 34 * SubexpLiftRing.baseWidth 3 (m.val 33) := by
  rw [h.denominator, RingProgram.flat_length]

private theorem halt_trace_of_eval {r s n : ℕ} {c : Cmd r s} {a b : State r s}
    (h : Eval c n a b) (input output : Fin s) :
    Trace (compiled c input output) (n + 1)
      (a.withPC (some (compiled c input output).entry)) (b.withPC none) :=
  compiled_halt_trace h input output

/-- One pair of polynomial coefficients is fixed before the physical input
and numeric model. The returned ring, cache and denominator proofs are all
produced by this same concrete arithmetic execution. -/
theorem arithmetic_resources : ∃ C d : ℕ,
    ∀ (base : Data) (m : Circuit.Model) (w : Bank.Words) (r : Bank.Regs),
      Circuit.Shape m w →
      projectState (LeafRingSetupProgram.registers 8 (by decide)) LeafRingSetupProgram.parameters
        (projectState LeafRingSetupProgram.wideRegisters LeafRingSetupProgram.wideStacks base) =
          Bank.state r w →
      ∀ S : ℕ, (∀ i, (base.stacks i).length ≤ S) →
        (∀ i, (Circuit.result Serialization.code m).val i ≤ S) →
        (∀ i, (Circuit.result Serialization.code m).len i ≤ S) →
        (∀ i, m.val i ≤ S) → (∀ i, m.len i ≤ S) →
        ∀ (ht : 0 < m.val 33) (hd : 0 < m.val 34),
          (Circuit.result Serialization.code m).val 44 = 3 ^ (m.val 34) - 2 →
          3 ^ (m.val 34) ≤ 16 * (m.val 21 + 1) ^ 2 → base.stacks 728 = [] →
          ∃ steps, ∃ (e : LeafRingSetupProgram.Data)
            (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
            (cache : RingProgram.ScalarCache 3 (m.val 33))
            (half : RingProgram.ScalarCode 3 (m.val 33)) (out : Data),
            steps ≤ C * (S + 1) ^ d ∧ Eval arithmeticCommand steps base out ∧
            ArithmeticOutput base out m hd M cache half e ∧
            out.stacks 204 = List.replicate (m.val 34) true ∧
            (RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache).decode
              (LayoutDenominatorProgramQuery.value (m.val 33) (IrreducibleSearch.data hd)
                M cache half (base.stacks 740).length) *
              (2 : (IrreducibleSearch.data hd).O (m.val 33)) ^ ((base.stacks 740).length - 1) = 1 ∧
            (∀ i, (out.stacks i).length ≤ S + C * (S + 1) ^ d) ∧
            Trace (compiled arithmeticCommand 700 728) (steps + 1)
              (base.withPC (some (compiled arithmeticCommand 700 728).entry)) (out.withPC none) ∧
            ∀ k c, k ≤ steps + 1 → Trace (compiled arithmeticCommand 700 728) k
              (base.withPC (some (compiled arithmeticCommand 700 728).entry)) c →
              ∀ i, (c.stacks i).length ≤ S + C * (S + 1) ^ d + 1 := by
  obtain ⟨C, d, hpoly⟩ := LeafProgram.Query.Width.arithmetic_budget_polynomial
  refine ⟨C, d, ?_⟩
  intro base m w r hs ha S hinit hv hw hmv hml ht hd hexp hfield h728
  obtain ⟨steps, hsteps, e, M, cache, half, out, he, ho, hinv⟩ :=
    arithmetic_eval base m w r hs ha S S S hinit hv hw ht hd hexp h728
  change Eval arithmeticCommand steps base out at he
  have htbound := hsteps.trans (hpoly m S S S (base.stacks 740).length S
    le_rfl le_rfl le_rfl (hinit 740) hml hmv hfield)
  have hdegree := arithmetic_degree base out steps he m w r hs ha S hinit hv hw ht hd hexp h728
  have hhalt : Trace (compiled arithmeticCommand 700 728) (steps + 1)
      (base.withPC (some (compiled arithmeticCommand 700 728).entry)) (out.withPC none) :=
    halt_trace_of_eval he 700 728
  refine ⟨steps, e, M, cache, half, out, htbound, he, ho, hdegree, hinv, ?_,
    hhalt, ?_⟩
  · intro i
    have hg : (out.stacks i).length ≤ (base.stacks i).length + steps := by
      simpa [selectedStackBits] using
        trace_selectedStackBits (compiled arithmeticCommand 700 728) {i} (compiled_trace he 700 728)
    have hi := hinit i
    omega
  · intro k c hk hc i
    have hg : (c.stacks i).length ≤ (base.stacks i).length + k := by
      simpa [selectedStackBits] using trace_selectedStackBits _ {i} hc
    have hi := hinit i
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
