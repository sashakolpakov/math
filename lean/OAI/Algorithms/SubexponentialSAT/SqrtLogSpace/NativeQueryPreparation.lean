import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryArithmetic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramQuantitative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryBank
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryFrontState
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryRingModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryModelBudgets
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramSerializationBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendPolynomial
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramReplay
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgramReplay
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgramInterpolationReplay
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQueryReplay
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandStackTransport
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedCleanup

/-! Concrete query packing and arithmetic preparation. Numeric and physical
input caps are kept separate from the subsequent exponential node traversal.
Every arithmetic object is returned by its actual native producer. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query CostAssembly.Polynomial

/-- Actual packing followed by actual ring/interpolation/denominator setup. -/
def command : Cmd 40 768 := .seq PackingCallerProgram.command arithmeticCommand

/-- This certificate checks the actual producer, interpolation, denominator
and packing instruction tables, including every peek. -/
theorem command_avoids : ProgramTapeReplay.AvoidsCmd LeafProgram.OuterCarried.hidden command :=
  ⟨PackingCallerProgram.Replay.command_avoids,
    ⟨⟨LeafRingSetupProgram.Replay.producerWideCall_avoids,
      LeafRingSetupProgram.Interpolation.Replay.command_avoids⟩,
      LayoutDenominatorProgramQuery.command_avoids⟩⟩

/-- The literal packing input includes every initial stack, physical padded
parameter word, and the numerically bounded complete type alphabet. -/
theorem packing_size_le (a : Data) (p : PackingCallerProgram.Problem) (S : ℕ)
    (hsources : PackingCallerProgram.Sources a p)
    (hwords : ∀ i, (a.stacks i).length ≤ S)
    (hn : p.n ≤ S) (hf : p.factors ≤ S) (hD : p.incidences ≤ S)
    (hr : p.r ≤ S) (hQ : p.Q ≤ S) (heps : p.s ≤ S)
    (htypes : p.r ^ (2 * p.Q) ≤ S) :
    PackingCallerProgram.globalSize a p ≤ 790 * (S + 1) := by
  have halphabet : p.r ^ p.Q ≤ S := by
    calc
      _ ≤ (p.r ^ p.Q) ^ 2 := Nat.le_self_pow (by decide) _
      _ = p.r ^ (2 * p.Q) := by rw [← pow_mul, Nat.mul_comm p.Q 2]
      _ ≤ S := htypes
  have hscopes := hwords 718
  rw [hsources.scopes] at hscopes
  have hmask := hwords 719
  rw [hsources.mask] at hmask
  have hmass : PackingCallerProgram.inputMass a ≤ 768 * S := by
    unfold PackingCallerProgram.inputMass
    calc
      _ ≤ ∑ _i : Fin 768, S := Finset.sum_le_sum (fun i _ => hwords i)
      _ = _ := by simp
  have h709 := hwords 709
  have h720 := hwords 720
  have h721 := hwords 721
  have h722 := hwords 722
  have h723 := hwords 723
  change PackingCallerProgram.inputMass a +
    (p.n + p.factors + p.incidences + p.r + p.Q + p.s + p.r ^ p.Q + p.r ^ (2 * p.Q) +
      (PackingIncidenceInput.Scan.scopeBits p.scopes).length + p.mask.length +
      (a.stacks 720).length + (a.stacks 709).length + (a.stacks 722).length +
      (a.stacks 723).length + (a.stacks 721).length + 1) + 1 ≤ _
  omega

/-- This fixed ordinary envelope pays for the complete packing and the
subsequent polynomial arithmetic phase. -/
def setupEnvelope (Cp dp Ca da S : ℕ) : ℕ :=
  let P := Cp * (790 * (S + 1)) ^ dp
  S + P + Ca * (S + P + 1) ^ da + 1

theorem setupEnvelope_polynomial (Cp dp Ca da : ℕ) :
    CostAssembly.Polynomial.Ordinary (setupEnvelope Cp dp Ca da) := by
  have hP : Ordinary (fun S => Cp * (790 * (S + 1)) ^ dp) :=
      ordinary_mul (ordinary_const Cp) (ordinary_pow
        (ordinary_mul (ordinary_const 790) (ordinary_add ordinary_id (ordinary_const 1))) dp)
  have hA := ordinary_add ordinary_id hP
  have hB := ordinary_mul (ordinary_const Ca)
      (ordinary_pow (ordinary_add hA (ordinary_const 1)) da)
  exact ordinary_add (ordinary_add hA hB) (ordinary_const 1)

/-- Complete preparation from the physical post-frontend sources. All
numeric premises are compact parameter caps; every requested algorithmic
stage is executed here and no evaluator service is supplied. -/
theorem command_resources : ∃ C d : ℕ,
    ∀ (base : Data) (p : PackingCallerProgram.Problem) (m : Circuit.Model)
      (w : Bank.Words) (r : Bank.Regs),
      PackingCallerProgram.Sources base p → PackingCallerProgram.Empty base →
      Circuit.Shape m w → projectState Exports.bankRegs Exports.bank base = Bank.state r w →
      ∀ S : ℕ, (∀ i, (base.stacks i).length ≤ S) →
        p.n ≤ S → p.factors ≤ S → p.incidences ≤ S → p.r ≤ S → p.Q ≤ S → p.s ≤ S →
        p.r ^ (2 * p.Q) ≤ S →
        (∀ i, (Circuit.result Serialization.code m).val i ≤ S) →
        (∀ i, (Circuit.result Serialization.code m).len i ≤ S) →
        (∀ i, m.val i ≤ S) → (∀ i, m.len i ≤ S) →
        ∀ (ht : 0 < m.val 33) (hd : 0 < m.val 34),
          (Circuit.result Serialization.code m).val 44 = 3 ^ (m.val 34) - 2 →
          3 ^ (m.val 34) ≤ 16 * (m.val 21 + 1) ^ 2 → base.stacks 728 = [] →
          ∃ first : MulticolorTypes.Word p.r p.Q,
            ∃ rest : List (MulticolorTypes.Word p.r p.Q), ∃ packed : Data, ∃ np na,
            ∃ (e : LeafRingSetupProgram.Data)
              (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
              (cache : RingProgram.ScalarCache 3 (m.val 33))
              (half : RingProgram.ScalarCode 3 (m.val 33)) (out : Data),
              (first :: rest).map Subexp.ReadPlan.encodeWord =
                Subexp.AssignmentAlphabetSemantics.wordBytes p.r p.Q ∧
              (first :: rest).Nodup ∧ (∀ z, z ∈ first :: rest) ∧
              Eval PackingCallerProgram.command np base packed ∧
              packed.stacks = (PackingCallerProgram.result base p first rest).stacks ∧
              Eval arithmeticCommand na packed out ∧
              ArithmeticOutput packed out m hd M cache half e ∧
              out.stacks 204 = List.replicate (m.val 34) true ∧
              (RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache).decode
                (LayoutDenominatorProgramQuery.value (m.val 33) (IrreducibleSearch.data hd)
                  M cache half (packed.stacks 740).length) *
                (2 : (IrreducibleSearch.data hd).O (m.val 33)) ^ ((packed.stacks 740).length - 1) = 1 ∧
              Eval command (np + na) base out ∧ np + na ≤ C * (S + 1) ^ d ∧
              (∀ i, (out.stacks i).length ≤ C * (S + 1) ^ d) ∧
              Trace (compiled command 700 728) (np + na + 1)
                (base.withPC (some (compiled command 700 728).entry)) (out.withPC none) ∧
              ∀ k c, k ≤ np + na + 1 → Trace (compiled command 700 728) k
                (base.withPC (some (compiled command 700 728).entry)) c →
                ∀ i, (c.stacks i).length ≤ C * (S + 1) ^ d := by
  obtain ⟨Cp, dp, hdp, hpackpoly⟩ := PackingCallerProgram.budget_polynomial
  obtain ⟨Ca, da, harith⟩ := arithmetic_resources
  obtain ⟨C, d, hpoly⟩ := setupEnvelope_polynomial Cp dp Ca da
  refine ⟨C, d, ?_⟩
  intro base p m w r hsources hempty hshape hbank S hinit hn hf hD hr hQ heps htypes
    hv hw hmv hml ht hd hexp hfield h728
  obtain ⟨first, rest, hrows, hnodup, hall⟩ := Subexp.AssignmentAlphabetSemantics.wordBytes_order p.hr p.Q
  obtain ⟨np, packed, hnp, hep, hbytes, hregs⟩ :=
    PackingCallerProgram.command_eval base p hsources hempty first rest hrows hnodup hall
  have hG := packing_size_le base p S hsources hinit hn hf hD hr hQ heps htypes
  obtain ⟨hbudget, hpacked⟩ := hpackpoly base p first rest hsources hempty hrows
  let P := Cp * (790 * (S + 1)) ^ dp
  let A := S + P
  have hP : PackingCallerProgram.budget base p first rest ≤ P :=
    hbudget.trans (Nat.mul_le_mul_left Cp (Nat.pow_le_pow_left hG dp))
  have hPwords : ∀ i, (packed.stacks i).length ≤ P := by
    intro i
    rw [hbytes]
    exact (hpacked i).trans (Nat.mul_le_mul_left Cp (Nat.pow_le_pow_left hG dp))
  have hSA : S ≤ A := by dsimp [A]; omega
  have hPA : P ≤ A := by dsimp [A]; omega
  have hpackedFrame (i : Fin 768) (hb : i.val < 417 ∨ 481 ≤ i.val)
      (hl : i.val < 128 ∨ 142 ≤ i.val) (hh : i.val < 730 ∨ 744 ≤ i.val) :
      packed.stacks i = base.stacks i := by
    rw [hbytes]
    exact PackingCallerProgram.result_frame base p first rest i hb hl hh
  have hpackedBank := ring_bank_of_frame base packed w r hbank
    (fun i hi hj => hpackedFrame i (Or.inl hj) (Or.inr (by omega)) (Or.inl (by omega)))
  have hpacked728 : packed.stacks 728 = [] :=
    (hpackedFrame 728 (by decide) (by decide) (by decide)).trans h728
  obtain ⟨na, e, M, cache, half, out, hna, hea, hout, hdegree, hinverse, hfinal, _, _⟩ :=
    harith packed m w (packed.regs ∘ Exports.bankRegs) hshape hpackedBank A
      (fun i => (hPwords i).trans hPA)
      (fun i => (hv i).trans hSA) (fun i => (hw i).trans hSA)
      (fun i => (hmv i).trans hSA) (fun i => (hml i).trans hSA)
      ht hd hexp hfield hpacked728
  have heval : Eval command (np + na) base out := hep.seq hea
  have htotal : S + (np + na) + 1 ≤ setupEnvelope Cp dp Ca da S := by
    change S + (np + na) + 1 ≤ S + P + Ca * (A + 1) ^ da + 1
    omega
  have hcap := htotal.trans (hpoly S)
  refine ⟨first, rest, packed, np, na, e, M, cache, half, out, hrows, hnodup, hall,
    hep, hbytes, hea, hout, hdegree, hinverse, heval, by omega, ?_,
    compiled_halt_trace heval 700 728, ?_⟩
  · intro i
    have hi := hfinal i
    have hfull := hpoly S
    change A + Ca * (A + 1) ^ da + 1 ≤ C * (S + 1) ^ d at hfull
    omega
  · intro k c hk hc i
    have hg : (c.stacks i).length ≤ (base.stacks i).length + k := by
      simpa [selectedStackBits] using trace_selectedStackBits _ {i} hc
    have hi := hinit i
    omega

/-- The successful branch test is the actual register written by the frontend. -/
theorem front_guard_register (q : LeafQueryFrontend.Query) (k : ℕ)
    (base front : Data) (l : Fin 8 → ℕ) (w : Bank.Words)
    (hf : FrontState q k base front l w) (hg : Guard (q.input k)) :
    front.regs 8 = true := hf.guard.mpr hg

/-- Erasing only the three syntactically untouched carried words is a proof
construction; the actual preparation still runs with those words present. -/
def shadow (a : Data) : Data :=
  ProgramTapeReplay.rebaseState LeafProgram.OuterCarried.hidden (fun _ => []) a

theorem shadow_visible (a : Data) (i : Fin 768)
    (hi : i.val < 320 ∨ 332 < i.val) : (shadow a).stacks i = a.stacks i := by
  apply ProgramTapeReplay.rebaseStacks_of_not_mem
  intro h
  simp only [LeafProgram.OuterCarried.hidden, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> norm_num [Fin.coe_ofNat_eq_mod] at hi

theorem shadow_sources (a : Data) (p : PackingCallerProgram.Problem)
    (h : PackingCallerProgram.Sources a p) : PackingCallerProgram.Sources (shadow a) p := by
  constructor
  · exact (shadow_visible a 718 (by decide)).trans h.scopes
  · exact (shadow_visible a 128 (by decide)).trans h.ambientUnary
  · exact (shadow_visible a 719 (by decide)).trans h.mask
  · simpa only [shadow_visible a 709 (by decide)] using h.ambient
  · simpa only [shadow_visible a 720 (by decide)] using h.coordinate
  · simpa only [shadow_visible a 721 (by decide)] using h.radius
  · simpa only [shadow_visible a 722 (by decide)] using h.epsilon
  · simpa only [shadow_visible a 723 (by decide)] using h.incidence

theorem shadow_empty (a : Data) (h : PackingCallerProgram.Empty a) :
    PackingCallerProgram.Empty (shadow a) := by
  constructor
  · intro i
    change (shadow a).stacks (PackingCallerProgram.Wide.ports i) = []
    rw [shadow_visible a _ (Or.inr (by change 332 < 417+i.val; omega))]
    exact h.bank i
  · exact (shadow_visible a 684 (by decide)).trans h.temporary
  · exact (shadow_visible a 133 (by decide)).trans h.words
  · exact (shadow_visible a 135 (by decide)).trans h.metadata
  · exact (shadow_visible a 136 (by decide)).trans h.plans
  · intro i
    exact (shadow_visible a _ (Or.inr (by change 332 < 730+i.val; omega))).trans (h.parked i)

theorem shadow_bank (a : Data) :
    projectState Exports.bankRegs Exports.bank (shadow a) =
      projectState Exports.bankRegs Exports.bank a := by
  apply CommandStackTransport.projectState_rebase
  intro i h
  have hi : 340 ≤ (Exports.bank i).val := by simp [Exports.bank]
  simp only [LeafProgram.OuterCarried.hidden, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h <;> have hv := congrArg Fin.val h <;>
    norm_num [Fin.coe_ofNat_eq_mod] at hv <;> omega

/-- Retiming a concrete semantic execution uses a bounded visible shadow.
The resulting run is the same fixed command on the original physical input;
its time excludes arbitrary carried words and its prefixes include them. -/
theorem command_source_resources : ∃ C d : ℕ,
    ∀ (base out : Data) (oldSteps : ℕ), Eval command oldSteps base out →
    ∀ (p : PackingCallerProgram.Problem) (m : Circuit.Model) (w : Bank.Words) (r : Bank.Regs),
      PackingCallerProgram.Sources base p → PackingCallerProgram.Empty base →
      Circuit.Shape m w → projectState Exports.bankRegs Exports.bank base = Bank.state r w →
      ∀ S B : ℕ,
        (∀ i, ¬ LeafProgram.OuterCarried.hidden i → (base.stacks i).length ≤ S) →
        (∀ i, LeafProgram.OuterCarried.hidden i → (base.stacks i).length ≤ B) →
        p.n ≤ S → p.factors ≤ S → p.incidences ≤ S → p.r ≤ S → p.Q ≤ S → p.s ≤ S →
        p.r ^ (2 * p.Q) ≤ S →
        (∀ i, (Circuit.result Serialization.code m).val i ≤ S) →
        (∀ i, (Circuit.result Serialization.code m).len i ≤ S) →
        (∀ i, m.val i ≤ S) → (∀ i, m.len i ≤ S) →
        ∀ (_ht : 0 < m.val 33) (_hd : 0 < m.val 34),
          (Circuit.result Serialization.code m).val 44 = 3 ^ (m.val 34) - 2 →
          3 ^ (m.val 34) ≤ 16 * (m.val 21 + 1) ^ 2 → base.stacks 728 = [] →
          oldSteps ≤ C * (S + 1) ^ d ∧
            Trace (compiled command 700 728) (oldSteps + 1)
              (base.withPC (some (compiled command 700 728).entry)) (out.withPC none) ∧
            ∀ k c, k ≤ oldSteps + 1 → Trace (compiled command 700 728) k
              (base.withPC (some (compiled command 700 728).entry)) c →
              ∀ i, (c.stacks i).length ≤ max (C * (S + 1) ^ d) B := by
  obtain ⟨C,d,hresources⟩ := command_resources
  refine ⟨C,d,?_⟩
  intro base out oldSteps hsem p m w r hs he hshape hbank S B hvisible hhidden
    hn hf hD hr hQ heps htypes hv hw hmv hml ht hd hexp hfield h728
  have hshadow : ∀ i, ((shadow base).stacks i).length ≤ S :=
    CommandStackTransport.shadow_stack_bound LeafProgram.OuterCarried.hidden base S hvisible
  obtain ⟨first,rest,packed,np,na,e,M,cache,half,shadowOut,_,_,_,_,_,_,_,_,_,
      hrun,htime,_,_,hprefix⟩ :=
    hresources (shadow base) p m w r (shadow_sources base p hs) (shadow_empty base he)
      hshape ((shadow_bank base).trans hbank) S hshadow hn hf hD hr hQ heps htypes
      hv hw hmv hml ht hd hexp hfield ((shadow_visible base 728 (by decide)).trans h728)
  have hactual := CommandStackTransport.eval_shadow LeafProgram.OuterCarried.hidden command_avoids hrun
  have hsteps : oldSteps = np + na := StreamResources.eval_steps_eq 700 728 hsem hactual
  refine ⟨by simpa only [hsteps] using htime, compiled_halt_trace hsem 700 728, ?_⟩
  rw [hsteps]
  exact CommandStackTransport.eval_shadow_prefix_bound LeafProgram.OuterCarried.hidden command_avoids
    700 728 hrun (fun k c hk hc i _ => hprefix k c hk hc i) hhidden

/-- The serialized word-length cap comes from the actual canonical frontend
padding vector. One polynomial works before the query, mark and input words
are selected. -/
theorem front_serialized_lengths_polynomial : ∃ C d : ℕ,
    ∀ (q : LeafQueryFrontend.Query) (k : ℕ) (base front : Data)
      (l : Fin 8 → ℕ) (w : Bank.Words),
      q.Valid → FrontState q k base front l w →
      ∀ i, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) l)).len i ≤
        C * (LeafScopeInputBounds.capacity q k + 1) ^ d := by
  obtain ⟨C,d,h⟩ := Serialization.uniform_guarded_lengths_polynomial
  have hp : Ordinary (fun S => C * (LeafQueryFrontend.parameterSize S + 1) ^ d) :=
    ordinary_mul (ordinary_const C) (ordinary_pow
      (ordinary_add LeafQueryFrontend.parameterSize_poly (ordinary_const 1)) d)
  obtain ⟨A,e,hA⟩ := hp
  refine ⟨A,e,?_⟩
  intro q k base front l w hv hf i
  rw [hf.canonicalLengths]
  exact (h (q.input k) (q.inputLengths k) (LeafQueryFrontend.parameterSize
    (LeafScopeInputBounds.capacity q k))
    (LeafQueryFrontend.parameter_counts_bound q k hv)
    (LeafQueryFrontend.parameter_lengths_bound q k hv) i).trans (hA _)

/-- The actual incidence scan retains one neutral factor for each uncovered
low coordinate. This is the original native factor-count identity. -/
theorem packing_factors_eq (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k)) :
    (packingProblem q k hg).factors = (q.input k).factors := by
  unfold PackingCallerProgram.Problem.factors packingProblem
  rw [PackingIncidenceInput.Stats.native_factor_count]
  rfl

/-- The concrete guarded frontend fixes all packing scalars and ring-array
sizes. These facts use its actual serialized bank, not a supplied layout. -/
theorem front_numeric_inputs (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) (base front : Data) (l : Fin 8 → ℕ) (w : Bank.Words)
    (hfront : FrontState q k base front l w) (S : ℕ)
    (hv : ∀ i, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) l)).val i ≤ S)
    (hl : ∀ i, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) l)).len i ≤ S) :
    let p := packingProblem q k hg
    let m := Execute.guardedModel (q.input k) l
    PackingCallerProgram.Sources front p ∧ PackingCallerProgram.Empty front ∧
    Circuit.Shape m w ∧
    projectState Exports.bankRegs Exports.bank front = Bank.state (front.regs ∘ Exports.bankRegs) w ∧
    p.n ≤ S ∧ p.factors ≤ S ∧ p.incidences ≤ S ∧ p.r ≤ S ∧ p.Q ≤ S ∧ p.s ≤ S ∧
    p.r ^ (2 * p.Q) ≤ S ∧ (∀ i, m.val i ≤ S) ∧ (∀ i, m.len i ≤ S) ∧
    0 < m.val 33 ∧ 0 < m.val 34 ∧
    (Circuit.result Serialization.code m).val 44 = 3 ^ (m.val 34) - 2 ∧
    3 ^ (m.val 34) ≤ 16 * (m.val 21 + 1) ^ 2 := by
  have hmv := QueryModelBudgets.serialized_model_values_le (q.input k) l S hv
  have hml := QueryModelBudgets.serialized_model_lengths_le (q.input k) l S hl
  obtain ⟨hn,hf,hD,hr,hQ,hs,_,hN,_⟩ :=
    QueryModelBudgets.produced_layout_scalars_le (q.input k) l S hmv
  refine ⟨packing_sources q k front hg l hfront.exported hfront.scopes hfront.forward hfront.ambient,
    packing_empty front hfront.privateEmpty hfront.spare, hfront.shape, hfront.bank,
    hn, ?_, ?_, hr, hQ, hs, hN, hmv, hml, ring_precision_pos _ _ hg,
    ring_degree_pos _ _ hg, ring_exponent _ _ hg, ?_⟩
  · simpa only [packing_factors_eq] using hf
  · simpa only [packingProblem_incidences] using hD
  · have hq : (produce (q.input k)).Q ≠ 0 := by
      have h := hg.2.2.2.2.2.2.1
      omega
    rw [Execute.guardedModel_degree (q.input k) l hq]
    have he : (Execute.guardedModel (q.input k) l).val 21 = (produce (q.input k)).Q :=
      (Execute.guardedModel_public (q.input k) l 4).trans
        (Layout.model_core_values (q.input k) l).2.2.2.2.1
    rw [he]
    exact fieldCard_le (q.input k)

/-- Concrete packing data returned by the guarded frontend preparation. -/
structure FrontPackingData (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) where
  first : MulticolorTypes.Word (packingProblem q k hg).r (packingProblem q k hg).Q
  rest : List (MulticolorTypes.Word (packingProblem q k hg).r (packingProblem q k hg).Q)
  packed : Data
  packingSteps : ℕ

/-- Concrete arithmetic data returned after packing. A standard product keeps
elaboration of the dependent ring objects shallow. -/
def FrontArithmeticData (q : LeafQueryFrontend.Query) (k : ℕ)
    (l : Fin 8 → ℕ) : Type :=
  ℕ × LeafRingSetupProgram.Data ×
    SubexpPreparedQuartic.Modulus 3 ((Execute.guardedModel (q.input k) l).val 33) ×
    RingProgram.ScalarCache 3 ((Execute.guardedModel (q.input k) l).val 33) ×
    RingProgram.ScalarCode 3 ((Execute.guardedModel (q.input k) l).val 33) × Data

namespace FrontArithmeticData

variable {q : LeafQueryFrontend.Query} {k : ℕ} {l : Fin 8 → ℕ}

abbrev arithmeticSteps (data : FrontArithmeticData q k l) := data.1
abbrev ringState (data : FrontArithmeticData q k l) := data.2.1
abbrev modulus (data : FrontArithmeticData q k l) := data.2.2.1
abbrev cache (data : FrontArithmeticData q k l) := data.2.2.2.1
abbrev half (data : FrontArithmeticData q k l) := data.2.2.2.2.1
abbrev output (data : FrontArithmeticData q k l) := data.2.2.2.2.2

end FrontArithmeticData

/-- All concrete data produced by native query preparation. -/
def FrontData (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
    (l : Fin 8 → ℕ) : Type :=
  FrontPackingData q k hg × FrontArithmeticData q k l

namespace FrontData

variable {q : LeafQueryFrontend.Query} {k : ℕ} {hg : Guard (q.input k)}
  {l : Fin 8 → ℕ}

abbrev packing (data : FrontData q k hg l) := data.1
abbrev arithmetic (data : FrontData q k hg l) := data.2
abbrev first (data : FrontData q k hg l) := data.packing.first
abbrev rest (data : FrontData q k hg l) := data.packing.rest
abbrev packed (data : FrontData q k hg l) := data.packing.packed
abbrev packingSteps (data : FrontData q k hg l) := data.packing.packingSteps
abbrev arithmeticSteps (data : FrontData q k hg l) := data.arithmetic.arithmeticSteps
abbrev ringState (data : FrontData q k hg l) := data.arithmetic.ringState
abbrev modulus (data : FrontData q k hg l) := data.arithmetic.modulus
abbrev cache (data : FrontData q k hg l) := data.arithmetic.cache
abbrev half (data : FrontData q k hg l) := data.arithmetic.half
abbrev output (data : FrontData q k hg l) := data.arithmetic.output

end FrontData

/-- Semantic facts for one concrete native preparation run. -/
structure FrontExecution (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) (front : Data) (l : Fin 8 → ℕ)
    (data : FrontData q k hg l) : Prop where
  rows : (data.first :: data.rest).map Subexp.ReadPlan.encodeWord =
    Subexp.AssignmentAlphabetSemantics.wordBytes (packingProblem q k hg).r
      (packingProblem q k hg).Q
  nodup : (data.first :: data.rest).Nodup
  complete : ∀ z, z ∈ data.first :: data.rest
  packing : Eval PackingCallerProgram.command data.packingSteps front data.packed
  packed_words : data.packed.stacks =
    (PackingCallerProgram.result front (packingProblem q k hg) data.first data.rest).stacks
  arithmetic : Eval arithmeticCommand data.arithmeticSteps data.packed data.output
  arithmetic_output : ArithmeticOutput data.packed data.output
    (Execute.guardedModel (q.input k) l) (ring_degree_pos (q.input k) l hg)
    data.modulus data.cache data.half data.ringState
  degree : data.output.stacks 204 =
    List.replicate ((Execute.guardedModel (q.input k) l).val 34) true
  inverse :
    (RingProgram.modelRing ((Execute.guardedModel (q.input k) l).val 33)
      (ring_precision_pos (q.input k) l hg) (ring_degree_pos (q.input k) l hg)
      (IrreducibleSearch.data (ring_degree_pos (q.input k) l hg))
      data.modulus data.cache).decode
      (LayoutDenominatorProgramQuery.value ((Execute.guardedModel (q.input k) l).val 33)
        (IrreducibleSearch.data (ring_degree_pos (q.input k) l hg))
        data.modulus data.cache data.half (data.packed.stacks 740).length) *
      (2 : (IrreducibleSearch.data (ring_degree_pos (q.input k) l hg)).O
        ((Execute.guardedModel (q.input k) l).val 33)) ^
        ((data.packed.stacks 740).length - 1) = 1
  command : Eval command (data.packingSteps + data.arithmeticSteps) front data.output

/-- Time and all-prefix space facts for one concrete native preparation run. -/
structure FrontBounds (front : Data) (S B cost : ℕ)
    {q : LeafQueryFrontend.Query} {k : ℕ} {hg : Guard (q.input k)}
    {l : Fin 8 → ℕ} (data : FrontData q k hg l) : Prop where
  time : data.packingSteps + data.arithmeticSteps ≤ cost
  output_space : ∀ i, (data.output.stacks i).length ≤ max cost B
  trace : Trace (compiled command 700 728) (data.packingSteps + data.arithmeticSteps + 1)
    (front.withPC (some (compiled command 700 728).entry)) (data.output.withPC none)
  prefix_space : ∀ j c, j ≤ data.packingSteps + data.arithmeticSteps + 1 →
    Trace (compiled command 700 728) j
      (front.withPC (some (compiled command 700 728).entry)) c →
    ∀ i, (c.stacks i).length ≤ max cost B

/-- A concrete preparation output paired with its semantic and resource certificates. -/
def FrontRun (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
    (front : Data) (l : Fin 8 → ℕ) (S B cost : ℕ) : Type :=
  { data : FrontData q k hg l //
    FrontExecution q k hg front l data ∧ FrontBounds front S B cost data }

namespace FrontRun

variable {q : LeafQueryFrontend.Query} {k : ℕ} {hg : Guard (q.input k)}
  {front : Data} {l : Fin 8 → ℕ} {S B cost : ℕ}

abbrev data (run : FrontRun q k hg front l S B cost) := run.1
abbrev execution (run : FrontRun q k hg front l S B cost) := run.2.1
abbrev bounds (run : FrontRun q k hg front l S B cost) := run.2.2
abbrev first (run : FrontRun q k hg front l S B cost) := run.data.first
abbrev rest (run : FrontRun q k hg front l S B cost) := run.data.rest
abbrev packed (run : FrontRun q k hg front l S B cost) := run.data.packed
abbrev packingSteps (run : FrontRun q k hg front l S B cost) := run.data.packingSteps
abbrev arithmeticSteps (run : FrontRun q k hg front l S B cost) := run.data.arithmeticSteps
abbrev ringState (run : FrontRun q k hg front l S B cost) := run.data.ringState
abbrev modulus (run : FrontRun q k hg front l S B cost) := run.data.modulus
abbrev cache (run : FrontRun q k hg front l S B cost) := run.data.cache
abbrev half (run : FrontRun q k hg front l S B cost) := run.data.half
abbrev output (run : FrontRun q k hg front l S B cost) := run.data.output
abbrev rows (run : FrontRun q k hg front l S B cost) := run.execution.rows
abbrev nodup (run : FrontRun q k hg front l S B cost) := run.execution.nodup
abbrev complete (run : FrontRun q k hg front l S B cost) := run.execution.complete
abbrev packing (run : FrontRun q k hg front l S B cost) := run.execution.packing
abbrev packed_words (run : FrontRun q k hg front l S B cost) := run.execution.packed_words
abbrev arithmetic (run : FrontRun q k hg front l S B cost) := run.execution.arithmetic
abbrev arithmetic_output (run : FrontRun q k hg front l S B cost) :=
  run.execution.arithmetic_output
abbrev degree (run : FrontRun q k hg front l S B cost) := run.execution.degree
abbrev inverse (run : FrontRun q k hg front l S B cost) := run.execution.inverse
abbrev command (run : FrontRun q k hg front l S B cost) := run.execution.command
abbrev time (run : FrontRun q k hg front l S B cost) := run.bounds.time
abbrev output_space (run : FrontRun q k hg front l S B cost) := run.bounds.output_space
abbrev trace (run : FrontRun q k hg front l S B cost) := run.bounds.trace
abbrev prefix_space (run : FrontRun q k hg front l S B cost) := run.bounds.prefix_space

end FrontRun


/-- Fully instantiated preparation after the actual guarded frontend. The
semantic producer run is constructed here; the same run has a source-only
time bound and a maximum-prefix bound retaining arbitrary carried words. -/
theorem front_resources : ∃ C d : ℕ,
    ∀ (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
      (base front : Data) (l : Fin 8 → ℕ) (bw : Bank.Words) (S B : ℕ),
      FrontState q k base front l bw →
      (∀ i, ¬ LeafProgram.OuterCarried.hidden i → (front.stacks i).length ≤ S) →
      (∀ i, LeafProgram.OuterCarried.hidden i → (front.stacks i).length ≤ B) →
      (∀ i, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) l)).val i ≤ S) →
      (∀ i, (Circuit.result Serialization.code (Execute.guardedModel (q.input k) l)).len i ≤ S) →
      front.stacks 728 = [] →
      Nonempty (FrontRun q k hg front l S B (C * (S + 1) ^ d)) := by
  obtain ⟨Cs,ds,hsemantic⟩ := command_resources
  obtain ⟨C,d,htimed⟩ := command_source_resources
  refine ⟨C,d,?_⟩
  intro q k hg base front l bw S B hfront hvisible hhidden hv hl h728
  obtain ⟨hs,he,hshape,hbank,hn,hf,hD,hr,hQ,heps,htypes,hmv,hml,ht,hd,hexp,hfield⟩ :=
    front_numeric_inputs q k hg base front l bw hfront S hv hl
  have hSA : S ≤ S+B := Nat.le_add_right _ _
  have hall : ∀ i, (front.stacks i).length ≤ S+B := by
    intro i
    by_cases hi : LeafProgram.OuterCarried.hidden i
    · exact (hhidden i hi).trans (Nat.le_add_left _ _)
    · exact (hvisible i hi).trans hSA
  obtain ⟨first,rest,packed,np,na,e,M,cache,half,out,hrows,hnodup,hcomplete,
      hpack,hbytes,harith,houtput,hdegree,hinverse,hrun,_,_,_,_⟩ :=
    hsemantic front (packingProblem q k hg) (Execute.guardedModel (q.input k) l)
      bw (front.regs ∘ Exports.bankRegs) hs he hshape hbank (S+B) hall
      (hn.trans hSA) (hf.trans hSA) (hD.trans hSA) (hr.trans hSA) (hQ.trans hSA)
      (heps.trans hSA) (htypes.trans hSA) (fun i => (hv i).trans hSA)
      (fun i => (hl i).trans hSA) (fun i => (hmv i).trans hSA)
      (fun i => (hml i).trans hSA) ht hd hexp hfield h728
  obtain ⟨htime,htrace,hprefix⟩ := htimed front out (np+na) hrun
    (packingProblem q k hg) (Execute.guardedModel (q.input k) l)
    bw (front.regs ∘ Exports.bankRegs) hs he hshape hbank S B hvisible hhidden
    hn hf hD hr hQ heps htypes hv hl hmv hml ht hd hexp hfield h728
  let packingData : FrontPackingData q k hg := {
    first := first
    rest := rest
    packed := packed
    packingSteps := np }
  let arithmeticData : FrontArithmeticData q k l := (na, e, M, cache, half, out)
  let data : FrontData q k hg l := (packingData, arithmeticData)
  let execution : FrontExecution q k hg front l data := {
    rows := hrows
    nodup := hnodup
    complete := hcomplete
    packing := hpack
    packed_words := hbytes
    arithmetic := harith
    arithmetic_output := houtput
    degree := hdegree
    inverse := hinverse
    command := hrun }
  have houtputSpace : ∀ i, (out.stacks i).length ≤ max (C * (S + 1) ^ d) B :=
    fun i => hprefix (np + na + 1) (out.withPC none) le_rfl htrace i
  let bounds : FrontBounds front S B (C * (S + 1) ^ d) data := {
    time := htime
    output_space := houtputSpace
    trace := htrace
    prefix_space := hprefix }
  exact ⟨⟨data, execution, bounds⟩⟩

/-- Packing and arithmetic preserve the current high mask and all collector
words. This is an endpoint fact about the concrete executed outputs. -/
theorem collector_frame (front packed out : Data) (p : PackingCallerProgram.Problem)
    (first : MulticolorTypes.Word p.r p.Q) (rest : List (MulticolorTypes.Word p.r p.Q))
    (hb : packed.stacks = (PackingCallerProgram.result front p first rest).stacks)
    {m : Circuit.Model} {hd : 0 < m.val 34}
    {M : SubexpPreparedQuartic.Modulus 3 (m.val 33)}
    {cache : RingProgram.ScalarCache 3 (m.val 33)} {half : RingProgram.ScalarCode 3 (m.val 33)}
    {e : LeafRingSetupProgram.Data} (ho : ArithmeticOutput packed out m hd M cache half e)
    (i : Fin 768) (hlo : 320 ≤ i.val) (hhi : i.val < 340) :
    out.stacks i = front.stacks i := by
  rw [ho.collectorFrame i hlo hhi, hb]
  exact PackingCallerProgram.result_frame front p first rest i
    (Or.inl (by omega)) (Or.inr (by omega)) (Or.inl (by omega))

/-- Persistent query sources stay byte-identical through the preparation. -/
theorem sources_frame (front packed out : Data) (p : PackingCallerProgram.Problem)
    (first : MulticolorTypes.Word p.r p.Q) (rest : List (MulticolorTypes.Word p.r p.Q))
    (hb : packed.stacks = (PackingCallerProgram.result front p first rest).stacks)
    {m : Circuit.Model} {hd : 0 < m.val 34}
    {M : SubexpPreparedQuartic.Modulus 3 (m.val 33)}
    {cache : RingProgram.ScalarCache 3 (m.val 33)} {half : RingProgram.ScalarCode 3 (m.val 33)}
    {e : LeafRingSetupProgram.Data} (ho : ArithmeticOutput packed out m hd M cache half e)
    (i : Fin 768) (hi : i ∈ ([700,701,702,703,707,708,709] : List (Fin 768))) :
    out.stacks i = front.stacks i := by
  have hf : out.stacks i = packed.stacks i := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ho.highFrame _ (by decide) (by decide) (by decide)
  rw [hf, hb]
  apply PackingCallerProgram.result_frame
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The complete arithmetic suffix preserves every parked packing master. -/
theorem parked_result (front packed out : Data) (p : PackingCallerProgram.Problem)
    (first : MulticolorTypes.Word p.r p.Q) (rest : List (MulticolorTypes.Word p.r p.Q))
    (hb : packed.stacks = (PackingCallerProgram.result front p first rest).stacks)
    {m : Circuit.Model} {hd : 0 < m.val 34}
    {M : SubexpPreparedQuartic.Modulus 3 (m.val 33)}
    {cache : RingProgram.ScalarCache 3 (m.val 33)} {half : RingProgram.ScalarCode 3 (m.val 33)}
    {e : LeafRingSetupProgram.Data} (ho : ArithmeticOutput packed out m hd M cache half e)
    (i : Fin 14) :
    out.stacks (LeafProgram.LayoutMasters.high i) =
      (PackingCallerProgram.result front p first rest).stacks (LeafProgram.LayoutMasters.high i) := by
  rw [arithmetic_parked ho (LeafProgram.LayoutMasters.high i)
    (by change 730 ≤ 730+i.val; omega)
    (by change 730+i.val < 744; have := i.isLt; omega), hb]


/-- The actual preparation call uses only the lower bank. In particular the
retained upper selector words are neither read nor written by any microstep. -/
theorem lift_command_avoids_upper :
    ProgramTapeReplay.AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val)
      (.call (ProgramLinking.liftProgram (compiled command 700 728)
        id HighMarkedFrontend.stackMap)) := by
  apply ProgramTapeReplay.avoids_call_lift_of_range
  intro i hi
  change 768 ≤ i.val at hi
  exact Nat.not_le_of_gt i.isLt hi

/-- Lift the same actual preparation run, paying its callee halt once. Time
is independent of all upper caller words; every prefix retains their bound. -/
theorem lift_command_resources (a : State 40 896) (out : Data) (steps localBound frameBound : ℕ)
    (he : Eval command steps (HighMarkedFrontend.project a) out)
    (hlocal : ∀ k c, k ≤ steps + 1 → Trace (compiled command 700 728) k
      ((HighMarkedFrontend.project a).withPC (some (compiled command 700 728).entry)) c →
      ∀ i, (c.stacks i).length ≤ localBound)
    (hframe : ∀ i, (a.stacks i).length ≤ frameBound) :
    let call : Cmd 40 896 := .call (ProgramLinking.liftProgram (compiled command 700 728)
      id HighMarkedFrontend.stackMap)
    let result := HighMarkedFrontend.result a out
    Eval call (steps + 1) a result ∧
      (∀ i, 768 ≤ i.val → result.stacks i = a.stacks i) ∧
      Trace (compiled call 700 728) (steps + 2)
        (a.withPC (some (compiled call 700 728).entry)) (result.withPC none) ∧
      ∀ k c, k ≤ steps + 2 → Trace (compiled call 700 728) k
        (a.withPC (some (compiled call 700 728).entry)) c →
        ∀ i, (c.stacks i).length ≤ max localBound frameBound := by
  dsimp only
  have ht := compiled_halt_trace he 700 728
  have hcall := eval_call_from_state (compiled command 700 728) id
    HighMarkedFrontend.stackMap a Function.injective_id (Fin.castAdd_injective _ _) ht
  have hp := HighQuerySpace.lifted_call_bound (compiled command 700 728) id
    HighMarkedFrontend.stackMap Function.injective_id (Fin.castAdd_injective _ _)
    a (HighMarkedFrontend.project a) out rfl (steps + 1) (max localBound frameBound) ht
    (fun k c hk hc i => (hlocal k c hk hc i).trans (Nat.le_max_left _ _))
    (fun i => (hframe i).trans (Nat.le_max_right _ _)) 700 728
  exact ⟨hcall, HighMarkedFrontend.result_upper_frame a out,
    compiled_halt_trace hcall 700 728,
    StructuredSpace.compiled_halt_stack_bound hcall 700 728 hp⟩

/-- Every upper caller word is unchanged at every prefix, including the
callee and caller halt microsteps. -/
theorem lift_command_prefix_frame (a : State 40 896) (out : Data) (steps : ℕ)
    (he : Eval command steps (HighMarkedFrontend.project a) out) :
    let call : Cmd 40 896 := .call (ProgramLinking.liftProgram (compiled command 700 728)
      id HighMarkedFrontend.stackMap)
    ∀ k c, k ≤ steps + 2 → Trace (compiled call 700 728) k
      (a.withPC (some (compiled call 700 728).entry)) c →
      ∀ i, 768 ≤ i.val → c.stacks i = a.stacks i := by
  dsimp only
  have hcall := eval_call_from_state (compiled command 700 728) id
    HighMarkedFrontend.stackMap a Function.injective_id (Fin.castAdd_injective _ _)
    (compiled_halt_trace he 700 728)
  have hs := ProgramTapeReplay.eval_rebase (fun i : Fin 896 => 768 ≤ i.val)
    lift_command_avoids_upper hcall (fun _ => [])
  intro k c hk hc i hi
  exact CommandStackTransport.eval_shadow_prefix_frame (fun i : Fin 896 => 768 ≤ i.val)
    lift_command_avoids_upper 700 728 hs hk hc i hi

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
