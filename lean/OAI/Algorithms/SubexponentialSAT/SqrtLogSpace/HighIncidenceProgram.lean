import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceStream
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgramCount
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Enumerators
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramPrepareBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramOrder

/-! The supplied high-coordinate odometer with a fixed-width exact accumulator.
The residual callback is an actual command; its interface is discharged by the
assembled query program. No branch family is stored on any source stack. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgram
open OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration OAI.Algorithms.SubexponentialSAT.ExecCNFTupleOdometer
open OAI.Algorithms.SubexponentialSAT.BinaryArithmetic
open scoped BigOperators

variable {R S : ℕ}

theorem body_step_bounded (p : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgram.Ports R S) (query : Cmd R S) (shape : List ℕ)
    (I : State R S → Prop) (budget width : ℕ) (value : ℕ → ℕ)
    (stable : MassStable p I) (spec : ResidualSpec p query shape I budget width value)
    (words : List (List Bool)) (a : State R S) (hw : words.map List.length = shape)
    (hi : Ready p I a) (hc : a.stacks p.counter.counter = Encoding.encodeList id words)
    (hs : a.stacks p.counter.scratch = []) (hlen : (read p a).length ≤ width)
    (hv : toNat (read p a) + value (CounterPrograms.value words.flatten) < 2 ^ width) :
    ∃ n b, n ≤ budget + 16 * (width + 1) + 3 ∧
      Eval (body p query) n a b ∧ Ready p I b ∧
      b.stacks p.counter.counter = Encoding.encodeList id words ∧
      b.stacks p.counter.scratch = [] ∧ (read p b).length ≤ width ∧
      toNat (read p b) = toNat (read p a) + value (CounterPrograms.value words.flatten) := by
  obtain ⟨n, b, hn, he, hbi, hbc, hbs, hacc, htmp, hwidth, hvalue⟩ :=
    spec words a hw hi hc hs
  obtain ⟨m, hm, regs, ha⟩ := OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Mass.invoke_eval p.mass b
    (fun i => b.regs (p.mass.register i)) (read p b) (b.stacks (p.mass.stack 1))
  rw [mass_self p b htmp] at ha
  let out := add (read p b) (b.stacks (p.mass.stack 1))
  let c := OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Mass.state p.mass b regs out []
  have hread : read p c = out := mass_stack p b regs out [] 0
  have hone : c.stacks (p.mass.stack 1) = [] := mass_stack p b regs out [] 1
  have htwo : c.stacks (p.mass.stack 2) = [] := mass_stack p b regs out [] 2
  have hbwidth : (read p b).length ≤ width := by rwa [hacc]
  have hmax : max (read p b).length (b.stacks (p.mass.stack 1)).length ≤ width :=
    max_le hbwidth hwidth
  refine ⟨n+m, c, by omega, he.seq ha, ⟨stable b regs out [] hbi, hone, htwo⟩,
    ?_, ?_, ?_, ?_⟩
  · exact (mass_frame p b regs out [] _ p.disjoint_counter).trans hbc
  · exact (mass_frame p b regs out [] _ p.disjoint_scratch).trans hbs
  · rw [hread]
    exact HighIncidenceStream.length_add_of_lt width _ _ hbwidth hwidth
      (by simpa only [hacc, hvalue] using hv)
  · rw [hread, toNat_add, hacc, hvalue]

/-- The numerical remaining sum bounds the live word at every callback boundary.
The natural-valued `fuel` is proof data, not an allocated unary counter. -/
theorem loop_sum_bounded (p : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgram.Ports R S) (query : Cmd R S) (shape : List ℕ)
    (I : State R S → Prop) (budget width : ℕ) (value : ℕ → ℕ)
    (cs : CounterForPrograms.FrameStable p.counter (fun _ => I))
    (ms : MassStable p I) (spec : ResidualSpec p query shape I budget width value)
    (fuel : ℕ) :
    ∀ (words : List (List Bool)) (a : State R S), words.map List.length = shape →
      Ready p I a → a.stacks p.counter.counter = Encoding.encodeList id words →
      a.stacks p.counter.scratch = [] → a.regs (p.counter.register 2) = true →
      CounterPrograms.value words.flatten + fuel = 2 ^ words.flatten.length →
      (read p a).length ≤ width →
      toNat (read p a) + rankSum value (CounterPrograms.value words.flatten) fuel < 2 ^ width →
      ∃ n b, Visits p.counter (body p query) shape
          (List.range' (CounterPrograms.value words.flatten) fuel) n a b ∧
        Ready p I b ∧ b.stacks p.counter.scratch = [] ∧ (read p b).length ≤ width ∧
        toNat (read p b) = toNat (read p a) +
          rankSum value (CounterPrograms.value words.flatten) fuel ∧
        n ≤ fuel * (budget + 16 * (width + 1) +
          7 * (Encoding.encodeList id words).length + 8) + 1 := by
  induction fuel with
  | zero =>
    intro words a hw hi hc hs hf hr hl hv
    have hlt := value_lt_power_length words.flatten
    omega
  | succ fuel ih =>
    intro words a hw hi hc hs hf hr hl hv
    have hvstep : toNat (read p a) + value (CounterPrograms.value words.flatten) < 2 ^ width := by
      rw [rankSum_succ] at hv
      omega
    obtain ⟨nb,e,hnb,hbody,hei,he,hes,helen,hevalue⟩ :=
      body_step_bounded p query shape I budget width value ms spec words a hw hi hc hs hl hvstep
    obtain ⟨na,hna,hadvance⟩ := advance_eval p.counter words e he hes
    have hnexti : Ready p I (advanceResult p.counter e words) :=
      ready_stable p I cs 0 e _ (advanceResult_outside p.counter e words) hei
    have hnlen : (read p (advanceResult p.counter e words)).length ≤ width := by
      simpa only [read_advance] using helen
    by_cases hz : fuel = 0
    · subst fuel
      have hlast : CounterPrograms.value words.flatten+1 = 2^words.flatten.length := by simpa using hr
      have hcarry := (overflow_at_last words hlast).1
      have hfalse : (advanceResult p.counter e words).regs (p.counter.register 2) = false := by
        simp only [advanceResult_flag,hcarry,Bool.not_true]
      have htail : Visits p.counter (body p query) shape [] 1
          (advanceResult p.counter e words) (advanceResult p.counter e words) := .done _ hfalse
      refine ⟨(nb+na)+1+1, advanceResult p.counter e words, ?_, hnexti,
        advanceResult_scratch p.counter e words, hnlen, ?_, ?_⟩
      · simpa using Visits.step hf hw hc hbody he hadvance htail
      · rw [read_advance, hevalue]
        simp
      · simp only [zero_add, one_mul]
        omega
    · have hbefore : CounterPrograms.value words.flatten+1 < 2^words.flatten.length := by omega
      obtain ⟨hcarry,hvalue⟩ := advance_before_last words hbefore
      have htrue : (advanceResult p.counter e words).regs (p.counter.register 2) = true := by
        simp only [advanceResult_flag,hcarry,Bool.not_false]
      have hrem : CounterPrograms.value (bumpWords words).2.flatten+fuel =
          2^(bumpWords words).2.flatten.length := by
        rw [bumpWords_flatten_length,hvalue]
        omega
      have hnvalue : toNat (read p (advanceResult p.counter e words)) +
          rankSum value (CounterPrograms.value (bumpWords words).2.flatten) fuel < 2 ^ width := by
        rw [read_advance, hevalue, hvalue]
        rw [rankSum_succ] at hv
        omega
      obtain ⟨nt,f,ht,hfi,hfs,hflen,hfvalue,hbound⟩ := ih (bumpWords words).2
        (advanceResult p.counter e words) ((bumpWords_lengths words).trans hw)
        hnexti (advanceResult_counter p.counter e words) (advanceResult_scratch p.counter e words)
        htrue hrem hnlen hnvalue
      rw [bumpWords_encoded_length] at hbound
      refine ⟨(nb+na)+nt+1,f,?_,hfi,hfs,hflen,?_,?_⟩
      · simpa only [List.range'_succ,hvalue] using Visits.step hf hw hc hbody he hadvance ht
      · rw [hfvalue, read_advance, hevalue, hvalue, rankSum_succ]
        omega
      · rw [Nat.succ_mul]
        omega

/-- Exact summation by the fixed odometer, with retained word width independent
of the exponential number of callbacks. -/
theorem enumerate_sum_bounded (p : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgram.Ports R S) (query : Cmd R S) (shape : List ℕ)
    (I : State R S → Prop) (budget width : ℕ) (value : ℕ → ℕ)
    (cs : CounterForPrograms.FrameStable p.counter (fun _ => I))
    (ms : MassStable p I) (spec : ResidualSpec p query shape I budget width value)
    (words : List (List Bool)) (a : State R S) (hw : words.map List.length = shape)
    (hi : Ready p I a) (hc : a.stacks p.counter.counter = Encoding.encodeList id words)
    (hs : a.stacks p.counter.scratch = []) (hz : CounterPrograms.value words.flatten = 0)
    (hl : (read p a).length ≤ width)
    (hv : toNat (read p a) + rankSum value 0 (2 ^ words.flatten.length) < 2 ^ width) :
    ∃ n b, Eval (enumerate p.counter (body p query)) (1+n) a b ∧
      Visits p.counter (body p query) shape (List.range' 0 (2 ^ words.flatten.length)) n
        (startResult p.counter a) b ∧ Ready p I b ∧ b.stacks p.counter.scratch = [] ∧
      (read p b).length ≤ width ∧
      toNat (read p b) = toNat (read p a) + rankSum value 0 (2 ^ words.flatten.length) ∧
      1+n ≤ 2 ^ words.flatten.length *
        (budget + 16 * (width + 1) + 7 * (Encoding.encodeList id words).length + 8) + 2 := by
  have hstart : Eval (startCmd p.counter) 1 a (startResult p.counter a) := .base (.atom _ _)
  have hsi := ready_stable p I cs 0 a (startResult p.counter a) (fun _ _ _ => rfl) hi
  have hread : read p (startResult p.counter a) = read p a := rfl
  obtain ⟨n,b,hv,hbi,hbs,hlen,hval,hn⟩ := loop_sum_bounded p query shape I budget width value cs ms spec
    (2 ^ words.flatten.length) words (startResult p.counter a) hw hsi
    (by simpa using hc) (by simpa using hs) (startResult_flag p.counter a)
    (by rw [hz]; omega) (by rwa [hread]) (by rw [hread]; simpa only [hz] using hv)
  refine ⟨n,b,hstart.seq hv.eval,?_,hbi,hbs,hlen,?_,?_⟩
  · simpa only [hz] using hv
  · rw [hread] at hval
    simpa only [hz] using hval
  · omega

/-- The physical high-variable stream counts all original assignments once,
including the sole branch for an empty high set. -/
theorem enumerate_full_count_bounded {V : Type*} [Fintype V] [DecidableEq V]
    (p : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgram.Ports R S) (query : Cmd R S) (H : Finset V) (order : Fin H.card ≃ H)
    (P : (V → Bool) → Prop) [DecidablePred P]
    (I : State R S → Prop) (budget width : ℕ) (value : ℕ → ℕ)
    (hwidth : Fintype.card V + 1 ≤ width)
    (cs : CounterForPrograms.FrameStable p.counter (fun _ => I))
    (ms : MassStable p I)
    (spec : ResidualSpec p query (List.replicate H.card 1) I budget width value)
    (hvalue : ∀ r : Fin (2 ^ H.card), value r.val =
      ∑ b : {v : V // v ∉ H} → Bool,
        if P (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence.glue H
          (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Rank.highEquiv order r) b) then 1 else 0)
    (a : State R S) (hi : Ready p I a)
    (hc : a.stacks p.counter.counter = Encoding.encodeList id (List.replicate H.card [false]))
    (hs : a.stacks p.counter.scratch = []) (ha : read p a = []) :
    ∃ n b, Eval (enumerate p.counter (body p query)) (1+n) a b ∧
      Ready p I b ∧ b.stacks p.counter.scratch = [] ∧ (read p b).length ≤ width ∧
      toNat (read p b) = (∑ x : V → Bool, if P x then 1 else 0) ∧
      1+n ≤ 2 ^ H.card * (budget + 16 * (width + 1) + 28 * H.card + 15) + 2 := by
  have htotal : rankSum value 0 (2 ^ H.card) ≤ 2 ^ Fintype.card V := by
    rw [rankSum_original H order P value hvalue]
    calc
      _ ≤ ∑ _x : V → Bool, 1 := Finset.sum_le_sum (by intros; split <;> omega)
      _ = _ := by simp
  have hpow : 2 ^ Fintype.card V < 2 ^ width :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  have hflat : (List.replicate H.card [false]).flatten.length = H.card := by simp
  have henc : (Encoding.encodeList id (List.replicate H.card [false])).length = 4 * H.card + 1 := by
    rw [ExecCNFTupleOdometer.encoded_length, hflat, List.length_replicate]
    omega
  obtain ⟨n,b,he,hvis,hbi,hbs,hlen,hval,hn⟩ :=
    enumerate_sum_bounded p query (List.replicate H.card 1) I budget width value cs ms spec
      (List.replicate H.card [false]) a (by simp) hi hc hs
      (by simp)
      (by simp [ha]) (by simpa only [ha, toNat_nil, zero_add, hflat] using htotal.trans_lt hpow)
  rw [hflat, henc] at hn
  rw [ha, toNat_nil, zero_add, hflat] at hval
  refine ⟨n,b,he,hbi,hbs,hlen,hval.trans (rankSum_original H order P value hvalue), ?_⟩
  convert hn using 1; ring

/-- All prefixes of the actual high-assignment loop obey one common bound.
The callback premise concerns its compiled microprogram and every port; the
surrounding odometer and persistent accumulator are covered here. -/
theorem visits_sum_stack_bound (p : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgram.Ports R S) (query : Cmd R S) (shape : List ℕ)
    (I : State R S → Prop) (budget width : ℕ) (value : ℕ → ℕ)
    (cs : CounterForPrograms.FrameStable p.counter (fun _ => I))
    (ms : MassStable p I) (spec : ResidualSpec p query shape I budget width value)
    (boundaryBound callbackBound : ℕ)
    (hboundary : ∀ words a, words.map List.length = shape → Ready p I a →
      a.stacks p.counter.counter = Encoding.encodeList id words →
      a.stacks p.counter.scratch = [] → (read p a).length ≤ width →
      ∀ i, (a.stacks i).length ≤ boundaryBound)
    (hcallback : ∀ words a b nb, words.map List.length = shape → Ready p I a →
      a.stacks p.counter.counter = Encoding.encodeList id words →
      a.stacks p.counter.scratch = [] → (read p a).length ≤ width →
      toNat (read p a) + value (CounterPrograms.value words.flatten) < 2 ^ width →
      Eval (body p query) nb a b →
      ∀ prefixSteps intermediate, prefixSteps ≤ nb →
        Trace (compiled (body p query) p.counter.counter p.counter.counter) prefixSteps
          (a.withPC (some (compiled (body p query) p.counter.counter p.counter.counter).entry))
          intermediate → ∀ i, (intermediate.stacks i).length ≤ callbackBound)
    {ranks : List ℕ} {steps : ℕ} {a b : State R S}
    (hvis : Visits p.counter (body p query) shape ranks steps a b)
    (hi : Ready p I a)
    (hwitness : ∃ words, words.map List.length = shape ∧
      a.stacks p.counter.counter = Encoding.encodeList id words)
    (hs : a.stacks p.counter.scratch = []) (hl : (read p a).length ≤ width)
    (hv : toNat (read p a) + (ranks.map value).sum < 2 ^ width) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (compiled (loopCmd p.counter (body p query)) p.counter.counter p.counter.counter)
        prefixSteps (a.withPC (some (compiled (loopCmd p.counter (body p query))
          p.counter.counter p.counter.counter).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤
        max callbackBound (S * boundaryBound + 7 * (2 * shape.sum + 2 * shape.length + 1) + 4) := by
  let bound := max callbackBound
    (S * boundaryBound + 7 * (2 * shape.sum + 2 * shape.length + 1) + 4)
  have hB : boundaryBound ≤ bound := by
    have hS : 1 ≤ S := by have := p.counter.counter.isLt; omega
    have hm : boundaryBound ≤ S * boundaryBound := by
      simpa using Nat.mul_le_mul_right boundaryBound hS
    exact hm.trans ((Nat.le_add_right _ _).trans
      ((Nat.le_add_right _ _).trans (Nat.le_max_right _ _)))
  induction hvis with
  | done a hf =>
      obtain ⟨words, hw, hc⟩ := hwitness
      exact StructuredSpace.while_false_stack_bound _ _ a hf
        (fun i => (hboundary words a hw hi hc hs hl i).trans hB)
        _ _ _ (compiled_site _ p.counter.counter p.counter.counter)
  | @step words a middle b nb na nt ranks hf hw hc hb he ha tail ih =>
      have hvstep : toNat (read p a) + value (CounterPrograms.value words.flatten) < 2 ^ width := by
        simp only [List.map_cons, List.sum_cons] at hv
        omega
      obtain ⟨nc,c,_,hbc,hci,hcc,hcs,hcl,hcv⟩ :=
        body_step_bounded p query shape I budget width value ms spec words a hw hi hc hs hl hvstep
      have hn : nb = nc := StreamResources.eval_steps_eq p.counter.counter p.counter.counter hb hbc
      have heq : middle = c := by
        have ht := trace_same_length_unique (compiled_halt_trace hb p.counter.counter p.counter.counter)
          (by simpa only [hn] using compiled_halt_trace hbc p.counter.counter p.counter.counter)
        exact congrArg StructuredProgram.State.ofCfg ht
      subst c
      have hnexti : Ready p I (advanceResult p.counter middle words) :=
        ready_stable p I cs 0 middle _ (advanceResult_outside p.counter middle words) hci
      have hnextl : (read p (advanceResult p.counter middle words)).length ≤ width := by
        simpa only [read_advance] using hcl
      have hnextv : toNat (read p (advanceResult p.counter middle words)) +
          (ranks.map value).sum < 2 ^ width := by
        rw [read_advance, hcv]
        simp only [List.map_cons, List.sum_cons] at hv
        omega
      have hnextw : ∃ ws, ws.map List.length = shape ∧
          (advanceResult p.counter middle words).stacks p.counter.counter =
            Encoding.encodeList id ws :=
        ⟨(bumpWords words).2, (bumpWords_lengths words).trans hw,
          advanceResult_counter p.counter middle words⟩
      have htail := ih hnexti hnextw (advanceResult_scratch p.counter middle words) hnextl hnextv
      obtain ⟨nk,_,hk,hlocal⟩ := Enumerators.advance_stack_bound p.counter words middle he hcs
        boundaryBound (hboundary words middle hw hci hcc hcs hcl)
      have hnk : na = nk := StreamResources.eval_steps_eq p.counter.counter p.counter.counter ha hk
      have hcontrol : ∀ prefixSteps intermediate, prefixSteps ≤ na →
          Trace (compiled (advanceCmd p.counter) p.counter.counter p.counter.counter) prefixSteps
            (middle.withPC (some (compiled (advanceCmd p.counter)
              p.counter.counter p.counter.counter).entry)) intermediate →
          ∀ i, (intermediate.stacks i).length ≤ bound := by
        intro prefixSteps intermediate hle htrace i
        rw [hnk] at hle
        have ht := hlocal prefixSteps intermediate hle htrace i
        rw [Enumerators.encoded_shape_length hw] at ht
        exact ht.trans (Nat.le_max_right _ _)
      have hbody : ∀ prefixSteps intermediate, prefixSteps ≤ nb →
          Trace (compiled (body p query) p.counter.counter p.counter.counter) prefixSteps
            (a.withPC (some (compiled (body p query) p.counter.counter p.counter.counter).entry))
            intermediate → ∀ i, (intermediate.stacks i).length ≤ bound := by
        intro prefixSteps intermediate hle htrace i
        exact (hcallback words a middle nb hw hi hc hs hl hvstep hb
          prefixSteps intermediate hle htrace i).trans (Nat.le_max_left _ _)
      have hsequence := StructuredSpace.sequence_stack_bound hb ha p.counter.counter p.counter.counter
        hbody hcontrol (compiled (.seq (body p query) (advanceCmd p.counter))
          p.counter.counter p.counter.counter)
        (siteAddress (.seq (body p query) (advanceCmd p.counter)))
        (exitAddress (.seq (body p query) (advanceCmd p.counter)))
        (compiled_site _ p.counter.counter p.counter.counter)
      exact StructuredSpace.while_true_stack_bound hf (.seq hb ha) tail.eval
        p.counter.counter p.counter.counter hsequence htail
        _ _ _ (compiled_site _ p.counter.counter p.counter.counter)

/-- A bounded-space residual query followed by the genuine polynomial-time
adder has a uniform callback bound, including all persistent caller stacks. -/
theorem body_stack_bound (p : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgram.Ports R S) (query : Cmd R S) (shape : List ℕ)
    (I : State R S → Prop) (budget width : ℕ) (value : ℕ → ℕ)
    (spec : ResidualSpec p query shape I budget width value)
    (words : List (List Bool)) (a b : State R S) (steps queryBound : ℕ)
    (hw : words.map List.length = shape) (hi : Ready p I a)
    (hc : a.stacks p.counter.counter = Encoding.encodeList id words)
    (hs : a.stacks p.counter.scratch = []) (hl : (read p a).length ≤ width)
    (hquery : ∀ n c, Eval query n a c →
      ∀ prefixSteps intermediate, prefixSteps ≤ n →
        Trace (compiled query p.counter.counter p.counter.counter) prefixSteps
          (a.withPC (some (compiled query p.counter.counter p.counter.counter).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ queryBound)
    (hbody : Eval (body p query) steps a b) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (compiled (body p query) p.counter.counter p.counter.counter) prefixSteps
        (a.withPC (some (compiled (body p query) p.counter.counter p.counter.counter).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤
          S * queryBound + 16 * (width + 1) + 3 := by
  obtain ⟨n,c,_,he,_,_,_,hacc,htmp,hwidth,_⟩ := spec words a hw hi hc hs
  obtain ⟨m,hm,regs,ha⟩ := OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Mass.invoke_eval p.mass c
    (fun i => c.regs (p.mass.register i)) (read p c) (c.stacks (p.mass.stack 1))
  rw [mass_self p c htmp] at ha
  have hcwidth : (read p c).length ≤ width := by rwa [hacc]
  have hmax : max (read p c).length (c.stacks (p.mass.stack 1)).length ≤ width :=
    max_le hcwidth hwidth
  have htime : m ≤ 16 * (width + 1) + 3 := by omega
  have hpost : ∀ i, (c.stacks i).length ≤ queryBound :=
    hquery n c he n _ le_rfl (compiled_trace he p.counter.counter p.counter.counter)
  have hin : dataBits (c.withPC (some (compiled (OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Mass.invoke p.mass)
      p.counter.counter p.counter.counter).entry)) ≤ S * queryBound :=
    StreamResources.dataBits_le_mul _ hpost
  have hadd : ∀ prefixSteps intermediate, prefixSteps ≤ m →
      Trace (compiled (OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Mass.invoke p.mass)
        p.counter.counter p.counter.counter) prefixSteps
        (c.withPC (some (compiled (OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Mass.invoke p.mass)
          p.counter.counter p.counter.counter).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ S * queryBound + 16 * (width + 1) + 3 := by
    intro prefixSteps intermediate hle htrace i
    have hp := StructuredSpace.local_stack_bound
      (compiled (OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Mass.invoke p.mass) p.counter.counter p.counter.counter)
      (steps := 16 * (width + 1) + 3) hin prefixSteps intermediate (hle.trans htime) htrace i
    simpa only [Nat.add_assoc] using hp
  have hS : 1 ≤ S := by have := p.counter.counter.isLt; omega
  have hmul : queryBound ≤ S * queryBound := by
    simpa using Nat.mul_le_mul_right queryBound hS
  have hq : ∀ prefixSteps intermediate, prefixSteps ≤ n →
      Trace (compiled query p.counter.counter p.counter.counter) prefixSteps
        (a.withPC (some (compiled query p.counter.counter p.counter.counter).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ S * queryBound + 16 * (width + 1) + 3 := by
    intro prefixSteps intermediate hle htrace i
    exact (hquery n c he prefixSteps intermediate hle htrace i).trans (by omega)
  have hsequence := StructuredSpace.sequence_stack_bound he ha p.counter.counter p.counter.counter
    hq hadd (compiled (body p query) p.counter.counter p.counter.counter)
    (siteAddress (body p query)) (exitAddress (body p query))
    (compiled_site _ p.counter.counter p.counter.counter)
  have ht : steps = n + m := StreamResources.eval_steps_eq p.counter.counter p.counter.counter
    hbody (he.seq ha)
  simpa only [ht, StructuredCalls.compiled] using hsequence


/-- The complete actual iterator has the same run for exact summation, time,
and every-prefix stack space. Callback obligations remain explicit here. -/
theorem enumerate_sum_trace_bounded (p : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgram.Ports R S)
    (query : Cmd R S) (shape : List ℕ) (I : State R S → Prop)
    (budget width : ℕ) (value : ℕ → ℕ)
    (cs : CounterForPrograms.FrameStable p.counter (fun _ => I))
    (ms : MassStable p I) (spec : ResidualSpec p query shape I budget width value)
    (boundaryBound callbackBound : ℕ)
    (hboundary : ∀ words a, words.map List.length = shape → Ready p I a →
      a.stacks p.counter.counter = Encoding.encodeList id words →
      a.stacks p.counter.scratch = [] → (read p a).length ≤ width →
      ∀ i, (a.stacks i).length ≤ boundaryBound)
    (hcallback : ∀ words a b nb, words.map List.length = shape → Ready p I a →
      a.stacks p.counter.counter = Encoding.encodeList id words →
      a.stacks p.counter.scratch = [] → (read p a).length ≤ width →
      toNat (read p a) + value (CounterPrograms.value words.flatten) < 2 ^ width →
      Eval (body p query) nb a b →
      ∀ prefixSteps intermediate, prefixSteps ≤ nb →
        Trace (compiled (body p query) p.counter.counter p.counter.counter) prefixSteps
          (a.withPC (some (compiled (body p query) p.counter.counter p.counter.counter).entry))
          intermediate → ∀ i, (intermediate.stacks i).length ≤ callbackBound)
    (words : List (List Bool)) (a : State R S) (hw : words.map List.length = shape)
    (hi : Ready p I a) (hc : a.stacks p.counter.counter = Encoding.encodeList id words)
    (hs : a.stacks p.counter.scratch = []) (hz : CounterPrograms.value words.flatten = 0)
    (hl : (read p a).length ≤ width)
    (hv : toNat (read p a) + rankSum value 0 (2 ^ words.flatten.length) < 2 ^ width) :
    ∃ (steps : ℕ) (b : State R S),
      Trace (ExecCNFTupleEnumeration.program p.counter (body p query)) steps
        (a.withPC (some (ExecCNFTupleEnumeration.program p.counter (body p query)).entry))
        (b.withPC none) ∧
      steps ≤ 2 ^ words.flatten.length *
        (budget + 16 * (width + 1) + 7 * (Encoding.encodeList id words).length + 8) + 3 ∧
      Ready p I b ∧ b.stacks p.counter.scratch = [] ∧ (read p b).length ≤ width ∧
      toNat (read p b) = toNat (read p a) + rankSum value 0 (2 ^ words.flatten.length) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace (ExecCNFTupleEnumeration.program p.counter (body p query)) prefixSteps
          (a.withPC (some (ExecCNFTupleEnumeration.program p.counter (body p query)).entry))
          intermediate → ∀ i, (intermediate.stacks i).length ≤
            max callbackBound (S * boundaryBound + 7 * (2 * shape.sum + 2 * shape.length + 1) + 4) := by
  obtain ⟨n,b,he,hvis,hbi,hbs,hbl,hval,hn⟩ :=
    enumerate_sum_bounded p query shape I budget width value cs ms spec words a hw hi hc hs hz hl hv
  have hsi := ready_stable p I cs 0 a (startResult p.counter a) (fun _ _ _ => rfl) hi
  have hloop := visits_sum_stack_bound p query shape I budget width value cs ms spec
    boundaryBound callbackBound hboundary hcallback hvis hsi
    ⟨words,hw,by simpa using hc⟩ (by simpa using hs) hl hv
  refine ⟨1+n+1,b,compiled_halt_trace he p.counter.counter p.counter.counter,
    by omega,hbi,hbs,hbl,hval,?_⟩
  exact OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Enumerators.enumerate_stack_bound p.counter (body p query) hvis hloop


/-- High-coordinate discovery is a polynomial-time local routine. Its complete
32-stack footprint includes the scopes, binary inputs and all arithmetic work. -/
theorem prepare_trace_space (regs : Fin 10 → Bool) (scopes : List (List ℕ))
    (n t : List Bool) (hn : 0 < toNat n) :
    ∃ (steps : ℕ) (b : State 10 32), Trace OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.program steps
      ((OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.initial regs scopes n t).withPC
        (some OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.program.entry)) (b.withPC none) ∧
      steps ≤ 270000 * (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.inputCapacity scopes n t)^3 ∧
      b.stacks 14 = OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.highPrefix scopes
        (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.cut scopes n t) (toNat n) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.program prefixSteps
          ((OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.initial regs scopes n t).withPC
            (some OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          32 * OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.inputCapacity scopes n t +
            270000 * (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.inputCapacity scopes n t)^3 := by
  obtain ⟨b, ⟨steps,hsteps,htrace⟩,hmask⟩ :=
    OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.runsIn regs scopes n t hn
  have ht := hsteps.trans (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.input_budget scopes n t hn)
  have hi : dataBits
      ((OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.initial regs scopes n t).withPC
        (some OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.program.entry)) ≤
      32 * OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.inputCapacity scopes n t := by
    apply StreamResources.dataBits_le_mul
    intro i
    dsimp [OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.initial,
      OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.inputCapacity, StructuredProgram.State.withPC]
    split_ifs <;> first | omega | exact Nat.zero_le _
  refine ⟨steps,b,htrace,ht,hmask,?_⟩
  intro prefixSteps intermediate hle htrace' i
  exact StructuredSpace.local_stack_bound
    OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.program
    (steps := 270000 * (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.inputCapacity scopes n t)^3)
    hi prefixSteps intermediate (hle.trans ht) htrace' i


/-- Residual indices increase with the original ambient identifier. The list
is obtained by filtering the actual finite coordinate list. -/
def freeCoordinates {n : ℕ} (H : Finset (Fin n)) : List (Fin n) :=
  (List.finRange n).filter (fun v => decide (v ∉ H))

theorem freeCoordinates_nodup {n : ℕ} (H : Finset (Fin n)) :
    (freeCoordinates H).Nodup := (List.nodup_finRange n).filter _

@[simp] theorem mem_freeCoordinates {n : ℕ} (H : Finset (Fin n)) (v : Fin n) :
    v ∈ freeCoordinates H ↔ v ∉ H := by simp [freeCoordinates]

def freeRawOrder {n : ℕ} (H : Finset (Fin n)) :
    Fin (freeCoordinates H).length ≃ {v : Fin n // v ∉ H} :=
  (List.Nodup.getEquiv (freeCoordinates H) (freeCoordinates_nodup H)).trans
    (Equiv.subtypeEquivRight (mem_freeCoordinates H))

@[simp] theorem freeCoordinates_length {n : ℕ} (H : Finset (Fin n)) :
    (freeCoordinates H).length = n - H.card := by
  have h := Fintype.card_congr (freeRawOrder H)
  simpa only [Fintype.card_fin, OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence.remaining_variable_count] using h

def freeOrder {n : ℕ} (H : Finset (Fin n)) :
    Fin (n - H.card) ≃ {v : Fin n // v ∉ H} :=
  (finCongr (freeCoordinates_length H).symm).trans (freeRawOrder H)

theorem freeOrder_val {n : ℕ} (H : Finset (Fin n)) (i : Fin (n - H.card)) :
    (freeOrder H i).val = (freeCoordinates H).get ⟨i.val, by simp⟩ := rfl

theorem freeOrder_strictMono {n : ℕ} (H : Finset (Fin n)) :
    StrictMono (fun i => (freeOrder H i).val) := by
  intro i j hij
  dsimp only
  rw [freeOrder_val, freeOrder_val]
  exact ((List.pairwise_lt_finRange n).filter _).rel_get_of_lt hij

theorem freeOrder_stream {n : ℕ} (H : Finset (Fin n)) (x : Fin n → Bool) :
    List.ofFn (fun i => x (freeOrder H i)) = (freeCoordinates H).map x := by
  apply List.ext_get
  · simp
  · intro i hi hj
    simp only [freeOrder_val, List.get_eq_getElem, List.getElem_map,
      List.getElem_ofFn]

private theorem selected_false_map {A : Type*} (xs : List A) (p : A → Bool) (x : A → Bool) :
    OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.selected false (xs.map p) (xs.map x) =
      (xs.filter (fun v => !(p v))).map x := by
  induction xs with
  | nil => rfl
  | cons v xs ih => cases hp : p v <;> simp [OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.selected, hp, ih]

/-- Inserting zeroes on H preserves the exact free-coordinate assignment. -/
def freeFill {n : ℕ} (H : Finset (Fin n)) (bits : Fin (n - H.card) → Bool) : Fin n → Bool :=
  OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence.glue H (fun _ => false) (fun v => bits ((freeOrder H).symm v))

@[simp] theorem freeFill_high {n : ℕ} (H : Finset (Fin n))
    (bits : Fin (n - H.card) → Bool) (v : H) : freeFill H bits v = false := by
  simp [freeFill, OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence.glue, v.property]

@[simp] theorem freeFill_order {n : ℕ} (H : Finset (Fin n))
    (bits : Fin (n - H.card) → Bool) (i : Fin (n - H.card)) :
    freeFill H bits (freeOrder H i) = bits i := by
  simp [freeFill, OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence.glue, (freeOrder H i).property]

def descendingHighMask {n : ℕ} (H : Finset (Fin n)) : List Bool :=
  (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.coordinates n).map (fun v => decide (v ∈ H))

theorem freeFill_high_stream {n : ℕ} (H : Finset (Fin n)) (bits : Fin (n - H.card) → Bool) :
    OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.selected true (descendingHighMask H)
      (List.ofFn (freeFill H bits)).reverse = List.replicate H.card false := by
  rw [← OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.coordinates_stream]
  unfold descendingHighMask
  rw [OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.selected_map]
  change (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.highCoordinates H).map (freeFill H bits) = _
  rw [← OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.highOrder_stream]
  simp

theorem freeFill_low_stream {n : ℕ} (H : Finset (Fin n)) (bits : Fin (n - H.card) → Bool) :
    OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.selected false (descendingHighMask H)
      (List.ofFn (freeFill H bits)).reverse = (List.ofFn bits).reverse := by
  rw [← OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.coordinates_stream]
  unfold descendingHighMask
  rw [selected_false_map]
  have hp : (fun v : Fin n => !(decide (v ∈ H))) = (fun v => decide (v ∉ H)) := by
    funext v
    simp
  rw [hp]
  change (((List.finRange n).reverse).filter (fun v => decide (v ∉ H))).map (freeFill H bits) = _
  rw [List.filter_reverse, List.map_reverse]
  change ((freeCoordinates H).map (freeFill H bits)).reverse = _
  rw [← freeOrder_stream]
  simp

/-- The existing four-stack merger physically expands the reversed residual
mask to an ambient-index mask with zeros at precisely the fixed coordinates. -/
theorem freeFill_padded_program_runsIn {n : ℕ} (regs : Fin 4 → Bool) (H : Finset (Fin n))
    (bits : Fin (n - H.card) → Bool) :
    ∃ rf, RunsIn OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.program (5 * n + 3)
      ((OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state regs (descendingHighMask H)
        (List.replicate H.card false) (List.ofFn bits).reverse []).withPC
          (some OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.program.entry))
      ((OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state rf [] [] []
        (List.ofFn (freeFill H bits))).withPC none) := by
  have hm : (descendingHighMask H).length = n := by
    simp [descendingHighMask, OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.coordinates]
  obtain ⟨rf,hr⟩ := OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.program_runsIn regs
    (descendingHighMask H) (List.ofFn (freeFill H bits)).reverse [] (by simp [hm])
  refine ⟨rf, ?_⟩
  simpa only [freeFill_high_stream, freeFill_low_stream, List.reverse_reverse,
    List.append_nil, hm] using hr


namespace ZeroHigh
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction

/-- An empty fixed-coordinate stream supplies zero in the actual source program. -/
theorem iteration (regs : Fin 4 → Bool) (b x : Bool)
    (mask low out : List Bool) :
    ∃ rf, Eval body 4
      (popped regs (b :: mask) [] (if b then low else x :: low) out)
      (popped rf mask [] low ((if b then false else x) :: out)) := by
  let a := popped regs (b :: mask) [] (if b then low else x :: low) out
  let item : Option Bool := if b then none else some x
  let r := readRegs (readRegs regs 0 1 (some b)) 2 3 item
  refine ⟨r, ?_⟩
  have hp : Eval pushBit 1 (state r mask [] low out)
      (state r mask [] low ((if b then false else x) :: out)) := by
    convert (Eval.base (StructuredProgram.Eval.atom (.push (3 : Fin 4) 2)
      (state r mask [] low out))) using 1
    · rfl
    · apply congrArg (StructuredProgram.State.mk _)
      funext i
      fin_cases i <;> cases b <;> simp [r, item, state, readRegs,
        StructuredProgram.Atom.instr, execInstr]
  have hl : Eval loadBit 2 a (state r mask [] low out) := by
    cases b with
    | false =>
        apply Eval.ite_false (by rfl)
        convert (Eval.base (StructuredProgram.Eval.atom (.pop (2 : Fin 4) 2 3) a)) using 1
        apply congrArg (StructuredProgram.State.mk _)
        funext i
        fin_cases i <;> simp [a, popped, state, readRegs,
          StructuredProgram.Atom.instr, execInstr]
    | true =>
        apply Eval.ite_true (by rfl)
        convert (Eval.base (StructuredProgram.Eval.atom (.pop (1 : Fin 4) 2 3) a)) using 1
        apply congrArg (StructuredProgram.State.mk _)
        funext i
        fin_cases i <;> simp [a, popped, state, readRegs,
          StructuredProgram.Atom.instr, execInstr]
  exact hl.seq (hp.seq (popMask_eval r mask [] low ((if b then false else x) :: out)))

theorem loop_eval (regs : Fin 4 → Bool) (mask xs out : List Bool)
    (hlen : mask.length = xs.length)
    (hzero : ∀ x ∈ selected true mask xs, x = false) :
    ∃ rf, Eval loop (5 * mask.length + 1)
      (popped regs mask [] (selected false mask xs) out)
      (state rf [] [] [] (xs.reverse ++ out)) := by
  induction mask generalizing regs xs out with
  | nil =>
      have hx : xs = [] := List.eq_nil_of_length_eq_zero hlen.symm
      subst xs
      exact ⟨readRegs regs 0 1 none, Eval.while_false (by rfl)⟩
  | cons b mask ih =>
      cases xs with
      | nil => simp at hlen
      | cons x xs =>
          have hz : ∀ v ∈ selected true mask xs, v = false := by
            intro v hv
            apply hzero v
            cases b <;> simp [selected, hv]
          have hx : (if b then false else x) = x := by
            cases b
            · rfl
            · exact (hzero x (by simp [selected])).symm
          obtain ⟨ri, hi⟩ := iteration regs b x mask (selected false mask xs) out
          have hi' : Eval body 4
              (popped regs (b :: mask) [] (selected false (b :: mask) (x :: xs)) out)
              (popped ri mask [] (selected false mask xs) (x :: out)) := by
            simpa only [hx] using (show Eval body 4
              (popped regs (b :: mask) [] (selected false (b :: mask) (x :: xs)) out)
              (popped ri mask [] (selected false mask xs) ((if b then false else x) :: out)) by
                convert hi using 1
                cases b <;> rfl)
          obtain ⟨rf, hr⟩ := ih ri xs (x :: out) (by simpa using hlen) hz
          refine ⟨rf, ?_⟩
          have h := Eval.while_true (show
            (popped regs (b :: mask) [] (selected false (b :: mask) (x :: xs)) out).regs 1 = true by rfl) hi' hr
          convert h using 1 <;> simp only [loop, List.length_cons, List.reverse_cons,
            List.append_assoc, List.singleton_append, Nat.mul_add, Nat.mul_one,
            Nat.add_comm, Nat.add_left_comm]
          omega

theorem command_eval (regs : Fin 4 → Bool) (mask xs out : List Bool)
    (hlen : mask.length = xs.length)
    (hzero : ∀ x ∈ selected true mask xs, x = false) :
    ∃ rf, Eval command (5 * mask.length + 2)
      (state regs mask [] (selected false mask xs) out)
      (state rf [] [] [] (xs.reverse ++ out)) := by
  obtain ⟨rf, hr⟩ := loop_eval regs mask xs out hlen hzero
  refine ⟨rf, ?_⟩
  convert (popMask_eval regs mask [] (selected false mask xs) out).seq hr using 1
  · rfl
  · omega

end ZeroHigh

/-- Runtime zero insertion needs no supplied padding: the fixed high stream is
empty, and the concrete source pop operation returns false. -/
theorem freeFill_command_eval {n : ℕ} (regs : Fin 4 → Bool) (H : Finset (Fin n))
    (bits : Fin (n - H.card) → Bool) :
    ∃ rf, Eval OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.command (5 * n + 2)
      (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state regs (descendingHighMask H)
        [] (List.ofFn bits).reverse [])
      (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state rf [] [] []
        (List.ofFn (freeFill H bits))) := by
  have hm : (descendingHighMask H).length = n := by
    simp [descendingHighMask, OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.coordinates]
  have hz : ∀ x ∈ OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.selected true
      (descendingHighMask H) (List.ofFn (freeFill H bits)).reverse, x = false := by
    rw [freeFill_high_stream]
    intro x hx
    exact (List.mem_replicate.mp hx).2
  obtain ⟨rf,he⟩ := ZeroHigh.command_eval regs (descendingHighMask H)
    (List.ofFn (freeFill H bits)).reverse [] (by simp [hm]) hz
  refine ⟨rf, ?_⟩
  simpa only [freeFill_low_stream, List.reverse_reverse, List.append_nil, hm] using he

theorem freeFill_program_runsIn {n : ℕ} (regs : Fin 4 → Bool) (H : Finset (Fin n))
    (bits : Fin (n - H.card) → Bool) :
    ∃ rf, RunsIn OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.program (5 * n + 3)
      ((OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state regs (descendingHighMask H)
        [] (List.ofFn bits).reverse []).withPC
          (some OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.program.entry))
      ((OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state rf [] [] []
        (List.ofFn (freeFill H bits))).withPC none) := by
  obtain ⟨rf,he⟩ := freeFill_command_eval regs H bits
  exact ⟨rf,5*n+2+1,by omega,compiled_halt_trace he 0 3⟩

/-- Zero insertion uses linear time and bounds every stack at every source
prefix, including unsuccessful pops of the intentionally empty high stream. -/
theorem freeFill_trace_space {n : ℕ} (regs : Fin 4 → Bool) (H : Finset (Fin n))
    (bits : Fin (n - H.card) → Bool) :
    ∃ rf, Trace OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.program (5 * n + 3)
      ((OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state regs (descendingHighMask H)
        [] (List.ofFn bits).reverse []).withPC
          (some OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.program.entry))
      ((OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state rf [] [] []
        (List.ofFn (freeFill H bits))).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ 5 * n + 3 →
        Trace OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.program prefixSteps
          ((OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state regs (descendingHighMask H)
            [] (List.ofFn bits).reverse []).withPC
              (some OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.program.entry)) intermediate →
          ∀ i, (intermediate.stacks i).length ≤ 9 * n + 3 := by
  obtain ⟨rf,he⟩ := freeFill_command_eval regs H bits
  refine ⟨rf,?_,?_⟩
  · exact compiled_halt_trace he 0 3
  · have hi : dataBits
        ((OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state regs (descendingHighMask H)
          [] (List.ofFn bits).reverse []).withPC
            (some OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.program.entry)) ≤ 4 * n := by
      apply StreamResources.dataBits_le_mul
      intro i
      fin_cases i <;> simp [OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state,
        descendingHighMask,
        OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Order.coordinates]
    intro prefixSteps intermediate hle htrace i
    have hb := StructuredSpace.local_stack_bound
      OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.program (steps := 5*n+3)
      hi prefixSteps intermediate hle htrace i
    omega

/-- The physical zero-fill routine encodes exactly the same support transported
from residual indices to ambient coordinates, with no fixed variable inserted. -/
theorem freeFill_support {n : ℕ} (H : Finset (Fin n)) (U : Finset (Fin (n - H.card)))
    (v : Fin n) :
    freeFill H (fun i => decide (i ∈ U)) v =
      decide (v ∈ U.image (fun i => (freeOrder H i).val)) := by
  by_cases hv : v ∈ H
  · have hnot : v ∉ U.image (fun i => (freeOrder H i).val) := by
      intro hm
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hm
      exact (freeOrder H i).property (hi.symm ▸ hv)
    simp [freeFill, OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence.glue, hv, hnot]
  · let i := (freeOrder H).symm ⟨v,hv⟩
    have hi : (freeOrder H i).val = v := by simp [i]
    have hm : v ∈ U.image (fun j => (freeOrder H j).val) ↔ i ∈ U := by
      constructor
      · intro hm
        obtain ⟨j,hj,hv'⟩ := Finset.mem_image.mp hm
        have he : j = i := (freeOrder H).injective (Subtype.ext (hv'.trans hi.symm))
        exact he ▸ hj
      · intro hu
        exact Finset.mem_image.mpr ⟨i,hu,hi⟩
    rw [← hi, freeFill_order]
    simp only [hi, hm]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram
