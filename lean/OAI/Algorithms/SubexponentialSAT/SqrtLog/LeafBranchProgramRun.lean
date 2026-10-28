import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgram

namespace OAI.Algorithms

/-! Actual overflow-controlled aggregation. The looser quadratic-in-branches
bound accommodates arbitrary leading zeroes in native binary answers. -/
namespace SubexponentialSAT.SqrtLog.LeafBranchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.ExecCNFTupleEnumeration SubexponentialSAT.ExecCNFTupleOdometer
variable {R S : ℕ}

def rankSum (value : ℕ → ℕ) (start count : ℕ) : ℕ :=
  ((List.range' start count).map value).sum
@[simp] theorem rankSum_zero (value : ℕ → ℕ) (start : ℕ) : rankSum value start 0 = 0 := rfl
@[simp] theorem rankSum_succ (value : ℕ → ℕ) (start count : ℕ) :
    rankSum value start (count+1) = value start + rankSum value (start+1) count := by
  simp [rankSum, List.range'_succ]

theorem ready_stable (p : Ports R S) (I : State R S → Prop)
    (stable : CounterForPrograms.FrameStable p.counter (fun _ => I)) :
    CounterForPrograms.FrameStable p.counter (fun _ => Ready p I) := by
  intro i a b h hi
  exact ⟨stable i a b h hi.1,
    (h _ (p.disjoint_counter 1) (p.disjoint_scratch 1)).symm.trans hi.2.1,
    (h _ (p.disjoint_counter 2) (p.disjoint_scratch 2)).symm.trans hi.2.2⟩

theorem read_advance (p : Ports R S) (a : State R S) (words : List (List Bool)) :
    read p (advanceResult p.counter a words) = read p a :=
  ((advanceResult_outside p.counter a words) _ (p.disjoint_counter 0) (p.disjoint_scratch 0)).symm

/-- Loop induction follows actual callback and odometer executions. `limit`
bounds the total allocated binary length, not a supplied list of answers. -/
theorem loop_sum (p : Ports R S) (query : Cmd R S) (shape : List ℕ)
    (I : State R S → Prop) (budget width : ℕ) (value : ℕ → ℕ)
    (cs : CounterForPrograms.FrameStable p.counter (fun _ => I))
    (ms : MassStable p I) (spec : ResidualSpec p query shape I budget width value)
    (limit fuel : ℕ) :
    ∀ (words : List (List Bool)) (a : State R S), words.map List.length = shape →
      Ready p I a → a.stacks p.counter.counter = Encoding.encodeList id words →
      a.stacks p.counter.scratch = [] → a.regs (p.counter.register 2) = true →
      CounterPrograms.value words.flatten + fuel = 2^words.flatten.length →
      (read p a).length + fuel*(width+1) ≤ limit →
      ∃ n b, Visits p.counter (body p query) shape
          (List.range' (CounterPrograms.value words.flatten) fuel) n a b ∧
        Ready p I b ∧ b.stacks p.counter.scratch = [] ∧ (read p b).length ≤ limit ∧
        BinaryArithmetic.toNat (read p b) = BinaryArithmetic.toNat (read p a) +
          rankSum value (CounterPrograms.value words.flatten) fuel ∧
        n ≤ fuel*(budget+16*(limit+1)+7*(Encoding.encodeList id words).length+8)+1 := by
  induction fuel with
  | zero =>
    intro words a hw hi hc hs hf hr hl
    have hlt := value_lt_power_length words.flatten
    omega
  | succ fuel ih =>
    intro words a hw hi hc hs hf hr hl
    obtain ⟨nb,e,hnb,hbody,hei,he,hes,helen,hevalue⟩ :=
      body_step p query shape I budget width value ms spec words a hw hi hc hs
    obtain ⟨na,hna,hadvance⟩ := advance_eval p.counter words e he hes
    have hnexti : Ready p I (advanceResult p.counter e words) :=
      ready_stable p I cs 0 e _ (advanceResult_outside p.counter e words) hei
    have hnb' : nb ≤ budget+16*(limit+1)+3 := by
      have hm : (read p a).length + width + 1 ≤ limit := by
        rw [Nat.succ_mul] at hl
        omega
      omega
    have hnlen : (read p (advanceResult p.counter e words)).length + fuel*(width+1) ≤ limit := by
      rw [read_advance]
      rw [Nat.succ_mul] at hl
      omega
    by_cases hz : fuel = 0
    · subst fuel
      have hlast : CounterPrograms.value words.flatten+1 = 2^words.flatten.length := by simpa using hr
      have hcarry := (overflow_at_last words hlast).1
      have hfalse : (advanceResult p.counter e words).regs (p.counter.register 2) = false := by
        simp only [advanceResult_flag,hcarry,Bool.not_true]
      have htail : Visits p.counter (body p query) shape [] 1
          (advanceResult p.counter e words) (advanceResult p.counter e words) := .done _ hfalse
      refine ⟨(nb+na)+1+1, advanceResult p.counter e words, ?_, hnexti,
        advanceResult_scratch p.counter e words, by simpa using hnlen, ?_, ?_⟩
      · simpa using Visits.step hf hw hc hbody he hadvance htail
      · rw [read_advance, hevalue]
        simp
      · simp only [zero_add,one_mul]
        omega
    · have hbefore : CounterPrograms.value words.flatten+1 < 2^words.flatten.length := by omega
      obtain ⟨hcarry,hvalue⟩ := advance_before_last words hbefore
      have htrue : (advanceResult p.counter e words).regs (p.counter.register 2) = true := by
        simp only [advanceResult_flag,hcarry,Bool.not_false]
      have hrem : CounterPrograms.value (bumpWords words).2.flatten+fuel =
          2^(bumpWords words).2.flatten.length := by
        rw [bumpWords_flatten_length,hvalue]
        omega
      obtain ⟨nt,f,ht,hfi,hfs,hflen,hfvalue,hbound⟩ := ih (bumpWords words).2
        (advanceResult p.counter e words) ((bumpWords_lengths words).trans hw)
        hnexti (advanceResult_counter p.counter e words) (advanceResult_scratch p.counter e words)
        htrue hrem hnlen
      rw [bumpWords_encoded_length] at hbound
      refine ⟨(nb+na)+nt+1,f,?_,hfi,hfs,hflen,?_,?_⟩
      · simpa only [List.range'_succ,hvalue] using Visits.step hf hw hc hbody he hadvance ht
      · rw [hfvalue, read_advance, hevalue, hvalue, rankSum_succ]
        omega
      · rw [Nat.succ_mul]
        omega

/-- Full branch aggregation executes a fixed loop and returns the exact sum
of the counts computed by its actual residual callback. -/
theorem enumerate_sum (p : Ports R S) (query : Cmd R S) (shape : List ℕ)
    (I : State R S → Prop) (budget width : ℕ) (value : ℕ → ℕ)
    (cs : CounterForPrograms.FrameStable p.counter (fun _ => I))
    (ms : MassStable p I) (spec : ResidualSpec p query shape I budget width value)
    (words : List (List Bool)) (a : State R S) (hw : words.map List.length = shape)
    (hi : Ready p I a) (hc : a.stacks p.counter.counter = Encoding.encodeList id words)
    (hs : a.stacks p.counter.scratch = []) (hz : CounterPrograms.value words.flatten = 0) :
    ∃ n b, Eval (enumerate p.counter (body p query)) (1+n) a b ∧
      Visits p.counter (body p query) shape (List.range' 0 (2^words.flatten.length)) n
        (startResult p.counter a) b ∧ Ready p I b ∧ b.stacks p.counter.scratch = [] ∧
      (read p b).length ≤ (read p a).length+2^words.flatten.length*(width+1) ∧
      BinaryArithmetic.toNat (read p b) = BinaryArithmetic.toNat (read p a) +
        rankSum value 0 (2^words.flatten.length) ∧
      1+n ≤ 2^words.flatten.length *
        (budget+16*((read p a).length+2^words.flatten.length*(width+1)+1)+
          7*(Encoding.encodeList id words).length+8)+2 := by
  have hstart : Eval (startCmd p.counter) 1 a (startResult p.counter a) := .base (.atom _ _)
  have hsi := ready_stable p I cs 0 a (startResult p.counter a) (fun _ _ _ => rfl) hi
  obtain ⟨n,b,hv,hbi,hbs,hlen,hval,hn⟩ := loop_sum p query shape I budget width value cs ms spec
    ((read p a).length+2^words.flatten.length*(width+1)) (2^words.flatten.length)
    words (startResult p.counter a) hw hsi (by simpa using hc) (by simpa using hs)
    (startResult_flag p.counter a) (by rw [hz]; omega) (by exact le_rfl)
  refine ⟨n,b,hstart.seq hv.eval,?_,hbi,hbs,hlen,?_,?_⟩
  · simpa only [hz] using hv
  · have hread : read p (startResult p.counter a) = read p a := rfl
    rw [hread] at hval
    simpa only [hz] using hval
  · omega

/-- The native odometer keeps the framing width constant through every visit. -/
theorem visits_counter_length {p : CounterForPrograms.Ports R S} {query : Cmd R S}
    {shape ranks : List ℕ} {n : ℕ} {a b : State R S}
    (h : Visits p query shape ranks n a b) :
    (b.stacks p.counter).length = (a.stacks p.counter).length := by
  induction h with
  | done d hf => rfl
  | @step words d e f nb na nt ranks hf hw hc hb he ha tail ih =>
    rw [ih, advanceResult_counter, bumpWords_encoded_length, hc]

end SubexponentialSAT.SqrtLog.LeafBranchProgram

end OAI.Algorithms
