import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgramWideControl
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafBranchProgramCount

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafBranchProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open scoped BigOperators

/-- Setup, exhaustive branching, exact native addition, and return to the
marked collector are one fixed command. The mask is ordinary runtime data. -/
theorem command_rankSum (query : Code) (a : Data) (I : Data → Prop)
    (budget width refBound : ℕ) (value : ℕ → ℕ)
    (cs : CounterForPrograms.FrameStable fixedPorts.counter (fun _ => I))
    (ms : MassStable fixedPorts I)
    (spec : ResidualSpec fixedPorts query
      (List.replicate (HighIncidenceProgram.Branches.trueCount (a.stacks 333)) 1)
      I budget width value)
    (iready : ∀ regs, I (initialized a regs (a.stacks 333)))
    (iref : ∀ b, I b → (b.stacks 321).length ≤ refBound)
    (hc : a.stacks 330 = []) (hs : a.stacks 331 = []) (ha : a.stacks 332 = [])
    (hnext : a.stacks 323 = []) (htmp : a.stacks 324 = []) :
    let h := HighIncidenceProgram.Branches.trueCount (a.stacks 333)
    let N := 2^h
    ∃ time b, Eval (command query) time a (finished b) ∧ I b ∧
      (finished b).stacks 331 = [] ∧
      ((finished b).stacks 323).length ≤ N*(width+1) ∧
      BinaryArithmetic.toNat ((finished b).stacks 323) = rankSum value 0 N ∧
      time ≤ 11*(a.stacks 333).length+5 +
        (N*(budget+16*(N*(width+1)+1)+28*h+15)+2) +
        (2*(4*h+1)+6*(N*(width+1))+2*refBound+15) := by
  dsimp only
  let h := HighIncidenceProgram.Branches.trueCount (a.stacks 333)
  obtain ⟨ni,regs,hni,hinit⟩ := initialize_eval a hc
  let a0 := initialized a regs (a.stacks 333)
  have hi : Ready fixedPorts I a0 := by
    refine ⟨iready regs,?_,?_⟩
    · exact (initialized_frame a regs _ 323 (by decide) (by decide)).trans hnext
    · exact (initialized_frame a regs _ 324 (by decide) (by decide)).trans htmp
  have hscratch : a0.stacks fixedPorts.counter.scratch = [] :=
    (initialized_frame a regs _ 331 (by decide) (by decide)).trans hs
  have hacc : read fixedPorts a0 = [] :=
    (initialized_frame a regs _ 332 (by decide) (by decide)).trans ha
  have hcounter : a0.stacks fixedPorts.counter.counter =
      Encoding.encodeList id (List.replicate h [false]) := initialized_counter a regs _
  obtain ⟨nl,b,hloop,hvis,hbi,hbs,hblen,hbval,hnl⟩ :=
    enumerate_sum fixedPorts query (List.replicate h 1) I budget width value cs ms spec
      (List.replicate h [false]) a0 (by simp) hi hcounter hscratch (by simp)
  have hflat : (List.replicate h [false]).flatten.length = h := by simp
  have henc : (Encoding.encodeList id (List.replicate h [false])).length = 4*h+1 := by
    rw [ExecCNFTupleOdometer.encoded_length,hflat,List.length_replicate]
    omega
  have hclen : (b.stacks 330).length = 4*h+1 := by
    have hh := visits_counter_length hvis
    change (b.stacks 330).length = (a0.stacks 330).length at hh
    exact hh.trans ((congrArg List.length hcounter).trans henc)
  rw [hflat,hacc] at hblen hbval hnl
  rw [henc] at hnl
  simp only [List.length_nil,zero_add,BinaryArithmetic.toNat] at hblen hbval hnl
  have hfinish := finish_eval b hbi.2.2
  have hout : (finished b).stacks 323 = read fixedPorts b :=
    finished_output b hbi.2.1 hbi.2.2
  have href := iref b hbi.1
  refine ⟨ni+(1+nl)+(2*(b.stacks 330).length+6*(b.stacks 332).length+
    2*(b.stacks 321).length+15),b,?_,hbi.1,?_,?_,?_,?_⟩
  · convert hinit.seq (hloop.seq hfinish) using 1 <;> simp [command,Nat.add_assoc]
  · exact (finished_frame b 331 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbs
  · rw [hout]
    exact hblen
  · rw [hout]
    exact hbval
  · change (b.stacks 332).length ≤ 2^h*(width+1) at hblen
    rw [hclen]
    have hnl' : 1+nl ≤ 2^h*(budget+16*(2^h*(width+1)+1)+28*h+15)+2 := by
      convert hnl using 1 ; ring
    dsimp only [h] at hnl' hblen ⊢
    omega

/-- The complete command returns the full original predicate count, rather
than the count from a single high-incidence branch. -/
theorem command_full_count {V : Type*} [Fintype V] [DecidableEq V]
    (query : Code) (a : Data) (I : Data → Prop) (H : Finset V) (order : Fin H.card ≃ H)
    (P : (V → Bool) → Prop) [DecidablePred P]
    (budget width refBound : ℕ) (value : ℕ → ℕ)
    (hdim : HighIncidenceProgram.Branches.trueCount (a.stacks 333) = H.card)
    (cs : CounterForPrograms.FrameStable fixedPorts.counter (fun _ => I))
    (ms : MassStable fixedPorts I)
    (spec : ResidualSpec fixedPorts query (List.replicate H.card 1) I budget width value)
    (iready : ∀ regs, I (initialized a regs (a.stacks 333)))
    (iref : ∀ b, I b → (b.stacks 321).length ≤ refBound)
    (hc : a.stacks 330 = []) (hs : a.stacks 331 = []) (ha : a.stacks 332 = [])
    (hnext : a.stacks 323 = []) (htmp : a.stacks 324 = [])
    (hvalue : ∀ r : Fin (2^H.card), value r.val =
      ∑ b : {v : V // v ∉ H} → Bool,
        if P (HighIncidence.glue H (HighIncidenceProgram.Rank.highEquiv order r) b) then 1 else 0) :
    ∃ time b, Eval (command query) time a (finished b) ∧ I b ∧
      (finished b).stacks 331 = [] ∧
      ((finished b).stacks 323).length ≤ 2^H.card*(width+1) ∧
      BinaryArithmetic.toNat ((finished b).stacks 323) = (∑ x : V → Bool, if P x then 1 else 0) ∧
      time ≤ 11*(a.stacks 333).length+5 +
        (2^H.card*(budget+16*(2^H.card*(width+1)+1)+28*H.card+15)+2) +
        (2*(4*H.card+1)+6*(2^H.card*(width+1))+2*refBound+15) := by
  have spec' : ResidualSpec fixedPorts query
      (List.replicate (HighIncidenceProgram.Branches.trueCount (a.stacks 333)) 1)
      I budget width value := by simpa only [hdim] using spec
  obtain ⟨time,b,he,hbi,hbs,hlen,hout,hbound⟩ := command_rankSum query a I budget width refBound value
    cs ms spec' iready iref hc hs ha hnext htmp
  refine ⟨time,b,he,hbi,hbs,?_,?_,?_⟩
  · simpa only [hdim] using hlen
  · rw [hdim] at hout
    exact hout.trans (rankSum_original H order P value hvalue)
  · simpa only [hdim] using hbound

end SubexponentialSAT.SqrtLog.LeafBranchProgram.Wide

end OAI.Algorithms
