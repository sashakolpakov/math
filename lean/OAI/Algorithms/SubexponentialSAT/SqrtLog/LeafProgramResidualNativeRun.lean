import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeExact

namespace OAI.Algorithms

/-! Composition lemmas for the unchanged residual instruction table.
The final native endpoint discharges the intermediate worker contract. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native
open SubexponentialSAT BitProgram StructuredCalls LeafNodeSamplesProgram SubexpLiftRing
universe u
noncomputable section

 theorem run_of_contract
    (Valid : (Fin 768 → List Bool) → Prop) (nodes : ℕ → List Bool)
    (Entry : ℕ → Type u) (encode : (i : ℕ) → Entry i → List Bool)
    (ValidEntry : (i : ℕ) → Entry i → Prop) (cost : ℕ → ℕ) (maxJet Q : ℕ)
    (worker : Rel.WorkerContract Node.command Valid nodes
      (Rel.WitnessResult Entry encode ValidEntry) cost maxJet Q)
    (a : Data) (words : List (List Bool)) (h W C count width : ℕ)
    (hcounter : a.stacks 330=ProgramEncoding.encodeRecords words)
    (hhigh : ∀ i∈LeafHighContextProgram.changed,a.stacks i=[])
    (hshape : words.map List.length=List.replicate h 1)
    (hcard : h=HighIncidenceProgram.Restriction.highCount (a.stacks 338))
    (hwidth : ∀ i,(a.stacks i).length ≤ W)
    (h190 : a.stacks 190=[]) (h191 : a.stacks 191=[]) (h265 : a.stacks 265=[])
    (h699 : a.stacks 699=[]) (hprep : ∀ i∈Count.Prepare.ports,a.stacks i=[])
    (hnodes : ((List.finRange Q).map (fun i => nodes i.val)).flatten=a.stacks 256)
    (hvalid : ∀ rh,Valid (Samples.prepared (LeafHighContextProgram.finished a rh words.flatten)).stacks)
    (hblank : ∀ rh i,i∈collectorBlankPorts →
      (Samples.prepared (LeafHighContextProgram.finished a rh words.flatten)).stacks i=[])
    (hsource : ∀ rh,(Samples.prepared (LeafHighContextProgram.finished a rh words.flatten)).stacks 300=
      Encoding.encodeList id (records (Rel.nodeSamples nodes) 0 Q))
    (hrecovery : ∀ rh (entries : (i : Fin Q) → Entry i.val),
      (∀ i,ValidEntry i.val (entries i) ∧ (encode i.val (entries i)).length ≤ maxJet) →
      ∀ rr,∃ r : Recovery (sampled (LeafHighContextProgram.finished a rh words.flatten)
        nodes (fun i => encode i.val (entries i)) rr),
        r.count=count ∧ r.cost ≤ C ∧
        ((countInput (sampled (LeafHighContextProgram.finished a rh words.flatten)
          nodes (fun i => encode i.val (entries i)) rr)).stacks 194).length+
          baseWidth 3 r.t ≤ width) :
    ∃ time out, time ≤ residualBound W (highBound a h) (sampleBudget a nodes cost maxJet Q) C ∧
      Eval Residual.command time a out ∧ BinaryArithmetic.toNat (out.stacks 323)=count ∧
      (out.stacks 323).length ≤ width ∧ out.stacks 324=[] ∧
      out.stacks=Function.update a.stacks 323 (out.stacks 323) ∧
      RegFrame a.regs out.regs := by
  obtain ⟨kh,rh,hkh,hh⟩ := LeafHighContextProgram.run_singleton a words h hcounter hhigh hshape hcard
  let b := LeafHighContextProgram.finished a rh words.flatten
  obtain ⟨entries,hentries,ks,rs,hks,hs,hrs⟩ := samples_of_contract Valid nodes Entry encode ValidEntry
    cost maxJet Q worker b (hvalid rh) (hblank rh) (hsource rh)
  let c := sampled b nodes (fun i => encode i.val (entries i)) rs
  obtain ⟨r,rcount,rcost,rwidth⟩ := hrecovery rh entries hentries rs
  obtain ⟨kc,out,hkc,hc,hvalue,hlen,h324,hprotected,hrc,hstacks⟩ := recover c r
  have hks' : ks ≤ sampleBudget a nodes cost maxJet Q := by
    simpa only [b,sampleBudget_high] using hks
  have hkh' : kh ≤ highBound a h := hkh
  have hcw : ∀ i,(c.stacks i).length ≤ W+highBound a h+sampleBudget a nodes cost maxJet Q := by
    intro i
    have hp := Query.eval_width (hh.seq hs) W hwidth i
    change (c.stacks i).length ≤ _ at hp
    omega
  have htail := tail_bound c r _ C hcw rcost
  have hframe : c.stacks=branchedStacks a words.flatten
      ((List.finRange Q).map (fun i => encode i.val (entries i))).flatten :=
    sampled_high_stacks a rh words.flatten nodes _ rs hhigh h190 h191 (hblank rh) hnodes
  refine ⟨kh+(ks+kc),out,?_,hh.seq (hs.seq hc),hvalue.trans rcount,hlen.le.trans rwidth,h324,?_,?_⟩
  · unfold residualBound
    omega
  · exact hstacks.trans (finalStacks_restored a c words.flatten _ _ hframe hprep h699 h265
      (hhigh 702 (by simp [LeafHighContextProgram.changed]))
      (hhigh 703 (by simp [LeafHighContextProgram.changed])))
  · intro i hlo hhi
    exact (hrc i hlo hhi).trans ((hrs i hlo hhi).trans
      (LeafHighContextProgram.finished_register_frame a rh words.flatten i (by omega)))

end
end SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native

end OAI.Algorithms
