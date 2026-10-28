import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsRelational
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReadyConstruction
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairCommit
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairControlFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandStackTransport
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun

/-! The actual finite-difference callback uses the physical pair masks and
one semantic node accumulator. The reference support decoding below is used
only in the proof; the executed controller retains its four finite words. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram QueryTupleState QueryPairCommit QueryReadyConstruction
open SignatureTupleSource
open scoped BigOperators
open SqrtLog.ProgramTapeReplay

local notation "Hidden" => (fun i : Fin 896 => Fin.val i=832 ∨ Fin.val i=833)

/-- The outer support represented by a finite ternary word. -/
def outer (N : ℕ) (word : List (Option Bool)) : Finset (Fin N) :=
  Finset.univ.filter (fun i => (word.getD i.val none).isSome)

/-- The inner support consists precisely of the `some true` positions. -/
def inner (N : ℕ) (word : List (Option Bool)) : Finset (Fin N) :=
  Finset.univ.filter (fun i => (word.getD i.val none).getD false)

theorem inner_subset (N : ℕ) (word : List (Option Bool)) :
    inner N word ⊆ outer N word := by
  intro i hi
  simp only [inner,Finset.mem_filter,Finset.mem_univ,true_and] at hi
  simp only [outer,Finset.mem_filter,Finset.mem_univ,true_and]
  change (word.getD i.val none).getD false=true at hi
  cases h : word.getD i.val none with
  | none => rw [h] at hi; cases hi
  | some b => simp

theorem encode_decoded (N : ℕ) (word : List (Option Bool)) (hlen : word.length=N) :
    DifferencePairs.encodePair (outer N word) (inner N word)=word := by
  subst N
  calc
    _=List.ofFn word.get := by
      unfold DifferencePairs.encodePair
      apply congrArg List.ofFn
      funext i
      have hd : word.getD i.val none=word.get i := List.getD_eq_getElem _ _ i.isLt
      simp only [outer,inner,Finset.mem_filter,Finset.mem_univ,true_and,hd]
      cases h : word.get i with
      | none => simp
      | some b => cases b <;> simp
    _=word := List.ofFn_get word

theorem decoded_encode {N : ℕ} (E U : Finset (Fin N)) (hU : U⊆E) :
    outer N (DifferencePairs.encodePair E U)=E ∧
      inner N (DifferencePairs.encodePair E U)=U := by
  apply DifferencePairs.encodePair_injective (inner_subset N _) hU
  exact encode_decoded N _ (by simp [DifferencePairs.encodePair])

/-- This is the additive semantic update performed after the complete tuple
product has been read out. The sign is computed from the actual two supports. -/
def visit {R : Type*} [CommRing R] (N : ℕ)
    (value : Finset (Fin N) → Finset (Fin N) → R)
    (word : List (Option Bool)) (total : R) : R :=
  total+(-1)^((outer N word).card-(inner N word).card)*
    value (outer N word) (inner N word)

/-- The verified native order visits each support pair once, uniformly for
J=0 and J>N. No byte-level representative of a ring element is selected. -/
theorem fold_signed_sum {R : Type*} [CommRing R] (N J : ℕ)
    (value : Finset (Fin N) → Finset (Fin N) → R) (total : R) :
    DifferencePairs.fold (visit N value) N J [] total = total+
      ∑ pair ∈ BooleanDifferences.pairFamily N J,
        (-1)^(pair.1.card-pair.2.card)*value pair.1 pair.2 := by
  have h := (DifferencePairs.fold_decode_sum (visit N value) id (fun _ => True)
    (fun word => (-1)^((outer N word).card-(inner N word).card)*
      value (outer N word) (inner N word)) N J total True.intro
    (fun _ _ _ _ => ⟨True.intro,rfl⟩)).2
  dsimp only [id] at h
  rw [h]
  apply congrArg (fun x => total+x)
  apply Finset.sum_congr rfl
  intro pair hp
  obtain ⟨he,hu⟩ := decoded_encode pair.1 pair.2
    (BooleanDifferences.mem_pairFamily.mp hp).2
  rw [he,hu]

/-- Reindex the actual finite-coordinate pair sum by the chosen free-variable
equivalence. The ambient assignment universe is not changed. -/
theorem sum_pairs_transport {V R : Type*} [Fintype V] [DecidableEq V]
    [AddCommMonoid R] {N : ℕ} (e : Fin N ≃ V) (J : ℕ)
    (f : Finset V → Finset V → R) :
    (∑ pair ∈ BooleanDifferences.pairFamily N J,
      f (e.finsetCongr pair.1) (e.finsetCongr pair.2)) =
      ∑ E ∈ Finset.univ.filter (fun E : Finset V => E.card<J),
        ∑ U ∈ E.powerset,f E U := by
  classical
  let S := Finset.univ.filter (fun E : Finset V => E.card<J)
  have hset : (Finset.univ.filter (fun p : Finset V × Finset V => p.1.card<J ∧ p.2⊆p.1))=
      S.biUnion (fun E => E.powerset.image (fun U => (E,U))) := by
    ext p
    rcases p with ⟨E,U⟩
    simp [S,Finset.mem_biUnion,Finset.mem_image]
  have hd : (S : Set (Finset V)).PairwiseDisjoint
      (fun E => E.powerset.image (fun U => (E,U))) := by
    intro E _ F _ hEF
    apply Finset.disjoint_left.mpr
    intro pair hp hq
    obtain ⟨U,_,hU⟩ := Finset.mem_image.mp hp
    obtain ⟨W,_,hW⟩ := Finset.mem_image.mp hq
    exact hEF (congrArg Prod.fst (hU.trans hW.symm))
  calc
    _=∑ pair ∈ (BooleanDifferences.pairFamily N J).map
        (Equiv.prodCongr e.finsetCongr e.finsetCongr).toEmbedding,f pair.1 pair.2 := by
      rw [Finset.sum_map]
      rfl
    _=∑ pair ∈ S.biUnion (fun E => E.powerset.image (fun U => (E,U))),f pair.1 pair.2 := by
      rw [BooleanDifferences.pairFamily_map_equiv,hset]
    _=_ := by
      rw [Finset.sum_biUnion hd]
      apply Finset.sum_congr rfl
      intro E _
      rw [Finset.sum_image]
      intro U _ W _ heq
      exact (Prod.mk.inj heq).2

/-- Physical words retained across each complete pair, in addition to the
source and ring masters. These include the current node cursor and address. -/
def framePorts : List (Fin 896) :=
  [194,201,202,203,204,207,209,211,212,243,256,280,281,300,301,307,320,322,338,649,
    700,701,702,703,704,705,706,707,708,709,713,714,715,716,717,718,719,728,
    730,731,732,733,734,735,736,737,738,739,740,741,742,743,863]

/-- The semantic accumulator and compact off-controller words form the DFS
invariant. The four controller lengths are bounded by its separate geometry. -/
structure Invariant {r Q n d : ℕ} (q : Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool) (P F : ℕ)
    (source : ProducedSource) (origin : State 40 896)
    (total : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896) : Prop where
  common : CommonReady q node H high P a
  accumulator : NodeAccumulatorMeaning q total a
  compact : ∀ i,(∀ j,i≠QueryStreamProgram.pairPorts.stack j) → (a.stacks i).length ≤ F
  masters : SignatureHeadLoader.MasterFrame source.masters
    (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)
  frame : ∀ i ∈ framePorts,a.stacks i=origin.stacks i

theorem Invariant.stable {r Q n d P F : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {source : ProducedSource}
    {origin a b : State 40 896} {total : Truncated (q.p.model.O q.p.t) q.J}
    (h : Invariant q node H high P F source origin total a)
    (hf : ∀ i,(∀ j,i≠QueryStreamProgram.pairPorts.stack j) → b.stacks i=a.stacks i) :
    Invariant q node H high P F source origin total b := by
  have hout (i : Fin 896) (hi : (i.val < 832) ∨ (836 ≤ i.val)) :
      ∀ j,i≠QueryStreamProgram.pairPorts.stack j := by
    intro j he
    have hv := congrArg Fin.val he
    change i.val=832+j.val at hv
    have hj := j.isLt
    omega
  refine ⟨h.common.frame ?_,h.accumulator.frame (hf 850 (hout 850 (by decide))),
    (fun i hi => by rw [hf i hi]; exact h.compact i hi),?_,?_⟩
  · intro i hi
    have hc : ∀ j ∈ commonPorts,j.val<832 := by simp [commonPorts,Fin.coe_ofNat_eq_mod]
    exact hf i (hout i (Or.inl (hc i hi)))
  · constructor
    intro i hi
    exact (hf (SignatureHeadLoader.lowStacks i) (hout _ (Or.inl (by
      change i.val<832
      have := i.isLt
      omega)))).trans (h.masters.stored i hi)
  · intro i hi
    have hc : ∀ j ∈ framePorts,(j.val < 832) ∨ (836 ≤ j.val) := by
      simp [framePorts,Fin.coe_ofNat_eq_mod]
    exact (hf i (hout i (hc i hi))).trans (h.frame i hi)

/-- The semantic invariant is independent of both opaque bookkeeping words. -/
theorem Invariant.rebase {r Q n d P F : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {source : ProducedSource}
    {origin a : State 40 896} {total : Truncated (q.p.model.O q.p.t) q.J}
    (h : Invariant q node H high P F source origin total a)
    (saved : Fin 896 → List Bool) :
    Invariant q node H high P F source origin total (rebaseState Hidden saved a) := by
  apply h.stable
  intro i hi
  change rebaseStacks Hidden saved a.stacks i=a.stacks i
  apply rebaseStacks_of_not_mem Hidden saved a.stacks i
  rintro (h0|h1)
  · exact hi 0 (Fin.ext h0)
  · exact hi 1 (Fin.ext h1)

/-- The callback's preliminary empty-depth pop changes registers only. -/
theorem cursor_popped_stacks (J : ℕ) (word : List (Option Bool)) (a : State 40 896)
    (ha : DifferencePairsProgram.Cursor QueryStreamProgram.pairPorts 0 J word true a) :
    (DifferencePairsProgram.popped QueryStreamProgram.pairPorts 0 2 a).stacks=a.stacks := by
  have hz : a.stacks (QueryStreamProgram.pairPorts.stack 0)=[] := ha.depth
  simp [DifferencePairsProgram.popped,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,BitProgram.execInstr,hz]

/-- At a callback the two live masks have exactly the active dimension;
erasing only the unread depth/budget words gives the fixed compact cap. -/
theorem cursor_shadow_bound {r Q n d P F : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {source : ProducedSource}
    {origin a : State 40 896} {total : Truncated (q.p.model.O q.p.t) q.J}
    (h : Invariant q node H high P F source origin total a)
    (J : ℕ) (word : List (Option Bool))
    (hc : DifferencePairsProgram.Cursor QueryStreamProgram.pairPorts 0 J word true a)
    (hlen : word.length=n-H.card) (hN : n-H.card ≤ F) :
    ∀ i,((rebaseState Hidden (fun _=>[])
      (DifferencePairsProgram.popped QueryStreamProgram.pairPorts 0 2 a)).stacks i).length ≤ F := by
  apply CommandStackTransport.shadow_stack_bound
  intro i hi
  rw [cursor_popped_stacks J word a hc]
  by_cases he : i=834
  · subst i
    change (a.stacks (QueryStreamProgram.pairPorts.stack 2)).length ≤ F
    rw [hc.outer,List.length_reverse,List.length_map,hlen]
    exact hN
  by_cases hu : i=835
  · subst i
    change (a.stacks (QueryStreamProgram.pairPorts.stack 3)).length ≤ F
    rw [hc.inner,List.length_reverse,List.length_map,hlen]
    exact hN
  apply h.compact
  intro j
  fin_cases j
  · intro h0; exact hi (Or.inl (congrArg Fin.val h0))
  · intro h1; exact hi (Or.inr (congrArg Fin.val h1))
  · exact he
  · exact hu

private theorem start_masters {source : ProducedSource} {a b : State 40 896}
    (hm : SignatureHeadLoader.MasterFrame source.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hf : ∀ i,i∉PairNativeSetup.scratch → i≠851 → i≠857 → i≠858 → b.stacks i=a.stacks i) :
    SignatureHeadLoader.MasterFrame source.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b) := by
  constructor
  intro i hi
  have hn : SignatureHeadLoader.lowStacks i∉PairNativeSetup.scratch ∧
      SignatureHeadLoader.lowStacks i≠851 ∧ SignatureHeadLoader.lowStacks i≠857 ∧
      SignatureHeadLoader.lowStacks i≠858 := by
    simp only [SignatureHeadLoader.masters,List.mem_cons,
      List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact (hf _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2).trans (hm.stored i hi)

/-- The actual paid pair start preserves the node sum and source witness,
resets851, and installs precisely the ambient images of the emitted masks. -/
theorem start_run {r Q n d P F : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {source : ProducedSource}
    {origin : State 40 896} (total : Truncated (q.p.model.O q.p.t) q.J)
    (a : State 40 896) (hi : Invariant q node H high P F source origin total a)
    (E U : Finset (Fin (n-H.card))) (hU : U⊆E)
    (hm : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (he : a.stacks 834=((DifferencePairs.encodePair E U).map Option.isSome).reverse)
    (hu : a.stacks 835=((DifferencePairs.encodePair E U).map (fun x => x.getD false)).reverse)
    (hb : ∀ i,(a.stacks i).length ≤ F) :
    ∃ steps b, Eval QueryExecution.PairStart.command steps a b ∧
      Invariant q node H high P F source origin total b ∧
      QueryReady q node H high
        (E.image (fun i => (HighIncidenceProgram.freeOrder H i).val))
        (U.image (fun i => (HighIncidenceProgram.freeOrder H i).val)) P b ∧
      PairAccumulatorMeaning q 0 b ∧
      (∀ j,b.stacks (QueryStreamProgram.pairPorts.stack j)=a.stacks (QueryStreamProgram.pairPorts.stack j)) ∧
      (∀ i,(b.stacks i).length ≤ F) ∧ steps+1 ≤ 300*(F+n+1)+2*F+5 := by
  obtain ⟨steps,b,hEval,h851,hE,hU',_hs,hframe,hbound,htime⟩ :=
    QueryExecution.PairStart.support_command_run a H E U hU F hm he hu hb
  have hc := hi.common.pair_frame hframe
  have hnode := hi.accumulator.frame (hframe 850 (by decide) (by decide) (by decide) (by decide))
  have hf : ∀ i ∈ framePorts,b.stacks i=origin.stacks i := by
    intro i him
    have hp : ∀ j ∈ framePorts,j∉PairNativeSetup.scratch ∧ j≠851 ∧ j≠857 ∧ j≠858 := by
      simp [framePorts,PairNativeSetup.scratch]
    exact (hframe i (hp i him).1 (hp i him).2.1 (hp i him).2.2.1 (hp i him).2.2.2).trans
      (hi.frame i him)
  refine ⟨steps,b,hEval,⟨hc,hnode,fun i _=>hbound i,start_masters hi.masters hframe,hf⟩,
    hc.toReady hE hU' (expanded_disjoint H E) (Finset.image_subset_image hU),
    PairAccumulatorMeaning.zero q b h851,?_,hbound,htime⟩
  intro j
  fin_cases j <;> exact hframe _ (by decide) (by decide) (by decide) (by decide)

/-- The full tuple provider restores its real query masters. The node word
and outer cursor words consequently retain their exact meaning. -/
theorem Invariant.query_frame {r Q n d P F : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {source : ProducedSource}
    {origin a b : State 40 896} {total : Truncated (q.p.model.O q.p.t) q.J}
    (h : Invariant q node H high P F source origin total a)
    (hf : QueryMasterFrame a b) (hbound : ∀ i,(b.stacks i).length ≤ F)
    (h649 : b.stacks 649=a.stacks 649) :
    Invariant q node H high P F source origin total b := by
  refine ⟨h.common.frame ?_,h.accumulator.frame (hf.word 850 (by decide)),
    (fun i _=>hbound i),source_frame_of_queryFrame source.masters a b h.masters hf,?_⟩
  · intro i hi
    have hm : ∀ j ∈ commonPorts,j ∈ masterPorts := by simp [commonPorts,masterPorts]
    exact hf.word i (hm i hi)
  · intro i hi
    have hm : ∀ j ∈ framePorts,j=649 ∨ j ∈ masterPorts := by
      intro j hj
      simp only [framePorts,List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals decide
    rcases hm i hi with rfl|hm
    · exact h649.trans (h.frame 649 hi)
    · exact (hf.word i hm).trans (h.frame i hi)

private theorem commit_masters {source : ProducedSource} {a b : State 40 896}
    (hm : SignatureHeadLoader.MasterFrame source.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hf : ∀ i,i∉QueryAssembler.pairScratch → i≠850 → i≠851 → b.stacks i=a.stacks i) :
    SignatureHeadLoader.MasterFrame source.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b) := by
  constructor
  intro i hi
  have hn : SignatureHeadLoader.lowStacks i∉QueryAssembler.pairScratch ∧
      SignatureHeadLoader.lowStacks i≠850 ∧ SignatureHeadLoader.lowStacks i≠851 := by
    simp only [SignatureHeadLoader.masters,List.mem_cons,
      List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact (hf _ hn.1 hn.2.1 hn.2.2).trans (hm.stored i hi)

def startBudget (n F : ℕ) : ℕ := 300*(F+n+1)+2*F+5

def commitBudget {r Q n d : ℕ} (q : Factor.Spec r Q n d) (N F : ℕ) : ℕ :=
  51000*(F+1)+QueryProgram.pairUpdateBudget n (baseWidth 3 q.p.t) d q.p.t q.J N N

/-- The concrete signed commit restores the loop invariant at the SAME
compact cap. Its readout is additive and occurs after the complete tuple sum. -/
theorem commit_run {r Q n d P F : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {source : ProducedSource}
    {origin : State 40 896} (total pairValue : Truncated (q.p.model.O q.p.t) q.J)
    (a : State 40 896) (hi : Invariant q node H high P F source origin total a)
    (E U : Finset (Fin (n-H.card))) (hU : U⊆E)
    (hready : QueryReady q node H high
      (E.image (fun i => (HighIncidenceProgram.freeOrder H i).val))
      (U.image (fun i => (HighIncidenceProgram.freeOrder H i).val)) P a)
    (he : a.stacks 834=((DifferencePairs.encodePair E U).map Option.isSome).reverse)
    (hu : a.stacks 835=((DifferencePairs.encodePair E U).map (fun x => x.getD false)).reverse)
    (hpair : PairAccumulatorMeaning q pairValue a) (hb : ∀ i,(a.stacks i).length ≤ F)
    (hcapacity : q.p.t*q.J*(2*(q.p.t+q.J+n)+2*(d*baseWidth 3 q.p.t)+2) ≤ F) :
    ∃ steps b, Eval QueryAssembler.commitPair steps a b ∧
      Invariant q node H high P F source origin (total+(-1)^(E.card-U.card)*pairValue) b ∧
      (∀ j,b.stacks (QueryStreamProgram.pairPorts.stack j)=a.stacks (QueryStreamProgram.pairPorts.stack j)) ∧
      (∀ i,(b.stacks i).length ≤ F) ∧ steps+1 ≤ commitBudget q (n-H.card) F ∧
      QueryExecution.PrefixBound QueryAssembler.commitPair (steps+1) a
        (896*F+commitBudget q (n-H.card) F) := by
  obtain ⟨steps,b,hEval,hnode,hready',_h851,hframe,hbound,htime,_htrace,hprefix⟩ :=
    QueryPairCommit.run q node H high E U hU P F a hready he hu pairValue total
      hpair hi.accumulator hb hcapacity
  have hElen : (a.stacks 834).length=n-H.card := by
    simp [he,DifferencePairs.encodePair]
  have hUlen : (a.stacks 835).length=n-H.card := by
    simp [hu,DifferencePairs.encodePair]
  rw [hElen,hUlen] at htime hprefix
  have hf : ∀ i ∈ framePorts,b.stacks i=origin.stacks i := by
    intro i him
    have hp : ∀ j ∈ framePorts,j∉QueryAssembler.pairScratch ∧ j≠850 ∧ j≠851 := by
      simp [framePorts,QueryAssembler.pairScratch_mem,Fin.coe_ofNat_eq_mod]
    exact (hframe i (hp i him).1 (hp i him).2.1 (hp i him).2.2).trans (hi.frame i him)
  refine ⟨steps,b,hEval,⟨common_of_ready hready',hnode,fun i _=>hbound i,
    commit_masters hi.masters hframe,hf⟩,?_,hbound,htime,⟨?_⟩⟩
  · intro j
    fin_cases j <;> exact hframe _ (by decide) (by decide) (by decide)
  · intro elapsed z hz htrace i
    simpa only [commitBudget,Nat.add_assoc] using hprefix elapsed z hz htrace i

/-- The complete attained-tuple value for the actual emitted free supports. -/
noncomputable def pairValue (s : ProducedSource) {d : ℕ}
    (q : Factor.Spec s.input.r s.input.Q s.input.n d)
    (H : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (E U : Finset (Fin (s.input.n-H.card))) : Truncated (q.p.model.O q.p.t) q.J :=
  SignatureTupleRun.tupleTotal s.key s.input.r (SignatureTupleRun.emittedValue s q H
    (E.image (fun i => (HighIncidenceProgram.freeOrder H i).val))
    (U.image (fun i => (HighIncidenceProgram.freeOrder H i).val)) high owner head facts)

/-- The native finite-index sum is the exact free-coordinate sum consumed by
the source-target identity. Both masks retain their ambient-coordinate images. -/
theorem signed_sum_free (s : ProducedSource) {d : ℕ}
    (q : Factor.Spec s.input.r s.input.Q s.input.n d)
    (H : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head) :
    (∑ pair ∈ BooleanDifferences.pairFamily (s.input.n-H.card) q.J,
      (-1)^(pair.1.card-pair.2.card)*pairValue s q H high owner head facts pair.1 pair.2) =
    ∑ E ∈ Finset.univ.filter (fun E : Finset (ResidualEmbedding.Free H) => E.card<q.J),
      ∑ U ∈ E.powerset,(-1)^(E.card-U.card)*
        SignatureTupleRun.tupleTotal s.key s.input.r
          (SignatureTupleRun.emittedValue s q H (E.image Subtype.val) (U.image Subtype.val)
            high owner head facts) := by
  classical
  have ht := sum_pairs_transport (HighIncidenceProgram.freeOrder H) q.J
    (fun E U => (-1)^(E.card-U.card)*SignatureTupleRun.tupleTotal s.key s.input.r
      (SignatureTupleRun.emittedValue s q H (E.image Subtype.val) (U.image Subtype.val)
        high owner head facts))
  simp only [Equiv.finsetCongr_apply,Finset.card_map] at ht
  simpa only [pairValue,Finset.map_eq_image,Finset.image_image,Function.comp_def,
    Equiv.toEmbedding_apply] using ht

noncomputable def callbackBudget (s : ProducedSource) {d : ℕ}
    (q : Factor.Spec s.input.r s.input.Q s.input.n d)
    (N F S Z B height : ℕ) : ℕ :=
  startBudget s.input.n F+SignatureTupleRun.runTime s q F S Z B height+commitBudget q N F

def callbackSpace (s : ProducedSource) {d : ℕ}
    (q : Factor.Spec s.input.r s.input.Q s.input.n d) (N F B : ℕ) : ℕ :=
  max (SignatureTupleRun.completeSpace s q F B) (896*F+startBudget s.input.n F+commitBudget q N F)

/-- One complete callback of the fixed program: actual mask expansion,
the complete attained-tuple DFS, and the actual signed dense commit. -/
theorem callback_run (s : ProducedSource) {d M F S Z B width height : ℕ}
    (q : Factor.Spec s.input.r s.input.Q s.input.n d)
    (H : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (caps : QueryVisitorHead.HeadBounds s.input q M F S Z B s.bound width)
    (cap : SignatureTupleComplete.RetainedCap s F)
    (hheads : ∀ depth<s.input.r,s.headSize depth ≤ height)
    (origin a : State 40 896) (total : Truncated (q.p.model.O q.p.t) q.J)
    (hi : Invariant q s.input.node H high M F s origin total a)
    (hm : origin.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (haddress : origin.stacks 649=List.replicate s.base true)
    (E U : Finset (Fin (s.input.n-H.card))) (hU : U⊆E)
    (he : a.stacks 834=((DifferencePairs.encodePair E U).map Option.isSome).reverse)
    (hu : a.stacks 835=((DifferencePairs.encodePair E U).map (fun x => x.getD false)).reverse)
    (hb : ∀ i,(a.stacks i).length ≤ F) :
    ∃ steps b, Eval QueryStreamProgram.pairCallback steps a b ∧
      Invariant q s.input.node H high M F s origin
        (total+(-1)^(E.card-U.card)*pairValue s q H high owner head facts E U) b ∧
      (∀ j,b.stacks (QueryStreamProgram.pairPorts.stack j)=a.stacks (QueryStreamProgram.pairPorts.stack j)) ∧
      (∀ i,(b.stacks i).length ≤ F) ∧
      steps ≤ callbackBudget s q (s.input.n-H.card) F S Z B height ∧
      QueryExecution.PrefixBound QueryStreamProgram.pairCallback (steps+1) a
        (callbackSpace s q (s.input.n-H.card) F B) := by
  obtain ⟨ns,b,hs,hi',hquery,hzero,hcontrol,hb',hts⟩ := start_run total a hi E U hU
    ((hi.frame 338 (by decide)).trans hm) he hu hb
  have hz : b.stacks 649=List.replicate s.base true :=
    (hi'.frame 649 (by decide)).trans haddress
  obtain ⟨nt,c,ht,_htrace,hqc,hacc,hc,hbase,hmasters,htt,hpt⟩ :=
    SignatureTupleRun.run_resources s q H
      (E.image (fun i => (HighIncidenceProgram.freeOrder H i).val))
      (U.image (fun i => (HighIncidenceProgram.freeOrder H i).val)) high owner head facts caps cap
      hheads 0 b hb' hi'.masters hz hquery hzero
  have hi'' := hi'.query_frame hmasters hc (hbase.trans hz.symm)
  have hec : c.stacks 834=((DifferencePairs.encodePair E U).map Option.isSome).reverse :=
    (hmasters.word 834 (by decide)).trans ((hcontrol 2).trans he)
  have huc : c.stacks 835=((DifferencePairs.encodePair E U).map (fun x => x.getD false)).reverse :=
    (hmasters.word 835 (by decide)).trans ((hcontrol 3).trans hu)
  have hpv : PairAccumulatorMeaning q (pairValue s q H high owner head facts E U) c := by
    simpa only [pairValue,zero_add] using hacc
  obtain ⟨nc,e,hcommit,hIe,hce,hebound,htc,hpc⟩ := commit_run total
    (pairValue s q H high owner head facts E U) c hi'' E U hU hqc hec huc hpv hc caps.multiply
  have hall : Eval QueryStreamProgram.pairCallback (ns+(nt+nc)) a e := hs.seq (ht.seq hcommit)
  let D := callbackSpace s q (s.input.n-H.card) F B
  have hsBound : 896*F+ns ≤ D := by
    have hn : ns ≤ startBudget s.input.n F := by unfold startBudget; omega
    exact (by omega : 896*F+ns ≤ 896*F+startBudget s.input.n F+commitBudget q (s.input.n-H.card) F).trans
      (Nat.le_max_right _ _)
  have hps : QueryExecution.PrefixBound QueryExecution.PairStart.command ns a D :=
    (QueryExecution.prefix_local _ ns F a hb).mono hsBound
  have hpt' : QueryExecution.PrefixBound SignatureTupleComplete.command nt b D := by
    constructor
    intro elapsed cfg hp htrace i
    exact (hpt elapsed cfg (by omega) htrace i).trans (Nat.le_max_left _ _)
  have hpc' : QueryExecution.PrefixBound QueryAssembler.commitPair nc c D := by
    constructor
    intro elapsed cfg hp htrace i
    exact (hpc.bound elapsed cfg (by omega) htrace i).trans
      ((by omega : 896*F+commitBudget q (s.input.n-H.card) F ≤         896*F+startBudget s.input.n F+commitBudget q (s.input.n-H.card) F).trans (Nat.le_max_right _ _))
  have hprefix := QueryExecution.prefix_seq hs (ht.seq hcommit) hps
    (QueryExecution.prefix_seq ht hcommit hpt' hpc')
  refine ⟨ns+(nt+nc),e,hall,hIe,?_,hebound,?_,⟨?_⟩⟩
  · intro j
    have hmj : QueryStreamProgram.pairPorts.stack j ∈ masterPorts := by fin_cases j <;> decide
    exact (hce j).trans ((hmasters.word _ hmj).trans (hcontrol j))
  · unfold callbackBudget startBudget
    omega
  · exact (hprefix.withHalt hall).bound

/-- The callback remains total when the untouched unary budget is arbitrary.
Only its proof-side shadow erases832/833; the actual run restores both words
and has exactly the same instruction count. -/
theorem callback_cursor_run (s : ProducedSource) {d M F S Z B width height : ℕ}
    (q : Factor.Spec s.input.r s.input.Q s.input.n d)
    (H : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (caps : QueryVisitorHead.HeadBounds s.input q M F S Z B s.bound width)
    (cap : SignatureTupleComplete.RetainedCap s F)
    (hheads : ∀ depth<s.input.r,s.headSize depth ≤ height)
    (origin a : State 40 896) (total : Truncated (q.p.model.O q.p.t) q.J)
    (hi : Invariant q s.input.node H high M F s origin total a)
    (hm : origin.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (haddress : origin.stacks 649=List.replicate s.base true)
    (J : ℕ) (word : List (Option Bool)) (hlen : word.length=s.input.n-H.card)
    (hc : DifferencePairsProgram.Cursor QueryStreamProgram.pairPorts 0 J word true a) :
    ∃ steps b,
      Eval QueryStreamProgram.pairCallback steps
        (DifferencePairsProgram.popped QueryStreamProgram.pairPorts 0 2 a) b ∧
      steps ≤ callbackBudget s q (s.input.n-H.card) F S Z B height ∧
      (∀ j,b.stacks (QueryStreamProgram.pairPorts.stack j)=a.stacks (QueryStreamProgram.pairPorts.stack j)) ∧
      Invariant q s.input.node H high M F s origin
        (visit (s.input.n-H.card) (pairValue s q H high owner head facts) word total) b ∧
      ((∀ i,(a.stacks i).length ≤ F) → (∀ i,(b.stacks i).length ≤ F) ∧
        QueryExecution.PrefixBound QueryStreamProgram.pairCallback (steps+1)
          (DifferencePairsProgram.popped QueryStreamProgram.pairPorts 0 2 a)
          (callbackSpace s q (s.input.n-H.card) F B)) := by
  let a₀ := DifferencePairsProgram.popped QueryStreamProgram.pairPorts 0 2 a
  let shadow := rebaseState Hidden (fun _=>[]) a₀
  have hsame : a₀.stacks=a.stacks := cursor_popped_stacks J word a hc
  have hi₀ : Invariant q s.input.node H high M F s origin total a₀ :=
    hi.stable (fun i _ => congrFun hsame i)
  have hiShadow := hi₀.rebase (fun _=>[])
  have hbound : ∀ i,(shadow.stacks i).length ≤ F :=
    cursor_shadow_bound hi J word hc hlen (by have := caps.count; omega)
  have hshadow (i : Fin 896) (hv : ¬ Hidden i) : shadow.stacks i=a.stacks i :=
    (rebaseStacks_of_not_mem Hidden (fun _=>[]) a₀.stacks i hv).trans (congrFun hsame i)
  have he : shadow.stacks 834=((DifferencePairs.encodePair
      (outer (s.input.n-H.card) word) (inner (s.input.n-H.card) word)).map Option.isSome).reverse := by
    rw [hshadow 834 (by decide),encode_decoded _ word hlen]
    exact hc.outer
  have hu : shadow.stacks 835=((DifferencePairs.encodePair
      (outer (s.input.n-H.card) word) (inner (s.input.n-H.card) word)).map (fun x=>x.getD false)).reverse := by
    rw [hshadow 835 (by decide),encode_decoded _ word hlen]
    exact hc.inner
  obtain ⟨steps,b,hEval,hI,hcontrol,hb,htime,hprefix⟩ :=
    callback_run s q H high owner head facts caps cap hheads origin shadow total hiShadow hm haddress
      (outer (s.input.n-H.card) word) (inner (s.input.n-H.card) word)
      (inner_subset _ word) he hu hbound
  let out := rebaseState Hidden a₀.stacks b
  have heval : Eval QueryStreamProgram.pairCallback steps a₀ out :=
    CommandStackTransport.eval_shadow Hidden QueryPairControlFrame.callback_avoids hEval
  refine ⟨steps,out,heval,htime,?_,hI.rebase a₀.stacks,?_⟩
  · intro j
    fin_cases j
    · exact congrFun hsame 832
    · exact congrFun hsame 833
    · exact (hcontrol 2).trans (hshadow 834 (by decide))
    · exact (hcontrol 3).trans (hshadow 835 (by decide))
  · intro ha
    have hframe : ∀ i,Hidden i → (a₀.stacks i).length ≤ F := by
      intro i _
      rw [hsame]
      exact ha i
    have hFD : F ≤ callbackSpace s q (s.input.n-H.card) F B := by
      exact (by omega : F ≤ 896*F+startBudget s.input.n F+commitBudget q (s.input.n-H.card) F).trans
        (Nat.le_max_right _ _)
    constructor
    · intro i
      by_cases hv : Hidden i
      · change (rebaseStacks Hidden a₀.stacks b.stacks i).length ≤ F
        rw [rebaseStacks_of_mem Hidden a₀.stacks b.stacks i hv]
        exact hframe i hv
      · change (rebaseStacks Hidden a₀.stacks b.stacks i).length ≤ F
        rw [rebaseStacks_of_not_mem Hidden a₀.stacks b.stacks i hv]
        exact hb i
    · constructor
      have hp := CommandStackTransport.eval_shadow_prefix_bound Hidden
        QueryPairControlFrame.callback_avoids 838 838 hEval
        (fun elapsed cfg he ht i _ => hprefix.bound elapsed cfg he ht i) hframe
      intro elapsed cfg he ht i
      exact (hp elapsed cfg he ht i).trans (max_le (Nat.le_refl _) hFD)

/-- The fixed native pair traversal computes its complete signed tuple sum.
Correctness, measured time, and every source-prefix stack bound refer to this
same run; no tuple evaluator, callback or byte-family service is a premise. -/
theorem run (s : ProducedSource) {d M F S Z B width height : ℕ}
    (q : Factor.Spec s.input.r s.input.Q s.input.n d)
    (H : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (caps : QueryVisitorHead.HeadBounds s.input q M F S Z B s.bound width)
    (cap : SignatureTupleComplete.RetainedCap s F)
    (hheads : ∀ depth<s.input.r,s.headSize depth ≤ height)
    (a : State 40 896) (total : Truncated (q.p.model.O q.p.t) q.J)
    (hi : Invariant q s.input.node H high M F s a total a)
    (hm : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (haddress : a.stacks 649=List.replicate s.base true)
    (ha : ∀ i,(a.stacks i).length ≤ F)
    (hdepth : a.stacks 832=List.replicate (s.input.n-H.card) true)
    (hbudget : a.stacks 833=List.replicate q.J true)
    (houter : a.stacks 834=[]) (hinner : a.stacks 835=[]) :
    ∃ steps b, Eval QueryStreamProgram.pairs steps a b ∧
      Trace (compiled QueryStreamProgram.pairs 832 834) (steps+1)
        (a.withPC (some (compiled QueryStreamProgram.pairs 832 834).entry)) (b.withPC none) ∧
      Invariant q s.input.node H high M F s a
        (total+∑ pair ∈ BooleanDifferences.pairFamily (s.input.n-H.card) q.J,
          (-1)^(pair.1.card-pair.2.card)*pairValue s q H high owner head facts pair.1 pair.2) b ∧
      (∀ j,b.stacks (QueryStreamProgram.pairPorts.stack j)=a.stacks (QueryStreamProgram.pairPorts.stack j)) ∧
      (∀ i,(b.stacks i).length ≤ F) ∧
      steps+1 ≤ DifferencePairsProgram.cost
        (callbackBudget s q (s.input.n-H.card) F S Z B height) (s.input.n-H.card) q.J ∧
      ∀ elapsed cfg,elapsed ≤ steps+1 → Trace (compiled QueryStreamProgram.pairs 832 834) elapsed
        (a.withPC (some (compiled QueryStreamProgram.pairs 832 834).entry)) cfg →
        ∀ i,(cfg.stacks i).length ≤ max (callbackSpace s q (s.input.n-H.card) F B) (896*F+13) := by
  let I := Invariant q s.input.node H high M F s a
  let update := visit (s.input.n-H.card) (pairValue s q H high owner head facts)
  let C := callbackBudget s q (s.input.n-H.card) F S Z B height
  let D := callbackSpace s q (s.input.n-H.card) F B
  have spec : DifferencePairsRelational.CallbackSpec QueryStreamProgram.pairPorts
      QueryStreamProgram.pairCallback update C (s.input.n-H.card) I := by
    constructor
    · intro value d e hf hI
      exact hI.stable hf
    · intro J word value d hn hc hI
      obtain ⟨t,e,he,ht,hf,hIe,_hp⟩ := callback_cursor_run s q H high owner head facts caps cap
        hheads a d value hI hm haddress (J+1) word hn hc
      exact ⟨t,e,ht,he,hf,hIe⟩
  have hcallback : ∀ value j word d e t,word.length=s.input.n-H.card →
      (j+1)+word.countP Option.isSome=q.J →
      DifferencePairsProgram.Cursor QueryStreamProgram.pairPorts 0 (j+1) word true d →
      I value d → (∀ i,(d.stacks i).length ≤ F) →
      Eval QueryStreamProgram.pairCallback t
        (DifferencePairsProgram.popped QueryStreamProgram.pairPorts 0 2 d) e →
      (∀ i,(e.stacks i).length ≤ F) ∧
      ∀ elapsed cfg,elapsed ≤ t → Trace (compiled QueryStreamProgram.pairCallback 832 834) elapsed
        ((DifferencePairsProgram.popped QueryStreamProgram.pairPorts 0 2 d).withPC
          (some (compiled QueryStreamProgram.pairCallback 832 834).entry)) cfg →
        ∀ i,(cfg.stacks i).length ≤ D := by
    intro value j word d e t hn _hj hc hI hb he
    obtain ⟨t',e',he',_ht,_hf,_hIe,hp⟩ := callback_cursor_run s q H high owner head facts caps cap
      hheads a d value hI hm haddress (j+1) word hn hc
    have ht := StreamResources.eval_steps_eq (0 : Fin 896) 0 he he'
    have ho := he.final_unique (0 : Fin 896) he'
    subst t'
    subst e'
    exact ⟨(hp hb).1,fun elapsed cfg hk hz i => (hp hb).2.bound elapsed cfg (by omega) hz i⟩
  obtain ⟨steps,b,he,ht,htrace,hf,hIb,hspace⟩ := DifferencePairsRelational.program_resources
    QueryStreamProgram.pairPorts QueryStreamProgram.pairCallback update I C (s.input.n-H.card) q.J F D
    spec hcallback total a ha hi hdepth hbudget houter hinner
  have hbound : ∀ i,(b.stacks i).length ≤ F := by
    intro i
    by_cases hc : ∃ j,i=QueryStreamProgram.pairPorts.stack j
    · obtain ⟨j,rfl⟩ := hc
      rw [hf j]
      exact ha _
    · exact hIb.compact i (fun j he => hc ⟨j,he⟩)
  have hsemantic := hIb
  rw [show DifferencePairs.fold update (s.input.n-H.card) q.J [] total =
      total+∑ pair ∈ BooleanDifferences.pairFamily (s.input.n-H.card) q.J,
        (-1)^(pair.1.card-pair.2.card)*pairValue s q H high owner head facts pair.1 pair.2
      from fold_signed_sum _ _ _ _] at hsemantic
  exact ⟨steps,b,he,htrace,hsemantic,hf,hbound,ht,hspace⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation
