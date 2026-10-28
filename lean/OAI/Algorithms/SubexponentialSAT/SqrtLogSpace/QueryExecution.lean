import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleInit
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleSum
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairs
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgramModel

/-! Composition of the concrete streamed query. The traversal resource lemma
keeps the per-head execution time separate from its prefix storage bound;
neither the number of assignments nor their running time is used as space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution

open OAI BitProgram StructuredCalls
open QueryTupleVisitor SignatureTupleProgram

abbrev Data := State 40 896
abbrev Code := Cmd 40 896

/-- A source-prefix assertion for the actual compiled command table. -/
structure PrefixBound (command : Code) (steps : ℕ) (a : Data) (bound : ℕ) : Prop where
  bound : ∀ q z, q ≤ steps → Trace (compiled command 838 838) q
    (a.withPC (some (compiled command 838 838).entry)) z →
    ∀ i, (z.stacks i).length ≤ bound

theorem PrefixBound.mono {command : Code} {steps B D : ℕ} {a : Data}
    (h : PrefixBound command steps a B) (hBD : B ≤ D) :
    PrefixBound command steps a D :=
  ⟨fun q z hq hz i => (h.bound q z hq hz i).trans hBD⟩

/-- Restrict a prefix certificate to a shorter execution prefix. -/
theorem PrefixBound.monoSteps {command : Code} {steps fewer B : ℕ} {a : Data}
    (h : PrefixBound command steps a B) (hfewer : fewer ≤ steps) :
    PrefixBound command fewer a B :=
  ⟨fun q z hq hz i => h.bound q z (hq.trans hfewer) hz i⟩

/-- Extend a command-prefix certificate through the compiled halt transition. -/
theorem PrefixBound.withHalt {command : Code} {steps B : ℕ} {a b : Data}
    (h : PrefixBound command steps a B) (he : Eval command steps a b) :
    PrefixBound command (steps+1) a B :=
  ⟨StructuredSpace.compiled_halt_stack_bound he 838 838 h.bound⟩

theorem prefix_seq {first second : Code} {n m B : ℕ} {a b c : Data}
    (hf : Eval first n a b) (hs : Eval second m b c)
    (hp : PrefixBound first n a B) (hq : PrefixBound second m b B) :
    PrefixBound (.seq first second) (n+m) a B := by
  constructor
  exact StructuredSpace.sequence_stack_bound hf hs 838 838 hp.bound hq.bound
    (compiled (.seq first second) 838 838) (siteAddress (.seq first second))
    (exitAddress (.seq first second)) (compiled_site (.seq first second) 838 838)

theorem prefix_local (command : Code) (steps B : ℕ) (a : Data)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    PrefixBound command steps a (896*B+steps) := by
  constructor
  exact StructuredSpace.local_stack_bound (compiled command 838 838)
    (StreamResources.dataBits_le_mul _ ha)

theorem finished_bound (a : Data) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((finished a).stacks i).length ≤ B := by
  intro i
  rw [finished_stacks]
  by_cases hi : i=838
  · subst i
    simp
  · rw [Function.update_of_ne hi]
    exact ha i

theorem cursor_word_length {base B : ℕ} {word : List Bool}
    {rest : List (List Bool)} {a : Data}
    (hc : FrameCursor base (word::rest) a)
    (ha : ∀ i, (a.stacks i).length ≤ B) : word.length ≤ B := by
  have h := ha 840
  rw [hc.frames] at h
  simp only [suspendedFrames, List.flatMap_cons, List.length_append,
    Encoding.length_frame, List.length_reverse] at h
  omega

/-- The actual frame parser and cleanup are composed with the measured work
trace. The possibly exponential work time does not enter the storage bound. -/
theorem body_prefix (work : Code) (base B D steps : ℕ) (a b : Data)
    (word : List Bool) (rest : List (List Bool))
    (hc : FrameCursor base (word::rest) a)
    (ha : ∀ i, (a.stacks i).length ≤ B)
    (hw : Eval work steps
      (headState a word (suspendedFrames rest) (List.replicate (base+rest.length) true)) b)
    (hb : ∀ i, (b.stacks i).length ≤ B)
    (hp : PrefixBound work steps
      (headState a word (suspendedFrames rest) (List.replicate (base+rest.length) true)) D) :
    PrefixBound (headBody work)
      (6*word.length+5+(steps+(2*(b.stacks 838).length+4))) a
      (max D (904*B+10)) := by
  have hlen := cursor_word_length hc ha
  have hr := readHead_frames a word rest base hc.frames hc.current hc.address
  have hf := finishHead_eval b
  have hread := (prefix_local readHead (6*word.length+5) B a ha).mono
    (show 896*B+(6*word.length+5) ≤ max D (904*B+10) by
      exact (by omega : 896*B+(6*word.length+5) ≤ 904*B+10).trans (Nat.le_max_right _ _))
  have hfinish := (prefix_local finishHead (2*(b.stacks 838).length+4) B b hb).mono
    (show 896*B+(2*(b.stacks 838).length+4) ≤ max D (904*B+10) by
      have h838 := hb 838
      exact (by omega : 896*B+(2*(b.stacks 838).length+4) ≤ 904*B+10).trans
        (Nat.le_max_right _ _))
  exact prefix_seq hr (hw.seq hf) hread
    (prefix_seq hw hf (hp.mono (Nat.le_max_left _ _)) hfinish)

/-- The list is a proof index for the already-emitted frame stack, not an
operational enumeration. This lemma composes actual callback traces and
preserves one fixed endpoint envelope throughout both representative passes. -/
theorem headLoop_resources (work : Code) (base C B D : ℕ)
    (I : List (List Bool) → Data → Prop)
    (step : ∀ word rest a, FrameCursor base (word::rest) a → I (word::rest) a →
      (∀ i, (a.stacks i).length ≤ B) →
      ∃ steps b, Eval work steps
        (headState a word (suspendedFrames rest) (List.replicate (base+rest.length) true)) b ∧
        steps ≤ C ∧ b.stacks 838=word ∧ b.stacks 840=suspendedFrames rest ∧
        b.stacks 843=List.replicate (base+rest.length) true ∧ I rest (finished b) ∧
        (∀ i, (b.stacks i).length ≤ B) ∧
        PrefixBound work steps
          (headState a word (suspendedFrames rest) (List.replicate (base+rest.length) true)) D)
    (words : List (List Bool)) (a : Data) (hc : FrameCursor base words a)
    (hi : I words a) (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∃ steps b, Eval (headLoop work) steps a b ∧ FrameCursor base [] b ∧ I [] b ∧
      (∀ i, (b.stacks i).length ≤ B) ∧
      steps ≤ 8*(words.map List.length).sum+(C+10)*words.length+1 ∧
      PrefixBound (headLoop work) steps a (max D (904*B+10)) := by
  induction words generalizing a with
  | nil =>
      have ht : a.regs 1=false := by simpa using hc.guard
      refine ⟨1,a,Eval.while_false ht,hc,hi,ha,by simp,⟨?_⟩⟩
      exact StructuredSpace.while_false_stack_bound (headBody work) 1 a ht
        (fun i => (ha i).trans ((by omega : B ≤ 904*B+10).trans (Nat.le_max_right _ _)))
        (compiled (headLoop work) 838 838) (siteAddress (headLoop work))
        (exitAddress (headLoop work)) (compiled_site (headLoop work) 838 838)
  | cons word rest ih =>
      obtain ⟨nt,b,hw,ht,h838,h840,h843,hI,hb,hprefix⟩ := step word rest a hc hi ha
      have hr := readHead_frames a word rest base hc.frames hc.current hc.address
      have hf := finishHead_eval b
      have hbody := hr.seq (hw.seq hf)
      have hnext := finished_cursor base rest b h840 h843
      obtain ⟨ns,c,hrest,hc',hi',hb',hcost,hspace⟩ :=
        ih (finished b) hnext hI (finished_bound b B hb)
      have htest : a.regs 1=true := by simpa using hc.guard
      refine ⟨_,c,Eval.while_true htest hbody hrest,hc',hi',hb',?_,⟨?_⟩⟩
      · rw [h838]
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        nlinarith
      · exact StructuredSpace.while_true_stack_bound htest hbody hrest 838 838
          (body_prefix work base B D nt a b word rest hc ha hw hb hprefix).bound
          hspace.bound (compiled (headLoop work) 838 838) (siteAddress (headLoop work))
          (exitAddress (headLoop work)) (compiled_site (headLoop work) 838 838)

/-- Re-read the existing representative stack for either of the two passes.
Both destination words are replaced by paid commands, including on the
second pass after the first has decremented its address to the node offset. -/
def replay (work : Code) : Code := .seq restart (.seq testFrames (headLoop work))

/-- Zero heads execute the real copy/test/halt path and invoke no head work.
In particular the repeated-pair base address649 is retained on this edge case. -/
theorem replay_nil (work : Code) (a : Data)
    (hreps : a.stacks 837=[]) (hscratch : a.stacks 841=[]) :
    Eval (replay work) (restartCost a+2) a (tested (restartState a)) ∧
      (tested (restartState a)).stacks 649=a.stacks 649 := by
  have hr := restart_eval a hscratch
  have ht := testFrames_eval (restartState a)
  have hf : (restartState a).stacks 840=[] := (restartState_words a).1.trans hreps
  have hl : Eval (headLoop work) 1 (tested (restartState a)) (tested (restartState a)) :=
    Eval.while_false (tested_empty _ hf)
  refine ⟨?_,restartState_frame a 649 (by decide) (by decide)⟩
  simpa only [replay, show restartCost a+(1+1)=restartCost a+2 by omega] using
    hr.seq (ht.seq hl)

theorem replay_resources (work : Code) (base C B D : ℕ)
    (I : List (List Bool) → Data → Prop)
    (step : ∀ word rest a, FrameCursor base (word::rest) a → I (word::rest) a →
      (∀ i, (a.stacks i).length ≤ B) →
      ∃ steps b, Eval work steps
        (headState a word (suspendedFrames rest) (List.replicate (base+rest.length) true)) b ∧
        steps ≤ C ∧ b.stacks 838=word ∧ b.stacks 840=suspendedFrames rest ∧
        b.stacks 843=List.replicate (base+rest.length) true ∧ I rest (finished b) ∧
        (∀ i, (b.stacks i).length ≤ B) ∧
        PrefixBound work steps
          (headState a word (suspendedFrames rest) (List.replicate (base+rest.length) true)) D)
    (words : List (List Bool)) (a : Data)
    (hreps : a.stacks 837=suspendedFrames words)
    (haddress : a.stacks 845=List.replicate (base+words.length) true)
    (hcurrent : a.stacks 838=[]) (hscratch : a.stacks 841=[])
    (hi : I words (tested (restartState a)))
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∃ steps b, Eval (replay work) steps a b ∧ FrameCursor base [] b ∧ I [] b ∧
      (∀ i, (b.stacks i).length ≤ B) ∧
      steps+1 ≤ 18*B+8*(words.map List.length).sum+(C+10)*words.length+19 ∧
      PrefixBound (replay work) (steps+1) a (max D (914*B+18)) := by
  have hr := restart_eval a hscratch
  have ht := testFrames_eval (restartState a)
  have hs := restartState_bound a B ha
  have hc := restartState_cursor a base words hreps haddress hcurrent
  obtain ⟨steps,b,he,hcursor,hI,hb,hcost,hprefix⟩ :=
    headLoop_resources work base C B D I step words (tested (restartState a)) hc hi hs
  have hwhole := hr.seq (ht.seq he)
  have hrbound : restartCost a ≤ 18*B+16 := by
    have h840 := ha 840
    have h837 := ha 837
    have h843 := ha 843
    have h845 := ha 845
    unfold restartCost
    omega
  have hrestart := (prefix_local restart (restartCost a) B a ha).mono
    (show 896*B+restartCost a ≤ max D (914*B+18) by
      exact (by omega : 896*B+restartCost a ≤ 914*B+18).trans (Nat.le_max_right _ _))
  have htest := (prefix_local testFrames 1 B (restartState a) hs).mono
    (show 896*B+1 ≤ max D (914*B+18) by
      exact (by omega : 896*B+1 ≤ 914*B+18).trans (Nat.le_max_right _ _))
  have hloop := hprefix.mono (show max D (904*B+10) ≤ max D (914*B+18) from
    max_le_max_left D (by omega))
  have hall := prefix_seq hr (ht.seq he) hrestart (prefix_seq ht he htest hloop)
  refine ⟨_,b,hwhole,hcursor,hI,hb,by omega,⟨?_⟩⟩
  exact StructuredSpace.compiled_halt_stack_bound hwhole 838 838 hall.bound

namespace TupleEnd

open OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram

/-- Return all borrowed current-head words before the attained-signature DFS
resumes. Ancestor frames and the emitted representatives are retained. -/
def cleanup : Code := QueryTupleInit.clearBank currentHeadPorts

noncomputable def cleaned (a : Data) : Data := QueryTupleInit.cleared currentHeadPorts a

def command : Code := .seq QueryTupleSum.command cleanup

def program := compiled command 852 851

noncomputable def result (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree output : List Bool) : Data :=
  cleaned (QueryTupleSum.result a rr modulus width degree output)

theorem result_pair (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree output : List Bool) :
    (result a rr modulus width degree output).stacks 851=output := by
  rw [result,cleaned,QueryTupleInit.cleared_stacks,ite_eq_right (by decide)]
  exact QueryTupleSum.result_output a rr modulus width degree output

theorem result_source (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree output : List Bool) :
    (result a rr modulus width degree output).stacks 852=[] := by
  rw [result,cleaned,QueryTupleInit.cleared_stacks,ite_eq_right (by decide)]
  exact QueryTupleSum.result_source a rr modulus width degree output

theorem result_current (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree output : List Bool) (i : Fin 896) (hi : i∈currentHeadPorts) :
    (result a rr modulus width degree output).stacks i=[] := by
  rw [result,cleaned,QueryTupleInit.cleared_stacks,ite_eq_left hi]

/-- This includes the persistent tuple ports836/837/842/845, node850,
correction masks857/858, accumulated jets863, and the full baseline869. -/
theorem result_high_frame (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree output : List Bool) (i : Fin 896)
    (hi : 128 ≤ i.val) (hc : i∉currentHeadPorts) (h851 : i≠851) (h852 : i≠852) :
    (result a rr modulus width degree output).stacks i=a.stacks i := by
  rw [result,cleaned,QueryTupleInit.cleared_stacks,ite_eq_right hc]
  apply QueryTupleSum.result_frame
  · intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  · intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  · intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  · intro h; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hi
  · exact h851
  · exact h852
  · intro h
    have hh := QueryTupleSum.scratchPorts_low h
    omega

theorem result_register_frame (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree output : List Bool) (i : Fin 40) (hi : 16 ≤ i.val) :
    (result a rr modulus width degree output).regs i=a.regs i := by
  unfold result cleaned QueryTupleInit.cleared
  rw [embedState_register_frame]
  · exact QueryTupleSum.result_register_frame a rr modulus width degree output i (by omega)
  · rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change j.val=i.val at hv
    have hjlt := j.isLt
    omega

theorem command_run (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (source seed : List (Product.Entry n (baseWidth p t) d))
    (hs : Good ∅ u J source) (hi : Good ∅ u J seed)
    (width degree : List Bool) (hd : degree.length=d) (hw : width.length=baseWidth p t)
    (a : Data) (B : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B)
    (hr : QueryTupleSum.Ready a M.bits width degree (Product.bytes seed) (Product.bytes source))
    (hcap : u*J*(2*(u+J+n)+2*(d*baseWidth p t)+2) ≤ B) :
    let output := Normalize.run p t M cache source seed
    ∃ steps rr, Eval command steps a (result a rr M.bits width degree (Product.bytes output)) ∧
      Good ∅ u J output ∧
      (∀ i, ((result a rr M.bits width degree (Product.bytes output)).stacks i).length ≤ B) ∧
      steps+1 ≤ QueryTupleSum.budget n (baseWidth p t) d u J B+16*B+25 := by
  dsimp only
  obtain ⟨steps,rr,ht,he,hg⟩ := QueryTupleSum.command_eval p t M cache source seed hs hi
    width degree hd hw a B ha hr
  have hb := QueryTupleSum.result_bound_of_good _ hg a rr M.bits width degree
    (Product.bytes seed) (Product.bytes source) hr B ha hcap
  have hc := QueryTupleInit.clear_eval currentHeadPorts
    (QueryTupleSum.result a rr M.bits width degree (Product.bytes (Normalize.run p t M cache source seed)))
  have hcost := QueryTupleInit.clearCost_le currentHeadPorts _ B hb
  rw [show currentHeadPorts.length=8 by rfl] at hcost
  refine ⟨_,rr,he.seq hc,hg,QueryTupleInit.cleared_bound currentHeadPorts _ B hb,?_⟩
  omega

/-- The same measured tail consumes the completed product and restores all
borrowed tuple words. Its local time is polynomial and does not depend on the
number of previously emitted signatures. -/
theorem run_space (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (source seed : List (Product.Entry n (baseWidth p t) d))
    (hs : Good ∅ u J source) (hi : Good ∅ u J seed)
    (width degree : List Bool) (hd : degree.length=d) (hw : width.length=baseWidth p t)
    (a : Data) (B : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B)
    (hr : QueryTupleSum.Ready a M.bits width degree (Product.bytes seed) (Product.bytes source))
    (hcap : u*J*(2*(u+J+n)+2*(d*baseWidth p t)+2) ≤ B) :
    let output := Normalize.run p t M cache source seed
    let cost := QueryTupleSum.budget n (baseWidth p t) d u J B+16*B+25
    ∃ steps rr, Trace program steps (a.withPC (some program.entry))
      ((result a rr M.bits width degree (Product.bytes output)).withPC none) ∧
      Good ∅ u J output ∧
      (∀ i, ((result a rr M.bits width degree (Product.bytes output)).stacks i).length ≤ B) ∧
      steps ≤ cost ∧
      ∀ q z, q ≤ steps → Trace program q (a.withPC (some program.entry)) z →
        ∀ i, (z.stacks i).length ≤ 896*B+cost := by
  dsimp only
  obtain ⟨steps,rr,he,hg,hb,ht⟩ := command_run p t M cache source seed hs hi
    width degree hd hw a B ha hr hcap
  refine ⟨steps+1,rr,compiled_halt_trace he 852 851,hg,hb,ht,?_⟩
  have hin : dataBits (a.withPC (some program.entry)) ≤ 896*B :=
    StreamResources.dataBits_le_mul _ ha
  intro q z hq hz i
  exact StructuredSpace.local_stack_bound program hin q z (hq.trans ht) hz i

end TupleEnd

namespace PairStart

theorem encoded_outer {m : ℕ} (E U : Finset (Fin m)) :
    (DifferencePairs.encodePair E U).map Option.isSome=List.ofFn (fun i => decide (i∈E)) := by
  rw [DifferencePairs.encodePair,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  by_cases hi : i∈E <;> simp [hi]

theorem encoded_inner {m : ℕ} (E U : Finset (Fin m)) (hU : U⊆E) :
    (DifferencePairs.encodePair E U).map (fun x => x.getD false)=
      List.ofFn (fun i => decide (i∈U)) := by
  rw [DifferencePairs.encodePair,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  by_cases hi : i∈E
  · simp [hi]
  · have hu : i∉U := fun h => hi (hU h)
    simp [hi,hu]

theorem expanded_support_word {n : ℕ} (H : Finset (Fin n))
    (E : Finset (Fin (n-H.card))) :
    List.ofFn (HighIncidenceProgram.freeFill H (fun i => decide (i∈E)))=
      OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.supportBits
        ⟨E.image (fun i => (HighIncidenceProgram.freeOrder H i).val)⟩ := by
  apply congrArg List.ofFn
  funext i
  exact HighIncidenceProgram.freeFill_support H E i

/-- A new finite-difference pair begins with the actual zero dictionary and
the current reversed free-coordinate masks are expanded to ambient masks.
Neither a support family nor a tuple family is stored by this command. -/
def command : Code := .seq (clearWord 851) PairNativeSetup.expandCaller

def program := compiled command 834 857

theorem command_run {n : ℕ} (a : Data) (H : Finset (Fin n))
    (E U : Fin (n-H.card) → Bool) (B : ℕ)
    (hm : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (he : a.stacks 834=(List.ofFn E).reverse)
    (hu : a.stacks 835=(List.ofFn U).reverse)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∃ steps b, Eval command steps a b ∧
      b.stacks 851=[] ∧
      b.stacks 858=List.ofFn (HighIncidenceProgram.freeFill H E) ∧
      b.stacks 857=List.ofFn (HighIncidenceProgram.freeFill H U) ∧
      (∀ i∈PairNativeSetup.scratch,b.stacks i=[]) ∧
      (∀ i, i∉PairNativeSetup.scratch → i≠851 → i≠857 → i≠858 →
        b.stacks i=a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ B) ∧
      steps+1 ≤ 300*(B+n+1)+2*B+5 := by
  let start := clearState 851 a
  have hb : ∀ i, (start.stacks i).length ≤ B := by
    intro i
    by_cases hi : i=851
    · subst i
      simp [start,clearState]
    · simpa [start,clearState,hi] using ha i
  have hf (i : Fin 896) (hi : i≠851) : start.stacks i=a.stacks i := by
    simp [start,clearState,hi]
  obtain ⟨steps,b,ht,hr,hE,hU,hs,hframe,hbound⟩ :=
    PairNativeSetup.expandCaller_eval start H E U B
      ((hf 338 (by decide)).trans hm) ((hf 834 (by decide)).trans he)
      ((hf 835 (by decide)).trans hu) hb
  refine ⟨_,b,(clearWord_eval 851 a).seq hr,?_,hE,hU,hs,?_,hbound,?_⟩
  · rw [hframe 851 (by decide) (by decide) (by decide)]
    simp [start,clearState]
  · intro i hscratch h851 h857 h858
    exact (hframe i hscratch h857 h858).trans (hf i h851)
  · have h851 := ha 851
    omega

theorem run_space {n : ℕ} (a : Data) (H : Finset (Fin n))
    (E U : Fin (n-H.card) → Bool) (B : ℕ)
    (hm : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (he : a.stacks 834=(List.ofFn E).reverse)
    (hu : a.stacks 835=(List.ofFn U).reverse)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∃ (steps : ℕ) (b : Data), Trace program steps (a.withPC (some program.entry)) (b.withPC none) ∧
      b.stacks 851=[] ∧
      b.stacks 858=List.ofFn (HighIncidenceProgram.freeFill H E) ∧
      b.stacks 857=List.ofFn (HighIncidenceProgram.freeFill H U) ∧
      (∀ i∈PairNativeSetup.scratch,b.stacks i=[]) ∧
      (∀ i, i∉PairNativeSetup.scratch → i≠851 → i≠857 → i≠858 →
        b.stacks i=a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ B) ∧
      steps ≤ 300*(B+n+1)+2*B+5 ∧
      ∀ q z, q ≤ steps → Trace program q (a.withPC (some program.entry)) z →
        ∀ i, (z.stacks i).length ≤ 896*B+(300*(B+n+1)+2*B+5) := by
  obtain ⟨steps,b,hr,hzero,hE,hU,hs,hframe,hbound,ht⟩ := command_run a H E U B hm he hu ha
  refine ⟨steps+1,b,compiled_halt_trace hr 834 857,hzero,hE,hU,hs,hframe,hbound,ht,?_⟩
  have hin : dataBits (a.withPC (some program.entry)) ≤ 896*B :=
    StreamResources.dataBits_le_mul _ ha
  intro q z hq hz i
  exact StructuredSpace.local_stack_bound program hin q z (hq.trans ht) hz i

/-- This instance starts from the exact masks emitted by the ternary pair
DFS. Its outputs are the transported supports used by the actual native
factor correction and head predicate; no high coordinate enters either set. -/
theorem support_command_run {n : ℕ} (a : Data) (H : Finset (Fin n))
    (E U : Finset (Fin (n-H.card))) (hU : U⊆E) (B : ℕ)
    (hm : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (he : a.stacks 834=((DifferencePairs.encodePair E U).map Option.isSome).reverse)
    (hu : a.stacks 835=((DifferencePairs.encodePair E U).map (fun x => x.getD false)).reverse)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∃ steps b, Eval command steps a b ∧ b.stacks 851=[] ∧
      b.stacks 858=OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.supportBits
        ⟨E.image (fun i => (HighIncidenceProgram.freeOrder H i).val)⟩ ∧
      b.stacks 857=OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafWeightProgram.supportBits
        ⟨U.image (fun i => (HighIncidenceProgram.freeOrder H i).val)⟩ ∧
      (∀ i∈PairNativeSetup.scratch,b.stacks i=[]) ∧
      (∀ i, i∉PairNativeSetup.scratch → i≠851 → i≠857 → i≠858 →
        b.stacks i=a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ B) ∧
      steps+1 ≤ 300*(B+n+1)+2*B+5 := by
  rw [encoded_outer] at he
  rw [encoded_inner E U hU] at hu
  simpa only [expanded_support_word] using
    command_run a H (fun i => decide (i∈E)) (fun i => decide (i∈U)) B hm he hu ha

end PairStart

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution
