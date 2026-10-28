import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeAppendSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramCountPrepare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgramNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramConstantsModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingNodeProgramModel
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

/-! The actual streamed-jet handoff, scratch preparation, and canonical count
reconstruction. Readiness is derived from the produced ring masters. The target
and jets are mathematical properties of the actual query output; no evaluator
or readiness service is accepted by the produced-input theorem. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing OAI.Algorithms.SubexponentialSAT.SqrtLog
open DensePolynomialProgram LeafProgram
open LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Data := State 40 896
abbrev CoreData := State 40 768

def ringPorts : List (Fin 320) := [194,201,202,203,204,207,209,211,212,243,280]

def coreCommand : Cmd 40 768 :=
  .seq Count.Prepare.command ReconstructionNative.command

def prepareBudget (B : ℕ) : ℕ :=
  2*B+6+3*Count.Prepare.ports.length+2*Count.Prepare.ports.length*B

def coreBudget (B S : ℕ) : ℕ := prepareBudget B+ReconstructionNative.budget S

def command : Cmd 40 896 :=
  .seq NodeAppendSpace.handoff
    (liftCommand coreCommand 256 323 id (Fin.castAdd 128))

def program := compiled command 863 323

def budget (B S : ℕ) : ℕ := 8*B+10+coreBudget B S

/-- All exponents are fixed before the input and before the produced jets. -/
theorem budget_polynomial (B S : ℕ) :
    budget B S ≤ (2400*(ReconstructionProgram.Native.costConstant+1)^4+
      5*Count.Prepare.ports.length+39628)*(B+S+1)^96 := by
  have hp : 0 < B+S+1 := by omega
  have hlinear : B+1 ≤ (B+S+1)^96 := by
    have h := Nat.pow_le_pow_right hp (show 1 ≤ 96 by decide)
    simp only [pow_one] at h
    omega
  have hrec := ReconstructionNative.budget_polynomial S
  have hpow : (S+1)^96 ≤ (B+S+1)^96 := Nat.pow_le_pow_left (by omega) 96
  have hrec' := hrec.trans (Nat.mul_le_mul_left
    (2400*(ReconstructionProgram.Native.costConstant+1)^4+39608) hpow)
  have hprep : 8*B+10+prepareBudget B ≤
      (5*Count.Prepare.ports.length+20)*(B+1) := by
    unfold prepareBudget
    nlinarith only [Nat.zero_le (Count.Prepare.ports.length*B)]
  have hprep' := hprep.trans (Nat.mul_le_mul_left
    (5*Count.Prepare.ports.length+20) hlinear)
  unfold budget coreBudget
  calc
    _ = (8*B+10+prepareBudget B)+ReconstructionNative.budget S := by omega
    _ ≤ (5*Count.Prepare.ports.length+20)*(B+S+1)^96 +
        (2400*(ReconstructionProgram.Native.costConstant+1)^4+39608)*(B+S+1)^96 :=
      Nat.add_le_add hprep' hrec'
    _ = _ := by
      rw [← Nat.add_mul]
      apply congrArg (fun x : ℕ => x*(B+S+1)^96)
      omega

/-- Preparation only clears words, including all of its arithmetic temporaries. -/
theorem prepare_bound (a : CoreData) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((Count.Prepare.output a).stacks i).length ≤ B := by
  intro i
  by_cases hi : i ∈ Count.Prepare.ports
  · simp [Count.Prepare.output, BankRoutines.clearBankStacks, hi]
  by_cases hs : i = 699
  · subst i
    simp [Count.Prepare.output, BankRoutines.clearBankStacks, hi]
  simpa [Count.Prepare.output, BankRoutines.clearBankStacks, hi, hs] using ha i

theorem prepare_budget (a : CoreData) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) : Count.Prepare.budget a ≤ prepareBudget B := by
  have hsum : (Count.Prepare.ports.map (fun i => (a.stacks i).length)).sum ≤
      Count.Prepare.ports.length * B := by
    have h := List.sum_le_length_nsmul
      (Count.Prepare.ports.map (fun i => (a.stacks i).length)) B (by
        intro x hx
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
        exact ha i)
    simpa only [List.length_map, smul_eq_mul] using h
  have hscratch := ha 699
  unfold Count.Prepare.budget prepareBudget
  simp only [Nat.mul_assoc]
  omega

/-- Readiness is proved from producer bytes after the actual scratch cleanup.
This is the proof underlying `PreparedRecovery.ofProduced`, applied directly so
that the old materialized query program is not an executable dependency. -/
private theorem core_execution (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (a : CoreData)
    (hframe : ∀ i ∈ ringPorts, a.stacks (Count.crtStacks i) = e.stacks (i.castAdd 320))
    (hQ : 0 < m.val 21) (hJ : 0 < m.val 42)
    (hfield : m.val 21 < 3^(m.val 34))
    (hexponent : (Circuit.result Serialization.code m).val 44 = 3^(m.val 34)-2)
    (jets : Fin (m.val 21) → CRTLocalProgram.Model.Poly
      (baseWidth 3 (m.val 33)) (m.val 34) (m.val 42))
    (hnodes : a.stacks 256 = (List.finRange (m.val 21)).flatMap
      (fun i => RingProgram.flat (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1))))
    (hjets : a.stacks 265 = (List.finRange (m.val 21)).flatMap (fun i => Fixed.encode (jets i)))
    (target : Polynomial ((IrreducibleSearch.data hd).O (m.val 33)))
    (hdegree : target.natDegree < m.val 21 * m.val 42)
    (hhas : Reconstruction.HasJets
      (RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache)
      (fun i : Fin (m.val 21) => RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1))
      (m.val 42) (fun i => (jets i).1) target)
    (count multiplicity ambient : ℕ) (hcount : count ≤ multiplicity*2^ambient)
    (hlarge : multiplicity*2^ambient < 3^(m.val 33))
    (hconstant : target.eval 0 = (count : (IrreducibleSearch.data hd).O (m.val 33)))
    (B S : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B)
    (hQsize : m.val 21 ≤ S) (hJsize : m.val 42 ≤ S) (htsize : m.val 33 ≤ S)
    (hdsize : m.val 34 ≤ S) (hqsize : 3^(m.val 34) ≤ S)
    (hmodsize : (a.stacks 194).length ≤ S) (hwidthsize : (a.stacks 202).length ≤ S)
    (hcountsize : (DisjointReuse.binaryNat count).length ≤ B) :
    ∃ steps out, steps+1 ≤ coreBudget B S ∧ Eval coreCommand steps a out ∧
      out.stacks = Function.update (Count.Prepare.output a).stacks 323
        (DisjointReuse.binaryNat count) ∧
      (∀ i, (out.stacks i).length ≤ B) ∧
      (∀ i : Fin 40, 16 ≤ i.val → out.regs i = a.regs i) := by
  let : NeZero (m.val 21) := ⟨Nat.ne_of_gt hQ⟩
  generalize hprepared : Count.Prepare.output a = prepared
  let input := Count.project prepared
  have preserved (i : Fin 768)
      (hi : i ∈ ([194,201,202,203,204,207,209,211,212,243,256,265,280] : List (Fin 768))) :
      prepared.stacks i = a.stacks i := by
    have h := Count.Prepare.output_input a i hi
    rw [hprepared] at h
    exact h
  have cleaned (i : Fin 320) (hi : i ∈ ReconstructionProgram.NativeState.cleanPorts) :
      input.stacks i = [] := by
    have h := Count.Prepare.output_clean a i hi
    rw [hprepared] at h
    exact h
  have readers (i : Fin 768)
      (hi : i ∈ ([323,324,325,326,327,328,329] : List (Fin 768))) :
      prepared.stacks i = [] := by
    have h := Count.Prepare.output_reader a i hi
    rw [hprepared] at h
    exact h
  have fw (i : Fin 320) (hi : i ∈ ringPorts) : input.stacks i = e.stacks (i.castAdd 320) := by
    change prepared.stacks (Count.crtStacks i) = _
    rw [preserved]
    · exact hframe i hi
    · simp only [ringPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have hm := (fw 194 (by simp [ringPorts])).trans hp.caches.modulus
  have hw := congrArg List.length (fw 202 (by simp [ringPorts])) |>.trans hp.caches.width
  have hz := (fw 203 (by simp [ringPorts])).trans hp.caches.scalarZero
  have htable := (fw 201 (by simp [ringPorts])).trans hp.native.table
  have hdw := congrArg List.length (fw 204 (by simp [ringPorts])) |>.trans hp.caches.degree
  have hzero := (fw 280 (by simp [ringPorts])).trans hp.caches.fullZero_model
  have hlen := congrArg List.length (fw 280 (by simp [ringPorts])) |>.trans hp.native.fullZeroLength
  have hclean (i : Fin 320) (hi : i ∈ ReconstructionProgram.InputReady.emptyPorts) :
      input.stacks i = [] := by
    have h := Count.Prepare.output_arithmetic_clean a i hi
    rw [hprepared] at h
    exact h
  have hscalar := ReconstructionProgram.InputReady.nativeReady 3 _ M cache _ input
    hclean hm hw hz htable hdw
  have hpoly := ReconstructionProgram.InputReady.polynomialReady 3 _ M cache _ input
    hclean hm hw hz htable hdw hlen
  have hmod : (input.stacks 194).length ≤ S := by
    change (prepared.stacks 194).length ≤ S
    rw [preserved 194 (by decide)]
    exact hmodsize
  have hwidth : (input.stacks 202).length ≤ S := by
    change (prepared.stacks 202).length ≤ S
    rw [preserved 202 (by decide)]
    exact hwidthsize
  obtain ⟨steps, out, hsteps, he, _, hs, hr, _⟩ :=
    ReconstructionNative.run_space (m.val 33) ht hd (IrreducibleSearch.data hd) M cache
      hp.caches.canonical hp.zero_bytes (m.val 42) hJ (Nat.mul_pos ht (by omega))
      (fun i : Fin (m.val 21) => RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1))
      jets (Constants.constantCode (m.val 34) cache.minusOne cache.zero)
      (Constants.minusOne_decode _ ht hd _ M cache) input hscalar (input.stacks 202)
      (ReconstructionProgram.InputReady.lowFrame input) hpoly cleaned
      hzero ((fw 207 (by simp [ringPorts])).trans hp.caches.fullOne_model)
      ((fw 211 (by simp [ringPorts])).trans
        (hp.caches.fullMinusOne.trans (Constants.constantCode_flat _ _ _).symm))
      ((fw 243 (by simp [ringPorts])).trans hp.jetOrder)
      ((preserved 256 (by decide)).trans hnodes)
      ((preserved 265 (by decide)).trans hjets)
      ((congrArg List.length ((fw 209 (by simp [ringPorts])).trans hp.exponent)).trans
        (by simp only [List.length_replicate, hexponent]))
      ((congrArg List.length ((fw 212 (by simp [ringPorts])).trans hp.caches.precision)).trans
        (by simp only [List.length_replicate]))
      (RingNodeProgram.generated_residue_injective _ ht hd _ M cache _ hfield)
      target hdegree hhas count multiplicity ambient hcount hlarge hconstant
      S hQsize hJsize htsize hdsize hqsize hmod hwidth prepared
      (hm ▸ M.value) hw readers
  have hstart : Count.install prepared input = prepared := Count.install_project _
  rw [hstart] at he hs hr
  have hprepare := Count.Prepare.command_eval a
  rw [hprepared] at hprepare
  have hbound := prepare_bound a B ha
  rw [hprepared] at hbound
  refine ⟨Count.Prepare.budget a+steps, out, ?_, hprepare.seq he, hs, ?_, ?_⟩
  · have hp := prepare_budget a B ha
    unfold coreBudget
    omega
  · intro i
    rw [hs]
    by_cases hi : i = 323
    · subst i
      simpa using hcountsize
    simpa only [Function.update_of_ne hi] using hbound i
  · intro i hi
    have hf := Count.Prepare.output_register_frame a i (by omega)
    rw [hprepared] at hf
    exact (hr i hi).trans hf

/-- The unchanged upper bank is retained through the lifted recovery call. -/
theorem outside_core (i : Fin 896) (hi : 768 ≤ i.val) :
    ¬ ∃ j : Fin 768, j.castAdd 128 = i := by
  rintro ⟨j, hj⟩
  have hv := congrArg Fin.val hj
  change j.val = i.val at hv
  omega

/-- The two accumulated counts lie above the native arithmetic bank and
below the canonical reader temporaries. Membership is proved structurally. -/
theorem collector_outside (i : Fin 768) (hlo : 320 ≤ i.val) (hhi : i.val < 323) :
    i ∉ Count.Prepare.ports := by
  intro hi
  simp only [Count.Prepare.ports, List.mem_dedup, List.mem_append] at hi
  rcases hi with hi | hi
  · obtain ⟨j, _, hj⟩ := List.mem_map.mp hi
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with h|h|h|h|h|h|h <;> subst i <;> simp at hhi

/-- Full concrete recovery from the actual ring producer and node/jet words.
The same run pays both transfers, real scratch clearing, Hermite arithmetic,
canonical whole-word readback, and the relocated callee halt. -/
-- Actual ring and node masters needed by the next high-assignment query.
def retainedPorts : List (Fin 896) :=
  [194,201,202,203,204,207,209,211,212,243,256,280,281,300]

private theorem retained_extra_outside (i : Fin 768)
    (hi : i ∈ ([281,300] : List (Fin 768))) : i ∉ Count.Prepare.ports := by
  intro hp
  simp only [Count.Prepare.ports, List.mem_dedup, List.map_append, List.mem_append] at hp
  rcases hp with (hp | hp) | hp
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl
    · exact (by decide : (281 : Fin 768) ∉ ReconstructionProgram.NativeState.cleanPorts.map Count.crtStacks) hp
    · exact (by decide : (300 : Fin 768) ∉ ReconstructionProgram.NativeState.cleanPorts.map Count.crtStacks) hp
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl
    · exact (by decide : (281 : Fin 768) ∉ ReconstructionProgram.InputReady.emptyPorts.map Count.crtStacks) hp
    · exact (by decide : (300 : Fin 768) ∉ ReconstructionProgram.InputReady.emptyPorts.map Count.crtStacks) hp
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl <;> simp at hp

theorem run_space_with_full_frame (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (a : Data) (hscratch : a.stacks 89 = [])
    (hframe : ∀ i ∈ ringPorts,
      a.stacks (i.castAdd 576) = e.stacks (i.castAdd 320))
    (hnodes : a.stacks 256 = e.stacks 256)
    (hQ : 0 < m.val 21) (hJ : 0 < m.val 42)
    (hfield : m.val 21 < 3^(m.val 34))
    (hexponent : (Circuit.result Serialization.code m).val 44 = 3^(m.val 34)-2)
    (jets : Fin (m.val 21) → CRTLocalProgram.Model.Poly
      (baseWidth 3 (m.val 33)) (m.val 34) (m.val 42))
    (hjets : a.stacks 863 = (List.finRange (m.val 21)).flatMap
      (fun i => Fixed.encode (jets i)))
    (target : Polynomial ((IrreducibleSearch.data hd).O (m.val 33)))
    (hdegree : target.natDegree < m.val 21 * m.val 42)
    (hhas : Reconstruction.HasJets
      (RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache)
      (fun i : Fin (m.val 21) => RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1))
      (m.val 42) (fun i => (jets i).1) target)
    (count multiplicity ambient : ℕ) (hcount : count ≤ multiplicity*2^ambient)
    (hlarge : multiplicity*2^ambient < 3^(m.val 33))
    (hconstant : target.eval 0 = (count : (IrreducibleSearch.data hd).O (m.val 33)))
    (B S : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B)
    (hQsize : m.val 21 ≤ S) (hJsize : m.val 42 ≤ S) (htsize : m.val 33 ≤ S)
    (hdsize : m.val 34 ≤ S) (hqsize : 3^(m.val 34) ≤ S)
    (hmodsize : (a.stacks 194).length ≤ S) (hwidthsize : (a.stacks 202).length ≤ S)
    (hcountsize : (DisjointReuse.binaryNat count).length ≤ B) :
    ∃ steps out, steps+1 ≤ budget B S ∧ Eval command steps a out ∧
      Trace program (steps+1) (a.withPC (some program.entry)) (out.withPC none) ∧
      out.stacks 323 = DisjointReuse.binaryNat count ∧
      out.stacks 863 = [] ∧
      (∀ i, (out.stacks i).length ≤ B) ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 863 → out.stacks i = a.stacks i) ∧
      out.stacks 320 = a.stacks 320 ∧ out.stacks 322 = a.stacks 322 ∧
      (∀ i : Fin 896, 330 ≤ i.val → i.val < 768 → i ≠ 699 → out.stacks i = a.stacks i) ∧
      (∀ i : Fin 896, i ∈ retainedPorts → out.stacks i = a.stacks i) ∧
      (∀ i : Fin 40, 16 ≤ i.val → out.regs i = a.regs i) ∧
      ∀ q z, q ≤ steps+1 → Trace program q (a.withPC (some program.entry)) z →
        ∀ i, (z.stacks i).length ≤ 896*B+budget B S := by
  let middle := NodeAppendSpace.handoffResult a
  let input : CoreData := projectState id (Fin.castAdd 128) middle
  have hmiddle : middle.stacks = Function.update (Function.update
      (Function.update a.stacks 265 (a.stacks 863)) 863 []) 89 [] :=
    NodeAppendSpace.handoffResult_stacks a hscratch
  have hinput (i : Fin 768) : input.stacks i = middle.stacks (i.castAdd 128) := rfl
  have hmiddleFrame (i : Fin 896) (h89 : i ≠ 89) (h863 : i ≠ 863) (h265 : i ≠ 265) :
      middle.stacks i = a.stacks i := by
    rw [hmiddle]
    simp only [Function.update_of_ne h89, Function.update_of_ne h863,
      Function.update_of_ne h265]
  have hring : ∀ i ∈ ringPorts, input.stacks (Count.crtStacks i) = e.stacks (i.castAdd 320) := by
    intro i hi
    rw [hinput]
    have hh : i ∈ ([194,201,202,203,204,207,209,211,212,243,280] : List (Fin 320)) := hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hh
    rcases hh with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      rw [hmiddleFrame _ (by decide) (by decide) (by decide)] <;> exact hframe _ hi
  have hnode : input.stacks 256 = (List.finRange (m.val 21)).flatMap
      (fun i => RingProgram.flat (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1))) := by
    rw [hinput, hmiddleFrame _ (by decide) (by decide) (by decide)]
    change a.stacks 256 = _
    rw [hnodes, hp.flatNodes]
    simp only [LeafRingSetupProgram.nodeWords, List.map_map, List.flatMap_def, Function.comp_def]
  have hjet : input.stacks 265 = (List.finRange (m.val 21)).flatMap
      (fun i => Fixed.encode (jets i)) := by
    rw [hinput, hmiddle]
    simpa using hjets
  have hmB := NodeAppendSpace.handoffResult_bound a hscratch B ha
  have hiB (i : Fin 768) : (input.stacks i).length ≤ B := hmB (i.castAdd 128)
  have hmS : (input.stacks 194).length ≤ S := by
    rw [hinput, hmiddleFrame _ (by decide) (by decide) (by decide)]
    exact hmodsize
  have hwS : (input.stacks 202).length ≤ S := by
    rw [hinput, hmiddleFrame _ (by decide) (by decide) (by decide)]
    exact hwidthsize
  obtain ⟨nk, b, hk, he, hb, hbB, hr⟩ := core_execution m ht hd M cache half e hp input hring
    hQ hJ hfield hexponent jets hnode hjet target hdegree hhas count multiplicity ambient
    hcount hlarge hconstant B S hiB hQsize hJsize htsize hdsize hqsize hmS hwS hcountsize
  let out := embedState id (Fin.castAdd 128) middle b
  have hc : Eval (liftCommand coreCommand 256 323 id (Fin.castAdd 128)) (nk+1)
      middle out := eval_liftCommand_from_state coreCommand 256 323 id (Fin.castAdd 128)
        middle Function.injective_id (Fin.castAdd_injective 768 128) he
  have heval : Eval command (NodeAppendSpace.handoffCost a+(nk+1)) a out :=
    (NodeAppendSpace.handoff_eval a hscratch).seq hc
  have hcost : NodeAppendSpace.handoffCost a+(nk+1)+1 ≤ budget B S := by
    have hh := (NodeAppendSpace.handoff_run_space a hscratch B ha).2.1
    unfold budget
    omega
  have hout (i : Fin 768) : out.stacks (i.castAdd 128) = b.stacks i :=
    embedState_stack id (Fin.castAdd 128) middle b (Fin.castAdd_injective 768 128) i
  have houter (i : Fin 896) (hi : 768 ≤ i.val) : out.stacks i = middle.stacks i :=
    embedState_stack_frame id (Fin.castAdd 128) middle b i (outside_core i hi)
  have hlocalFrame (i : Fin 768) (hp : i ∉ Count.Prepare.ports) (hs : i ≠ 699)
      (hc : i ≠ 323) (h89 : i.castAdd 128 ≠ 89) (h265 : i.castAdd 128 ≠ 265) :
      out.stacks (i.castAdd 128) = a.stacks (i.castAdd 128) := by
    rw [hout, hb, Function.update_of_ne hc, Count.Prepare.output_frame input i hp hs,
      hinput, hmiddleFrame _ h89 (by intro h; have := congrArg Fin.val h; simp at this; omega) h265]
  refine ⟨_, out, hcost, heval, compiled_halt_trace heval 863 323, ?_, ?_, ?_, ?_,
    hlocalFrame 320 (collector_outside 320 (by decide) (by decide)) (by decide) (by decide) (by decide) (by decide),
    hlocalFrame 322 (collector_outside 322 (by decide) (by decide)) (by decide) (by decide) (by decide) (by decide), ?_, ?_, ?_, ?_⟩
  · rw [show (323 : Fin 896) = (323 : Fin 768).castAdd 128 from rfl, hout, hb]
    rfl
  · rw [houter 863 (by decide), hmiddle]
    simp
  · intro i
    by_cases hi : i.val < 768
    · let j : Fin 768 := ⟨i.val, hi⟩
      have hj : j.castAdd 128 = i := Fin.ext rfl
      rw [← hj, hout]
      exact hbB j
    · rw [houter i (by omega)]
      exact hmB i
  · intro i hi h863
    rw [houter i hi, hmiddleFrame i (by intro h; subst i; simp at hi) h863
      (by intro h; subst i; simp at hi)]
  · intro i hi hlo h699
    let j : Fin 768 := ⟨i.val, hlo⟩
    have hj : j.castAdd 128 = i := Fin.ext rfl
    rw [← hj]
    apply hlocalFrame j
    · intro h
      have hh := Count.Prepare.ports_lt j h
      change i.val < 330 at hh
      omega
    · intro h
      apply h699
      apply Fin.ext
      exact congrArg (fun q : Fin 768 => q.val) h
    all_goals intro h; have hh := congrArg Fin.val h; norm_num [j, Fin.castAdd, Fin.coe_ofNat_eq_mod] at hh; omega
  · intro i hi
    simp only [retainedPorts, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact hlocalFrame 194 (fun h => (List.disjoint_left.mp Count.Prepare.inputs_disjoint) h (by decide)) (by decide) (by decide) (by decide) (by decide)
    · exact hlocalFrame 201 (fun h => (List.disjoint_left.mp Count.Prepare.inputs_disjoint) h (by decide)) (by decide) (by decide) (by decide) (by decide)
    · exact hlocalFrame 202 (fun h => (List.disjoint_left.mp Count.Prepare.inputs_disjoint) h (by decide)) (by decide) (by decide) (by decide) (by decide)
    · exact hlocalFrame 203 (fun h => (List.disjoint_left.mp Count.Prepare.inputs_disjoint) h (by decide)) (by decide) (by decide) (by decide) (by decide)
    · exact hlocalFrame 204 (fun h => (List.disjoint_left.mp Count.Prepare.inputs_disjoint) h (by decide)) (by decide) (by decide) (by decide) (by decide)
    · exact hlocalFrame 207 (fun h => (List.disjoint_left.mp Count.Prepare.inputs_disjoint) h (by decide)) (by decide) (by decide) (by decide) (by decide)
    · exact hlocalFrame 209 (fun h => (List.disjoint_left.mp Count.Prepare.inputs_disjoint) h (by decide)) (by decide) (by decide) (by decide) (by decide)
    · exact hlocalFrame 211 (fun h => (List.disjoint_left.mp Count.Prepare.inputs_disjoint) h (by decide)) (by decide) (by decide) (by decide) (by decide)
    · exact hlocalFrame 212 (fun h => (List.disjoint_left.mp Count.Prepare.inputs_disjoint) h (by decide)) (by decide) (by decide) (by decide) (by decide)
    · exact hlocalFrame 243 (fun h => (List.disjoint_left.mp Count.Prepare.inputs_disjoint) h (by decide)) (by decide) (by decide) (by decide) (by decide)
    · exact hlocalFrame 256 (fun h => (List.disjoint_left.mp Count.Prepare.inputs_disjoint) h (by decide)) (by decide) (by decide) (by decide) (by decide)
    · exact hlocalFrame 280 (fun h => (List.disjoint_left.mp Count.Prepare.inputs_disjoint) h (by decide)) (by decide) (by decide) (by decide) (by decide)
    · exact hlocalFrame 281 (retained_extra_outside 281 (by decide)) (by decide) (by decide) (by decide) (by decide)
    · exact hlocalFrame 300 (retained_extra_outside 300 (by decide)) (by decide) (by decide) (by decide) (by decide)
  · intro i hi
    have hreg : out.regs i = b.regs i :=
      embedState_register id (Fin.castAdd 128) middle b Function.injective_id i
    rw [hreg, hr i hi]
    exact NodeAppendSpace.handoffResult_register_frame a i
      (by intro h; subst i; simp at hi) (by intro h; subst i; simp at hi)
  · have hbits := StreamResources.dataBits_le_mul (a.withPC (some program.entry)) ha
    intro q z hq hz i
    exact StructuredSpace.local_stack_bound program hbits q z (hq.trans hcost) hz i

theorem run_space_with_frame (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (a : Data) (hscratch : a.stacks 89 = [])
    (hframe : ∀ i ∈ ringPorts,
      a.stacks (i.castAdd 576) = e.stacks (i.castAdd 320))
    (hnodes : a.stacks 256 = e.stacks 256)
    (hQ : 0 < m.val 21) (hJ : 0 < m.val 42)
    (hfield : m.val 21 < 3^(m.val 34))
    (hexponent : (Circuit.result Serialization.code m).val 44 = 3^(m.val 34)-2)
    (jets : Fin (m.val 21) → CRTLocalProgram.Model.Poly
      (baseWidth 3 (m.val 33)) (m.val 34) (m.val 42))
    (hjets : a.stacks 863 = (List.finRange (m.val 21)).flatMap
      (fun i => Fixed.encode (jets i)))
    (target : Polynomial ((IrreducibleSearch.data hd).O (m.val 33)))
    (hdegree : target.natDegree < m.val 21 * m.val 42)
    (hhas : Reconstruction.HasJets
      (RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache)
      (fun i : Fin (m.val 21) => RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1))
      (m.val 42) (fun i => (jets i).1) target)
    (count multiplicity ambient : ℕ) (hcount : count ≤ multiplicity*2^ambient)
    (hlarge : multiplicity*2^ambient < 3^(m.val 33))
    (hconstant : target.eval 0 = (count : (IrreducibleSearch.data hd).O (m.val 33)))
    (B S : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B)
    (hQsize : m.val 21 ≤ S) (hJsize : m.val 42 ≤ S) (htsize : m.val 33 ≤ S)
    (hdsize : m.val 34 ≤ S) (hqsize : 3^(m.val 34) ≤ S)
    (hmodsize : (a.stacks 194).length ≤ S) (hwidthsize : (a.stacks 202).length ≤ S)
    (hcountsize : (DisjointReuse.binaryNat count).length ≤ B) :
    ∃ steps out, steps+1 ≤ budget B S ∧ Eval command steps a out ∧
      Trace program (steps+1) (a.withPC (some program.entry)) (out.withPC none) ∧
      out.stacks 323 = DisjointReuse.binaryNat count ∧
      out.stacks 863 = [] ∧
      (∀ i, (out.stacks i).length ≤ B) ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 863 → out.stacks i = a.stacks i) ∧
      out.stacks 320 = a.stacks 320 ∧ out.stacks 322 = a.stacks 322 ∧
      (∀ i : Fin 896, 330 ≤ i.val → i.val < 768 → i ≠ 699 → out.stacks i = a.stacks i) ∧
      (∀ i : Fin 40, 16 ≤ i.val → out.regs i = a.regs i) ∧
      ∀ q z, q ≤ steps+1 → Trace program q (a.withPC (some program.entry)) z →
        ∀ i, (z.stacks i).length ≤ 896*B+budget B S := by
  obtain ⟨steps, out, hcost, he, htrace, hword, hjetsOut, hbound, hupper,
    h320, h322, hmiddle, _, hregs, hprefix⟩ :=
    run_space_with_full_frame m ht hd M cache half e hp a hscratch hframe hnodes
      hQ hJ hfield hexponent jets hjets target hdegree hhas count multiplicity ambient
      hcount hlarge hconstant B S ha hQsize hJsize htsize hdsize hqsize hmodsize
      hwidthsize hcountsize
  exact ⟨steps, out, hcost, he, htrace, hword, hjetsOut, hbound, hupper,
    h320, h322, hmiddle, hregs, hprefix⟩

/-- Compatibility form of the recovery theorem. The stronger actual frame
in `run_space_with_frame` also retains the query's kept ports700/701/707/708/709. -/
theorem run_space (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (a : Data) (hscratch : a.stacks 89 = [])
    (hframe : ∀ i ∈ ringPorts,
      a.stacks (i.castAdd 576) = e.stacks (i.castAdd 320))
    (hnodes : a.stacks 256 = e.stacks 256)
    (hQ : 0 < m.val 21) (hJ : 0 < m.val 42)
    (hfield : m.val 21 < 3^(m.val 34))
    (hexponent : (Circuit.result Serialization.code m).val 44 = 3^(m.val 34)-2)
    (jets : Fin (m.val 21) → CRTLocalProgram.Model.Poly
      (baseWidth 3 (m.val 33)) (m.val 34) (m.val 42))
    (hjets : a.stacks 863 = (List.finRange (m.val 21)).flatMap
      (fun i => Fixed.encode (jets i)))
    (target : Polynomial ((IrreducibleSearch.data hd).O (m.val 33)))
    (hdegree : target.natDegree < m.val 21 * m.val 42)
    (hhas : Reconstruction.HasJets
      (RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache)
      (fun i : Fin (m.val 21) => RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1))
      (m.val 42) (fun i => (jets i).1) target)
    (count multiplicity ambient : ℕ) (hcount : count ≤ multiplicity*2^ambient)
    (hlarge : multiplicity*2^ambient < 3^(m.val 33))
    (hconstant : target.eval 0 = (count : (IrreducibleSearch.data hd).O (m.val 33)))
    (B S : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B)
    (hQsize : m.val 21 ≤ S) (hJsize : m.val 42 ≤ S) (htsize : m.val 33 ≤ S)
    (hdsize : m.val 34 ≤ S) (hqsize : 3^(m.val 34) ≤ S)
    (hmodsize : (a.stacks 194).length ≤ S) (hwidthsize : (a.stacks 202).length ≤ S)
    (hcountsize : (DisjointReuse.binaryNat count).length ≤ B) :
    ∃ steps out, steps+1 ≤ budget B S ∧ Eval command steps a out ∧
      Trace program (steps+1) (a.withPC (some program.entry)) (out.withPC none) ∧
      out.stacks 323 = DisjointReuse.binaryNat count ∧
      out.stacks 863 = [] ∧
      (∀ i, (out.stacks i).length ≤ B) ∧
      (∀ i : Fin 896, 768 ≤ i.val → i ≠ 863 → out.stacks i = a.stacks i) ∧
      out.stacks 320 = a.stacks 320 ∧ out.stacks 322 = a.stacks 322 ∧
      (∀ i : Fin 896, 730 ≤ i.val → i.val < 768 → out.stacks i = a.stacks i) ∧
      (∀ i : Fin 40, 16 ≤ i.val → out.regs i = a.regs i) ∧
      ∀ q z, q ≤ steps+1 → Trace program q (a.withPC (some program.entry)) z →
        ∀ i, (z.stacks i).length ≤ 896*B+budget B S := by
  obtain ⟨steps, out, hcost, he, htrace, hword, hjetsOut, hbound, hupper,
    h320, h322, hmiddle, hregs, hprefix⟩ :=
    run_space_with_frame m ht hd M cache half e hp a hscratch hframe hnodes
      hQ hJ hfield hexponent jets hjets target hdegree hhas count multiplicity ambient
      hcount hlarge hconstant B S ha hQsize hJsize htsize hdsize hqsize hmodsize
      hwidthsize hcountsize
  refine ⟨steps, out, hcost, he, htrace, hword, hjetsOut, hbound, hupper,
    h320, h322, ?_, hregs, hprefix⟩
  intro i hi hhi
  apply hmiddle i (by omega) hhi
  intro h
  subst i
  norm_num at hi

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction
