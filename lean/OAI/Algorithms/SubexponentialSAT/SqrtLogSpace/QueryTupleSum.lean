import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeAppendSpace

/-! Concrete unsigned tuple accumulation. The complete head product on852
is normalized into the pair accumulator851. Physical caches are copied from
retained masters and every native peripheral scratch word is paid for. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleSum

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

abbrev Data := State 40 896
abbrev Code := Cmd 40 896

def registers : Fin 8 → Fin 40 := Fin.castAdd 32

theorem registers_injective : Function.Injective registers := Fin.castAdd_injective _ _

def ports (i : Fin 28) : Fin 896 :=
  if i = 5 then 5 else if i = 12 then 12 else if i = 24 then 39
  else if i = 15 then 851 else if i = 27 then 852 else ⟨100+i.val, by omega⟩

private def portIndex (j : ℕ) : ℕ :=
  if j = 5 then 5 else if j = 12 then 12 else if j = 39 then 24
  else if j = 851 then 15 else if j = 852 then 27 else j-100

private theorem portIndex_ports (i : Fin 28) : portIndex (ports i).val = i.val := by
  fin_cases i <;> rfl

theorem ports_injective : Function.Injective ports := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun k : Fin 896 => portIndex k.val) h
  simpa only [portIndex_ports] using hv

def scratchIndices : List (Fin 28) :=
  (List.ofFn (fun i : Fin 28 => i)).filter (fun i => decide
    (i ≠ 5 ∧ i ≠ 12 ∧ i ≠ 24 ∧ i ≠ 15 ∧ i ≠ 27))

def scratchPorts : List (Fin 896) := scratchIndices.map ports

theorem mem_scratchIndices (i : Fin 28) : i ∈ scratchIndices ↔
    i ≠ 5 ∧ i ≠ 12 ∧ i ≠ 24 ∧ i ≠ 15 ∧ i ≠ 27 := by
  simp only [scratchIndices,List.mem_filter,List.mem_ofFn,exists_eq,
    decide_eq_true_eq,true_and]

theorem scratchPorts_low {i : Fin 896} (hi : i ∈ scratchPorts) :
    100 ≤ i.val ∧ i.val < 128 := by
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  obtain ⟨h5,h12,h24,h15,h27⟩ := (mem_scratchIndices j).mp hj
  simp only [ports,h5,h12,h24,h15,h27,ite_false]
  omega

theorem scratchPorts_length : scratchPorts.length = 23 := by decide

def prepare : Code := .seq NodeAppendSpace.prepare (NodeReadoutSpace.clearMany scratchPorts)

def prepared (a : Data) : Data :=
  NodeReadoutSpace.clearedMany scratchPorts (NodeAppendSpace.prepared a)

def prepareCost (a : Data) : ℕ := NodeAppendSpace.prepareCost a +
  NodeReadoutSpace.clearCost scratchPorts (NodeAppendSpace.prepared a)

theorem prepare_eval (a : Data) : Eval prepare (prepareCost a) a (prepared a) :=
  (NodeAppendSpace.prepare_eval a).seq
    (NodeReadoutSpace.clearMany_eval scratchPorts (NodeAppendSpace.prepared a))

theorem prepared_stacks (a : Data) (i : Fin 896) :
    (prepared a).stacks i = if i ∈ scratchPorts then [] else
      if i = 5 then a.stacks 194 else if i = 12 then a.stacks 202 else
      if i = 39 then a.stacks 204 else if i = 89 then [] else a.stacks i := by
  rw [prepared,NodeReadoutSpace.clearedMany_stack,NodeAppendSpace.prepared_stacks]

theorem prepared_bound (a : Data) (B : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((prepared a).stacks i).length ≤ B := by
  intro i
  rw [prepared_stacks]
  split_ifs <;> first | exact ha _ | exact Nat.zero_le _

theorem prepareCost_le (a : Data) (B : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B) :
    prepareCost a ≤ 75*B+96 := by
  have h1 := NodeAppendSpace.prepareCost_le a B ha
  have h2 := NodeReadoutSpace.clearCost_le scratchPorts (NodeAppendSpace.prepared a) B
    (NodeAppendSpace.prepared_bound a B ha)
  rw [scratchPorts_length] at h2
  unfold prepareCost
  omega

structure Ready (a : Data) (modulus width degree seed source : List Bool) : Prop where
  modulus : a.stacks 194 = modulus
  width : a.stacks 202 = width
  degree : a.stacks 204 = degree
  seed : a.stacks 851 = seed
  source : a.stacks 852 = source

theorem localState_stack (rr : Fin 8 → Bool)
    (modulus width degree seed source : List Bool) (i : Fin 28) :
    (Normalize.state rr modulus width degree seed source).stacks i =
      if i = 5 then modulus else if i = 12 then width else if i = 24 then degree
      else if i = 15 then seed else if i = 27 then source else [] := by
  fin_cases i <;> rfl

theorem prepared_eq (a : Data) (modulus width degree seed source : List Bool)
    (hr : Ready a modulus width degree seed source) :
    embedState registers ports (prepared a)
      (Normalize.state (fun i => (prepared a).regs (registers i))
        modulus width degree seed source) = prepared a := by
  apply embedState_eq_of_ports _ _ _ _ _ registers_injective ports_injective
  · intro i; rfl
  · intros; rfl
  · intro i
    rw [localState_stack]
    by_cases h5 : i = 5
    · subst i; simpa [ports,prepared_stacks,show (5 : Fin 896) ∉ scratchPorts from by decide]
        using hr.modulus
    by_cases h12 : i = 12
    · subst i; simpa [ports,prepared_stacks,show (12 : Fin 896) ∉ scratchPorts from by decide]
        using hr.width
    by_cases h24 : i = 24
    · subst i; simpa [ports,prepared_stacks,show (39 : Fin 896) ∉ scratchPorts from by decide]
        using hr.degree
    by_cases h15 : i = 15
    · subst i; simpa [ports,prepared_stacks,show (851 : Fin 896) ∉ scratchPorts from by decide]
        using hr.seed
    by_cases h27 : i = 27
    · subst i; simpa [ports,prepared_stacks,show (852 : Fin 896) ∉ scratchPorts from by decide]
        using hr.source
    have hm : ports i ∈ scratchPorts := List.mem_map.mpr
      ⟨i,(mem_scratchIndices i).mpr ⟨h5,h12,h24,h15,h27⟩,rfl⟩
    simp only [prepared_stacks, hm, ite_true, h5, h12, h24, h15, h27,
      ite_false]
  · intros; rfl

def command : Code := .seq prepare
  (.call (ProgramLinking.liftProgram Normalize.program registers ports))

def program := compiled command 852 851

noncomputable def result (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree output : List Bool) : Data :=
  embedState registers ports (prepared a) (Normalize.state rr modulus width degree output [])

theorem result_output (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree output : List Bool) :
    (result a rr modulus width degree output).stacks 851 = output := by
  change (embedState registers ports _ _).stacks (ports 15) = _
  rw [embedState_stack _ _ _ _ ports_injective]
  rfl

theorem result_source (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree output : List Bool) :
    (result a rr modulus width degree output).stacks 852 = [] := by
  change (embedState registers ports _ _).stacks (ports 27) = _
  rw [embedState_stack _ _ _ _ ports_injective]
  rfl

theorem result_cache (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree output : List Bool) :
    (result a rr modulus width degree output).stacks 5 = modulus ∧
      (result a rr modulus width degree output).stacks 12 = width ∧
      (result a rr modulus width degree output).stacks 39 = degree := by
  constructor
  · change (embedState registers ports _ _).stacks (ports 5) = _
    rw [embedState_stack _ _ _ _ ports_injective]
    rfl
  constructor
  · change (embedState registers ports _ _).stacks (ports 12) = _
    rw [embedState_stack _ _ _ _ ports_injective]
    rfl
  · change (embedState registers ports _ _).stacks (ports 24) = _
    rw [embedState_stack _ _ _ _ ports_injective]
    rfl

theorem result_copy_scratch (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree output : List Bool) :
    (result a rr modulus width degree output).stacks 89 = [] := by
  unfold result
  rw [embedState_stack_frame _ _ _ _ 89 (by decide),prepared_stacks]
  simp

theorem result_scratch (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree output : List Bool) (i : Fin 896) (hi : i ∈ scratchPorts) :
    (result a rr modulus width degree output).stacks i = [] := by
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  obtain ⟨h5,h12,h24,h15,h27⟩ := (mem_scratchIndices j).mp hj
  change (embedState registers ports _ _).stacks (ports j) = _
  rw [embedState_stack _ _ _ _ ports_injective,localState_stack]
  simp only [h5,h12,h24,h15,h27,ite_false]

theorem result_frame (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree output : List Bool) (i : Fin 896)
    (h5 : i ≠ 5) (h12 : i ≠ 12) (h39 : i ≠ 39) (h89 : i ≠ 89)
    (h851 : i ≠ 851) (h852 : i ≠ 852) (hs : i ∉ scratchPorts) :
    (result a rr modulus width degree output).stacks i = a.stacks i := by
  have hn : ¬ ∃ j, ports j = i := by
    rintro ⟨j,hj⟩
    by_cases hj5 : j = 5
    · subst j; exact h5 hj.symm
    by_cases hj12 : j = 12
    · subst j; exact h12 hj.symm
    by_cases hj24 : j = 24
    · subst j; exact h39 hj.symm
    by_cases hj15 : j = 15
    · subst j; exact h851 hj.symm
    by_cases hj27 : j = 27
    · subst j; exact h852 hj.symm
    exact hs (List.mem_map.mpr ⟨j,(mem_scratchIndices j).mpr
      ⟨hj5,hj12,hj24,hj15,hj27⟩,hj⟩)
  unfold result
  rw [embedState_stack_frame _ _ _ _ i hn,prepared_stacks]
  simp only [hs,h5,h12,h39,h89,ite_false]

theorem result_bound (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree seed source output : List Bool)
    (hr : Ready a modulus width degree seed source)
    (B : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B) (hout : output.length ≤ B) :
    ∀ i, ((result a rr modulus width degree output).stacks i).length ≤ B := by
  have hm : modulus.length ≤ B := by simpa only [hr.modulus] using ha 194
  have hw : width.length ≤ B := by simpa only [hr.width] using ha 202
  have hd : degree.length ≤ B := by simpa only [hr.degree] using ha 204
  intro i
  by_cases hi : ∃ j, ports j = i
  · obtain ⟨j,rfl⟩ := hi
    change ((embedState registers ports _ _).stacks (ports j)).length ≤ B
    rw [embedState_stack _ _ _ _ ports_injective,localState_stack]
    split_ifs <;> first | exact hm | exact hw | exact hd | exact hout | exact Nat.zero_le _
  · unfold result
    rw [embedState_stack_frame _ _ _ _ i hi]
    exact prepared_bound a B ha i

theorem result_register_frame (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree output : List Bool) (i : Fin 40) (hi : 8 ≤ i.val) :
    (result a rr modulus width degree output).regs i = a.regs i := by
  change (embedState registers ports _ _).regs i = _
  rw [embedState_register_frame]
  · rw [prepared,NodeReadoutSpace.clearedMany_register scratchPorts _ i
      (fun h => by subst i; simp at hi) (fun h => by subst i; simp at hi)]
    exact NodeAppendSpace.prepared_register_frame a i hi
  · rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    simp only [registers,Fin.val_castAdd] at hv
    omega

def budget (n B d u J incoming : ℕ) : ℕ :=
  75*incoming+97+additionBudget n B d u J

theorem budget_polynomial (n B d u J incoming : ℕ) :
    budget n B d u J incoming ≤
      75*incoming+97+3000000*(n+B+d+u+J+1)^10 := by
  have h := (additionBudget_le_local n B d u J 0).trans (localBudget_le n B d u J 0)
  simpa only [budget,Nat.add_zero] using Nat.add_le_add_left h (75*incoming+97)

theorem command_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (source seed : List (Product.Entry n (baseWidth p t) d))
    (hs : Good ∅ u J source) (hi : Good ∅ u J seed)
    (width degree : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (a : Data) (incoming : ℕ) (ha : ∀ i, (a.stacks i).length ≤ incoming)
    (hr : Ready a M.bits width degree (Product.bytes seed) (Product.bytes source)) :
    let output := Normalize.run p t M cache source seed
    ∃ steps rr, steps+1 ≤ budget n (baseWidth p t) d u J incoming ∧
      Eval command steps a (result a rr M.bits width degree (Product.bytes output)) ∧
      Good ∅ u J output := by
  dsimp only
  obtain ⟨steps,rr,hb,ht,hg,_⟩ := addition_run_space p t M cache source seed hs hi
    (fun i => (prepared a).regs (registers i)) width degree hd hw
  have he := eval_call_lifted Normalize.program registers ports (prepared a)
    registers_injective ports_injective ht
  rw [prepared_eq a M.bits width degree (Product.bytes seed) (Product.bytes source) hr] at he
  refine ⟨prepareCost a+steps,rr,?_,(prepare_eval a).seq he,hg⟩
  have hc := prepareCost_le a incoming ha
  unfold budget
  omega

theorem run_space (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (source seed : List (Product.Entry n (baseWidth p t) d))
    (hs : Good ∅ u J source) (hi : Good ∅ u J seed)
    (width degree : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (a : Data) (incoming : ℕ) (ha : ∀ i, (a.stacks i).length ≤ incoming)
    (hr : Ready a M.bits width degree (Product.bytes seed) (Product.bytes source)) :
    let output := Normalize.run p t M cache source seed
    ∃ steps rr, steps ≤ budget n (baseWidth p t) d u J incoming ∧
      Trace program steps (a.withPC (some program.entry))
        ((result a rr M.bits width degree (Product.bytes output)).withPC none) ∧
      Good ∅ u J output ∧
      ∀ time mid, time ≤ steps → Trace program time (a.withPC (some program.entry)) mid →
        ∀ i, (mid.stacks i).length ≤ 896*incoming+budget n (baseWidth p t) d u J incoming := by
  dsimp only
  obtain ⟨steps,rr,hb,he,hg⟩ := command_eval p t M cache source seed hs hi width degree
    hd hw a incoming ha hr
  refine ⟨steps+1,rr,hb,compiled_halt_trace he 852 851,hg,?_⟩
  have hbits : dataBits (a.withPC (some program.entry)) ≤ 896*incoming := by
    change (∑ i : Fin 896, (a.stacks i).length) ≤ _
    calc
      _ ≤ ∑ _ : Fin 896, incoming := Finset.sum_le_sum (fun i _ => ha i)
      _ = _ := by simp
  intro time mid hm ht i
  exact StructuredSpace.local_stack_bound program hbits time mid (hm.trans hb) ht i

/-- A fixed boundary cap is restored after each tuple. The temporary prefix
bound is kept separate and is never recursively substituted for this cap. -/
theorem result_bound_of_good {n B d u J : ℕ}
    (output : List (Product.Entry n B d)) (hg : Good ∅ u J output)
    (a : Data) (rr : Fin 8 → Bool) (modulus width degree seed source : List Bool)
    (hr : Ready a modulus width degree seed source)
    (bound : ℕ) (ha : ∀ i, (a.stacks i).length ≤ bound)
    (hcap : u*J*(2*(u+J+n)+2*(d*B)+2) ≤ bound) :
    ∀ i, ((result a rr modulus width degree (Product.bytes output)).stacks i).length ≤ bound :=
  result_bound a rr modulus width degree seed source (Product.bytes output) hr bound ha
    ((empty_bytes_length_le hg).trans hcap)

noncomputable section
variable {R : Type*} [CommRing R]

theorem output_dense (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (source seed : List (Product.Entry n (baseWidth p t) d)) (hi : Good ∅ u J seed) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    rawValue u J f (Normalize.run p t M cache source seed) =
      rawValue u J f seed+rawValue u J f source := by
  dsimp only
  rw [normalize_dense p t M cache scalar basis u J source seed hi.nodup,add_comm]

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleSum
