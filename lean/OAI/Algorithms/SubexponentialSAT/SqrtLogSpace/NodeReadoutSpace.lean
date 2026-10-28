import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

/-! Actual node-array readout after all finite-difference pairs. The fixed
cleanup pays for transient lower words and clears the old output. Preserved
masters supply the coefficient zero vector and both truncation bounds. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

abbrev Data := State 40 896
abbrev Code := Cmd 40 896

def registers : Fin 8 → Fin 40 := Fin.castAdd 32

theorem registers_injective : Function.Injective registers := Fin.castAdd_injective _ _

/-- Shared inputs are restored by the original native readout. -/
def ports (i : Fin 40) : Fin 896 :=
  if i = 0 then 862 else if i = 5 then 5 else if i = 12 then 12
  else if i = 15 then 850 else if i = 24 then 39 else if i = 27 then 280
  else if i = 28 then 212 else if i = 29 then 243 else if i = 36 then 128
  else ⟨88 + i.val, by omega⟩

private def portIndex (j : ℕ) : ℕ :=
  if j = 862 then 0 else if j = 5 then 5 else if j = 12 then 12
  else if j = 850 then 15 else if j = 39 then 24 else if j = 280 then 27
  else if j = 212 then 28 else if j = 243 then 29 else if j = 128 then 36
  else j - 88

private theorem portIndex_ports (i : Fin 40) : portIndex (ports i).val = i.val := by
  fin_cases i <;> rfl

theorem ports_injective : Function.Injective ports := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun k : Fin 896 => portIndex k.val) h
  simpa only [portIndex_ports] using hv

def scratchIndices : List (Fin 40) :=
  (List.ofFn (fun i : Fin 40 => i)).filter (fun i => decide
    (i ≠ 0 ∧ i ≠ 5 ∧ i ≠ 12 ∧ i ≠ 15 ∧ i ≠ 24 ∧ i ≠ 27 ∧
      i ≠ 28 ∧ i ≠ 29 ∧ i ≠ 36))

def scratchPorts : List (Fin 896) := scratchIndices.map ports

def clearPorts : List (Fin 896) := 862 :: scratchPorts

theorem mem_scratchIndices (i : Fin 40) : i ∈ scratchIndices ↔
    i ≠ 0 ∧ i ≠ 5 ∧ i ≠ 12 ∧ i ≠ 15 ∧ i ≠ 24 ∧ i ≠ 27 ∧
      i ≠ 28 ∧ i ≠ 29 ∧ i ≠ 36 := by
  simp only [scratchIndices, List.mem_filter, List.mem_ofFn, exists_eq,
    decide_eq_true_eq, true_and]

theorem scratchPorts_low {i : Fin 896} (hi : i ∈ scratchPorts) :
    88 ≤ i.val ∧ i.val < 128 := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  obtain ⟨h0,h5,h12,h15,h24,h27,h28,h29,h36⟩ := (mem_scratchIndices j).mp hj
  simp only [ports, h0, h5, h12, h15, h24, h27, h28, h29, h36, ite_false]
  omega

theorem clearPorts_length : clearPorts.length ≤ 41 := by
  have h := List.length_filter_le
    (p := fun i : Fin 40 => decide
      (i ≠ 0 ∧ i ≠ 5 ∧ i ≠ 12 ∧ i ≠ 15 ∧ i ≠ 24 ∧ i ≠ 27 ∧
        i ≠ 28 ∧ i ≠ 29 ∧ i ≠ 36)) (l := List.ofFn (fun i : Fin 40 => i))
  simpa only [clearPorts, scratchPorts, scratchIndices, List.length_cons,
    List.length_map, List.length_ofFn] using Nat.succ_le_succ h

def clearOne (i : Fin 896) : Code := .call (StackRoutines.clearProgram i 0 1)

def cleared (i : Fin 896) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, Function.update a.stacks i []⟩

def clearMany : List (Fin 896) → Code
  | [] => .base .skip
  | i :: is => .seq (clearOne i) (clearMany is)

def clearedMany : List (Fin 896) → Data → Data
  | [], a => a
  | i :: is, a => clearedMany is (cleared i a)

def clearCost : List (Fin 896) → Data → ℕ
  | [], _ => 0
  | i :: is, a => 2 * (a.stacks i).length + 3 + clearCost is (cleared i a)

theorem clearOne_eval (i : Fin 896) (a : Data) :
    Eval (clearOne i) (2 * (a.stacks i).length + 3) a (cleared i a) :=
  .call _ (ListRegisterProgram.clear_run i 0 1 a.regs a.stacks)

theorem clearMany_eval (ps : List (Fin 896)) (a : Data) :
    Eval (clearMany ps) (clearCost ps a) a (clearedMany ps a) := by
  induction ps generalizing a with
  | nil => exact .base (.skip a)
  | cons p ps ih => exact (clearOne_eval p a).seq (ih _)

theorem clearedMany_stack (ps : List (Fin 896)) (a : Data) (i : Fin 896) :
    (clearedMany ps a).stacks i = if i ∈ ps then [] else a.stacks i := by
  induction ps generalizing a with
  | nil => simp [clearedMany]
  | cons p ps ih =>
      rw [clearedMany, ih]
      by_cases hp : i = p <;> by_cases hs : i ∈ ps <;> simp [cleared, hp, hs]

theorem clearCost_le (ps : List (Fin 896)) (a : Data) (B : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ B) : clearCost ps a ≤ ps.length * (2 * B + 3) := by
  induction ps generalizing a with
  | nil => simp [clearCost]
  | cons p ps ih =>
      have hb : ∀ i, ((cleared p a).stacks i).length ≤ B := by
        intro i
        by_cases hi : i = p
        · subst i; simp [cleared]
        · simpa [cleared, hi] using ha i
      have ht := ih (cleared p a) hb
      have hp := ha p
      simp only [clearCost, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

def command : Code := .seq (clearMany clearPorts)
  (.call (ProgramLinking.liftProgram MomentsReadoutProgram.program registers ports))

def program := compiled command 850 862

def budget (n B d u J incoming : ℕ) : ℕ :=
  41 * (2 * incoming + 3) +
    MomentsReadoutProgram.uniformReadoutBudget B d n u J (n + u + J) (u * J) + 1

/-- Only actual retained words are hypotheses; scratch is physically cleared. -/
structure Ready (a : Data) (modulus width degree dictionary zero marker taylor shape : List Bool) : Prop where
  modulus : a.stacks 5 = modulus
  width : a.stacks 12 = width
  degree : a.stacks 39 = degree
  dictionary : a.stacks 850 = dictionary
  zero : a.stacks 280 = zero
  marker : a.stacks 212 = marker
  taylor : a.stacks 243 = taylor
  shape : a.stacks 128 = shape

def localState (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape output : List Bool) : State 8 40 :=
  MomentsReadoutProgram.wideState rr
    {modulus := modulus, width := width, count := degree, dict := dictionary, out := output}
    (MomentsReadoutProgram.inputHigh zero marker taylor shape)

theorem localState_stack (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape output : List Bool) (i : Fin 40) :
    (localState rr modulus width degree dictionary zero marker taylor shape output).stacks i =
      if i = 0 then output else if i = 5 then modulus else if i = 12 then width
      else if i = 15 then dictionary else if i = 24 then degree else if i = 27 then zero
      else if i = 28 then marker else if i = 29 then taylor else if i = 36 then shape else [] := by
  fin_cases i <;> rfl

theorem clearedMany_frame (a : Data) (i : Fin 896) (hi : i ∉ clearPorts) :
    (clearedMany clearPorts a).stacks i = a.stacks i := by
  rw [clearedMany_stack, ite_eq_right hi]

theorem prepared_eq (a : Data)
    (modulus width degree dictionary zero marker taylor shape : List Bool)
    (h : Ready a modulus width degree dictionary zero marker taylor shape) :
    let b := clearedMany clearPorts a
    embedState registers ports b
      (localState (fun i => b.regs (registers i))
        modulus width degree dictionary zero marker taylor shape []) = b := by
  dsimp only
  apply embedState_eq_of_ports _ _ _ _ _ registers_injective ports_injective
  · intro i; rfl
  · intros; rfl
  · intro i
    rw [localState_stack]
    by_cases h0 : i = 0
    · subst i
      simp [ports, clearedMany_stack,
        show (862 : Fin 896) ∈ clearPorts from List.mem_cons_self]
    by_cases h5 : i = 5
    · subst i
      simpa [ports, clearedMany_frame a 5 (by decide)] using h.modulus
    by_cases h12 : i = 12
    · subst i
      simpa [ports, clearedMany_frame a 12 (by decide)] using h.width
    by_cases h15 : i = 15
    · subst i
      simpa [ports, clearedMany_frame a 850 (by decide)] using h.dictionary
    by_cases h24 : i = 24
    · subst i
      simpa [ports, clearedMany_frame a 39 (by decide)] using h.degree
    by_cases h27 : i = 27
    · subst i
      simpa [ports, clearedMany_frame a 280 (by decide)] using h.zero
    by_cases h28 : i = 28
    · subst i
      simpa [ports, clearedMany_frame a 212 (by decide)] using h.marker
    by_cases h29 : i = 29
    · subst i
      simpa [ports, clearedMany_frame a 243 (by decide)] using h.taylor
    by_cases h36 : i = 36
    · subst i
      simpa [ports, clearedMany_frame a 128 (by decide)] using h.shape
    have hm : ports i ∈ scratchPorts := List.mem_map.mpr
      ⟨i, (mem_scratchIndices i).mpr ⟨h0,h5,h12,h15,h24,h27,h28,h29,h36⟩, rfl⟩
    have hmc : ports i ∈ clearPorts := List.mem_cons_of_mem 862 hm
    rw [clearedMany_stack, ite_eq_left hmc]
    simp only [h0, h5, h12, h15, h24, h27, h28, h29, h36, ite_false]
  · intros; rfl

noncomputable def result (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool) : Data :=
  embedState registers ports (clearedMany clearPorts a)
    (localState rr modulus width degree dictionary zero marker taylor shape bits)

theorem result_output (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).stacks 862 = bits := by
  change (embedState registers ports _ _).stacks (ports 0) = bits
  rw [embedState_stack _ _ _ _ ports_injective]
  rfl

theorem result_stack (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : Ready a modulus width degree dictionary zero marker taylor shape)
    (i : Fin 896) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).stacks i =
      if i = 862 then bits else (clearedMany clearPorts a).stacks i := by
  by_cases hi : ∃ j, ports j = i
  · obtain ⟨j, rfl⟩ := hi
    change (embedState registers ports _ _).stacks (ports j) = _
    rw [embedState_stack _ _ _ _ ports_injective]
    by_cases hj : j = 0
    · subst j
      simp only [localState_stack, ports, ↓reduceIte]
    have hn : ports j ≠ 862 := fun h => hj (ports_injective (show ports j = ports 0 from h))
    rw [ite_eq_right hn]
    have hp := congrArg (fun d : Data => d.stacks (ports j))
      (prepared_eq a modulus width degree dictionary zero marker taylor shape hr)
    rw [embedState_stack _ _ _ _ ports_injective] at hp
    rw [← hp]
    simp only [localState_stack, hj, ite_false]
  · have hn : i ≠ 862 := fun h => hi ⟨0, (show ports 0 = 862 from rfl).trans h.symm⟩
    change (embedState registers ports _ _).stacks i = _
    rw [embedState_stack_frame _ _ _ _ i hi, ite_eq_right hn]

/-- All input masters and other high query buffers survive exactly. -/
theorem result_frame (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : Ready a modulus width degree dictionary zero marker taylor shape)
    (i : Fin 896) (ho : i ≠ 862) (hs : i ∉ scratchPorts) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).stacks i =
      a.stacks i := by
  rw [result_stack a rr _ _ _ _ _ _ _ _ _ hr i, ite_eq_right ho, clearedMany_stack]
  exact ite_eq_right (by simpa only [clearPorts, List.mem_cons, not_or] using And.intro ho hs)

theorem result_scratch (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : Ready a modulus width degree dictionary zero marker taylor shape)
    (i : Fin 896) (hs : i ∈ scratchPorts) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).stacks i = [] := by
  have ho : i ≠ 862 := by
    have := scratchPorts_low hs
    intro h
    subst i
    change 88 ≤ 862 ∧ 862 < 128 at this
    omega
  rw [result_stack a rr _ _ _ _ _ _ _ _ _ hr i, ite_eq_right ho, clearedMany_stack]
  exact ite_eq_left (List.mem_cons_of_mem 862 hs)

theorem result_bound (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : Ready a modulus width degree dictionary zero marker taylor shape)
    (bound : ℕ) (ha : ∀ i, (a.stacks i).length ≤ bound) (hb : bits.length ≤ bound) :
    ∀ i, ((result a rr modulus width degree dictionary zero marker taylor shape bits).stacks i).length ≤ bound := by
  intro i
  rw [result_stack a rr _ _ _ _ _ _ _ _ _ hr i]
  by_cases ho : i = 862
  · simpa only [ite_eq_left ho] using hb
  rw [ite_eq_right ho, clearedMany_stack]
  by_cases hc : i ∈ clearPorts
  · simp only [ite_eq_left hc, List.length_nil, Nat.zero_le]
  · simpa only [ite_eq_right hc] using ha i

theorem clearedMany_register (ps : List (Fin 896)) (a : Data) (i : Fin 40)
    (h0 : i ≠ 0) (h1 : i ≠ 1) : (clearedMany ps a).regs i = a.regs i := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
      rw [clearedMany, ih]
      exact StackRoutines.readRegs_frame a.regs 0 1 i none h0 h1

theorem result_register_frame (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (i : Fin 40) (hi : 8 ≤ i.val) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).regs i = a.regs i := by
  change (embedState registers ports _ _).regs i = _
  rw [embedState_register_frame]
  · exact clearedMany_register clearPorts a i
      (fun h => by subst i; simp at hi) (fun h => by subst i; simp at hi)
  · rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    simp only [registers, Fin.val_castAdd] at hv
    omega

theorem budget_polynomial (n B d u J incoming : ℕ) :
    budget n B d u J incoming ≤
      41 * (2 * incoming + 3) + 30000 * (n + B + d + u + J + 1) ^ 6 + 1 := by
  exact Nat.add_le_add_right
    (Nat.add_le_add_left (TruncatedRingProgram.readoutBudget_polynomial n B d u J) _) 1

/-- One fixed instruction sequence clears scratch and performs the actual readout. -/
theorem command_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (entries : List (Product.Entry n (baseWidth p t) d))
    (he : Good ∅ u J entries) (zero : RingProgram.Code (Word (baseWidth p t)) d)
    (width degree marker taylor shape : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hu : marker.length = u) (hJ : taylor.length = J) (hs : shape.length = n)
    (a : Data) (incoming : ℕ) (ha : ∀ i, (a.stacks i).length ≤ incoming)
    (hr : Ready a M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
      marker taylor shape) :
    let bits := MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J
    ∃ steps rr,
      steps + 1 ≤ budget n (baseWidth p t) d u J incoming ∧
      Eval command steps a
        (result a rr M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
          marker taylor shape bits) ∧ bits.length = J * (d * baseWidth p t) := by
  dsimp only
  let b := clearedMany clearPorts a
  obtain ⟨steps, rr, hb, ht, hl, _⟩ := readout_run_space p t M cache entries he zero
    (fun i => b.regs (registers i)) width degree marker taylor shape hd hw hu hJ hs
  have call := eval_call_lifted MomentsReadoutProgram.program registers ports b
    registers_injective ports_injective ht
  change Eval _ steps
    (embedState registers ports b
      (localState (fun i => b.regs (registers i)) M.bits width degree (Product.bytes entries)
        (RingProgram.flat zero) marker taylor shape []))
    (result a rr M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
      marker taylor shape _) at call
  rw [prepared_eq a M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
    marker taylor shape hr] at call
  refine ⟨clearCost clearPorts a + steps, rr, ?_, (clearMany_eval clearPorts a).seq call, hl⟩
  have hc := (clearCost_le clearPorts a incoming ha).trans
    (Nat.mul_le_mul_right _ clearPorts_length)
  unfold budget
  omega

/-- The same concrete run has the exact flattened output and a bound at every
source prefix, including paid cleanup and every retained caller stack. -/
theorem run_space (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (entries : List (Product.Entry n (baseWidth p t) d))
    (he : Good ∅ u J entries) (zero : RingProgram.Code (Word (baseWidth p t)) d)
    (width degree marker taylor shape : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hu : marker.length = u) (hJ : taylor.length = J) (hs : shape.length = n)
    (a : Data) (incoming : ℕ) (ha : ∀ i, (a.stacks i).length ≤ incoming)
    (hr : Ready a M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
      marker taylor shape) :
    let bits := MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J
    ∃ steps rr,
      steps ≤ budget n (baseWidth p t) d u J incoming ∧
      Trace program steps (a.withPC (some program.entry))
        ((result a rr M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
          marker taylor shape bits).withPC none) ∧
      bits.length = J * (d * baseWidth p t) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace program prefixSteps (a.withPC (some program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          896 * incoming + budget n (baseWidth p t) d u J incoming := by
  dsimp only
  obtain ⟨steps, rr, hb, ht, hl⟩ := command_eval p t M cache entries he zero
    width degree marker taylor shape hd hw hu hJ hs a incoming ha hr
  refine ⟨steps + 1, rr, hb, compiled_halt_trace ht 850 862, hl, ?_⟩
  have hbits : dataBits (a.withPC (some program.entry)) ≤ 896 * incoming := by
    change (∑ i : Fin 896, (a.stacks i).length) ≤ _
    calc
      _ ≤ ∑ _ : Fin 896, incoming := Finset.sum_le_sum (fun i _ => ha i)
      _ = _ := by simp
  intro prefixSteps intermediate hp htrace i
  exact StructuredSpace.local_stack_bound program hbits prefixSteps intermediate
    (hp.trans hb) htrace i

noncomputable section
variable {R : Type*} [CommRing R]

/-- The actual output is the unframed Taylor coefficient stream, in increasing
Taylor order, and its decoded polynomial is the additive dense readout. -/
theorem output_codes_dense (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (entries : List (Product.Entry n (baseWidth p t) d))
    (he : Good ∅ u J entries) (zero : RingProgram.Code (Word (baseWidth p t)) d)
    (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (hz : RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis zero = 0)
    (a : Data) (rr : Fin 8 → Bool) (width degree marker taylor shape : List Bool) :
    let codes := MomentsReadoutProgram.outputCodes p t M cache entries u zero 0 J
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    (result a rr M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
      marker taylor shape (MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J)).stacks 862 =
        (codes.map RingProgram.flat).flatten ∧
      Truncated.ofPolynomial J (PolynomialAlgorithm.denote (codes.map f)) =
        Dense.readout (rawValue u J f entries) := by
  dsimp only
  exact ⟨result_output a rr _ _ _ _ _ _ _ _ _,
    TruncatedRingProgram.readout_codes_dense p t M cache scalar basis u J entries zero he.nodup hz⟩

end

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace
