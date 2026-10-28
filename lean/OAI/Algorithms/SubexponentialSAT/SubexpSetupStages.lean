import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupProgram

namespace OAI.Algorithms

/-! Actual execution and frame rules for the statically allocated setup stages. -/

noncomputable section

namespace SubexponentialSAT.SubexpSetupProgram

open BitProgram StructuredCalls SubexpSetupStorage

def Protected (c : Config) (i : Fin (stackCount c)) : Prop := helperSize c ≤ i.val

def Preserves (c : Config) (modified : List (Fin (stackCount c)))
    (a b : SetupState c) : Prop :=
  b.regs 15 = a.regs 15 ∧
    ∀ i, Protected c i → i ∉ modified → b.stacks i = a.stacks i

@[simp] theorem persistent_protected (c : Config) (i : Fin 32) :
    Protected c (persistent c i) := by
  change helperSize c ≤ helperSize c + thresholdCount c + i.val
  omega

@[simp] theorem threshold_protected (c : Config) (i : Fin (thresholdCount c)) :
    Protected c (threshold c i) := by
  change helperSize c ≤ helperSize c + i.val
  omega

theorem protected_ne_work (c : Config) {s : ℕ} (hs : s < helperSize c)
    {i : Fin (stackCount c)} (hi : Protected c i) (j : Fin s) : i ≠ workPort c hs j := by
  intro he
  have hv := congrArg Fin.val he
  unfold Protected at hi
  change i.val = j.val at hv
  have := j.isLt
  omega

theorem protected_ne_temporary (c : Config) {i : Fin (stackCount c)}
    (hi : Protected c i) : i ≠ temporary c := by
  intro he
  have hv := congrArg Fin.val he
  unfold Protected at hi
  change i.val = helperSize c - 1 at hv
  have hh : 0 < helperSize c := by unfold helperSize; omega
  omega

theorem work_ne_temporary (c : Config) {s : ℕ} (hs : s < helperSize c) (j : Fin s) :
    workPort c hs j ≠ temporary c := by
  intro he
  have hv := congrArg Fin.val he
  change j.val = helperSize c - 1 at hv
  have := j.isLt
  omega

theorem protected_not_localPorts (c : Config) {s : ℕ} (hs : s < helperSize c)
    {i : Fin (stackCount c)} (hi : Protected c i) : i ∉ localPorts c hs := by
  simp only [localPorts, List.mem_ofFn, not_exists]
  intro j he
  exact protected_ne_work c hs hi j he.symm

theorem work_mem_localPorts (c : Config) {s : ℕ} (hs : s < helperSize c) (j : Fin s) :
    workPort c hs j ∈ localPorts c hs := by
  simp only [localPorts, List.mem_ofFn]
  exact ⟨j, rfl⟩

theorem inputCopies_good (c : Config) {s : ℕ} (hs : s < helperSize c)
    (inputs : List (Fin (stackCount c) × Fin s))
    (hi : ∀ p ∈ inputs, Protected c p.1) :
    ∀ p ∈ inputCopies c hs inputs,
      p.1 ≠ p.2 ∧ p.1 ≠ temporary c ∧ temporary c ≠ p.2 := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact ⟨protected_ne_work c hs (hi q hq) q.2,
    protected_ne_temporary c (hi q hq), (work_ne_temporary c hs q.2).symm⟩

theorem outputCopies_good (c : Config) {s : ℕ} (hs : s < helperSize c)
    (outputs : List (Fin s × Fin (stackCount c)))
    (ho : ∀ p ∈ outputs, Protected c p.2) :
    ∀ p ∈ outputCopies c hs outputs,
      p.1 ≠ p.2 ∧ p.1 ≠ temporary c ∧ temporary c ≠ p.2 := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact ⟨(protected_ne_work c hs (ho q hq) q.1).symm,
    work_ne_temporary c hs q.1, (protected_ne_temporary c (ho q hq)).symm⟩

def prepared (c : Config) {s : ℕ} (hs : s < helperSize c)
    (inputs : List (Fin (stackCount c) × Fin s)) (a : SetupState c) : SetupState c :=
  prepareState (temporary c) (localPorts c hs) (inputCopies c hs inputs) a

def returned (c : Config) {r s : ℕ} (register : Fin r → Fin 16)
    (hs : s < helperSize c) (inputs : List (Fin (stackCount c) × Fin s))
    (outputs : List (Fin s × Fin (stackCount c))) (a : SetupState c) (out : State r s) :
    SetupState c :=
  finishState (localPorts c hs) (outputCopies c hs outputs)
    (embedState register (workPort c hs) (prepared c hs inputs a) out)

def stageCost (c : Config) {r s : ℕ} (register : Fin r → Fin 16)
    (hs : s < helperSize c) (inputs : List (Fin (stackCount c) × Fin s))
    (outputs : List (Fin s × Fin (stackCount c))) (a : SetupState c)
    (out : State r s) (t : ℕ) : ℕ :=
  prepareCost (temporary c) (localPorts c hs) (inputCopies c hs inputs) a +
    (t + finishCost (localPorts c hs) (outputCopies c hs outputs)
      (embedState register (workPort c hs) (prepared c hs inputs a) out))

theorem stageCost_mono (c : Config) {r s : ℕ} (register : Fin r → Fin 16)
    (hs : s < helperSize c) (inputs : List (Fin (stackCount c) × Fin s))
    (outputs : List (Fin s × Fin (stackCount c))) (a : SetupState c)
    (out : State r s) {t u : ℕ} (h : t ≤ u) :
    stageCost c register hs inputs outputs a out t ≤
      stageCost c register hs inputs outputs a out u := by
  unfold stageCost
  omega

theorem prepared_frame (c : Config) {s : ℕ} (hs : s < helperSize c)
    (inputs : List (Fin (stackCount c) × Fin s)) (a : SetupState c)
    (i : Fin (stackCount c)) (hi : Protected c i) :
    (prepared c hs inputs a).stacks i = a.stacks i := by
  apply prepare_frame _ _ _ _ _ (protected_ne_temporary c hi)
    (protected_not_localPorts c hs hi)
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact protected_ne_work c hs hi q.2

theorem prepared_word (c : Config) {s : ℕ} (hs : s < helperSize c)
    (inputs : List (Fin (stackCount c) × Fin s)) (a : SetupState c)
    (hi : ∀ p ∈ inputs, Protected c p.1) (hd : (inputs.map Prod.snd).Nodup)
    (p : Fin (stackCount c) × Fin s) (hp : p ∈ inputs) :
    (prepared c hs inputs a).stacks (workPort c hs p.2) = a.stacks p.1 := by
  have hd' : ((inputCopies c hs inputs).map Prod.snd).Nodup := by
    simpa only [inputCopies, List.map_map, Function.comp_def] using
      (List.Nodup.map (workPort_injective c hs) hd)
  have hc : ∀ q ∈ inputCopies c hs inputs,
      (beforeCopies (temporary c) (localPorts c hs) a).stacks q.2 = [] := by
    intro q hq
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hq
    simp only [beforeCopies, resetMany_stacks, clearMany_stacks,
      ite_eq_left (work_mem_localPorts c hs z.2)]
  have hsep : ∀ q ∈ inputCopies c hs inputs, ∀ z ∈ inputCopies c hs inputs, q.1 ≠ z.2 := by
    intro q hq z hz
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    exact protected_ne_work c hs (hi q' hq') z'.2
  have hv := copyMany_value (inputCopies c hs inputs)
    (beforeCopies (temporary c) (localPorts c hs) a) hd' hc hsep
    (p.1, workPort c hs p.2) (List.mem_map.mpr ⟨p, hp, rfl⟩)
  change (prepared c hs inputs a).stacks (workPort c hs p.2) = _ at hv
  rw [hv]
  simp only [beforeCopies, resetMany_stacks, clearMany_stacks,
    ite_eq_right (protected_not_localPorts c hs (hi p hp))]
  simp [protected_ne_temporary c (hi p hp)]

theorem prepared_empty (c : Config) {s : ℕ} (hs : s < helperSize c)
    (inputs : List (Fin (stackCount c) × Fin s)) (a : SetupState c)
    (j : Fin s) (hj : ∀ p ∈ inputs, j ≠ p.2) :
    (prepared c hs inputs a).stacks (workPort c hs j) = [] := by
  have hn : ∀ p ∈ inputCopies c hs inputs, workPort c hs j ≠ p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact fun he => hj q hq ((workPort_injective c hs) he)
  unfold prepared prepareState
  rw [copyMany_frame _ _ _ hn]
  simp only [beforeCopies, resetMany_stacks, clearMany_stacks,
    ite_eq_left (work_mem_localPorts c hs j)]

/-- A concrete canonical callee state follows from its assigned input ports,
zero scratch words, and register values after the real preparation code. -/
theorem prepared_eq (c : Config) {r s : ℕ} (register : Fin r → Fin 16)
    (hs : s < helperSize c) (inputs : List (Fin (stackCount c) × Fin s))
    (a : SetupState c) (start : State r s)
    (hi : ∀ p ∈ inputs, Protected c p.1) (hd : (inputs.map Prod.snd).Nodup)
    (hr : ∀ j, (prepared c hs inputs a).regs (register j) = start.regs j)
    (hw : ∀ p ∈ inputs, start.stacks p.2 = a.stacks p.1)
    (hz : ∀ j, (∀ p ∈ inputs, j ≠ p.2) → start.stacks j = []) :
    project register (workPort c hs) (prepared c hs inputs a) = start := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext j; exact hr j
  · funext j
    by_cases hm : ∃ p ∈ inputs, p.2 = j
    · obtain ⟨p, hp, rfl⟩ := hm
      exact (prepared_word c hs inputs a hi hd p hp).trans (hw p hp).symm
    · have hj : ∀ p ∈ inputs, j ≠ p.2 := by
        intro p hp he
        exact hm ⟨p, hp, he.symm⟩
      exact (prepared_empty c hs inputs a j hj).trans (hz j hj).symm

theorem prepared_register (c : Config) {r s : ℕ} (hr : r ≤ 9)
    (hs : s < helperSize c) (inputs : List (Fin (stackCount c) × Fin s))
    (a : SetupState c) (j : Fin r) :
    (prepared c hs inputs a).regs (registerPort hr j) = false :=
  prepare_reg _ _ _ _ (j.castLE hr)

theorem stage_eval (c : Config) {r s l : ℕ} (p : Program r s l)
    (register : Fin r → Fin 16) (hr : Function.Injective register)
    (hs : s < helperSize c) (inputs : List (Fin (stackCount c) × Fin s))
    (outputs : List (Fin s × Fin (stackCount c))) (a : SetupState c)
    (start out : State r s) {t : ℕ}
    (hi : ∀ q ∈ inputs, Protected c q.1) (ho : ∀ q ∈ outputs, Protected c q.2)
    (hlocal : project register (workPort c hs) (prepared c hs inputs a) = start)
    (ht : Trace p t (start.withPC (some p.entry)) (out.withPC none)) :
    Eval (stage c p register hs inputs outputs)
      (stageCost c register hs inputs outputs a out t) a
      (returned c register hs inputs outputs a out) := by
  apply isolated_eval p register (workPort c hs) hr (workPort_injective c hs)
    (temporary c) (localPorts c hs) (inputCopies c hs inputs) (outputCopies c hs outputs)
    a out (inputCopies_good c hs inputs hi) (outputCopies_good c hs outputs ho)
  · rintro ⟨j, hj⟩
    exact work_ne_temporary c hs j hj
  · change Trace p t
      ((project register (workPort c hs) (prepared c hs inputs a)).withPC (some p.entry))
      (out.withPC none)
    rw [hlocal]
    exact ht

theorem returned_word (c : Config) {r s : ℕ} (register : Fin r → Fin 16)
    (hs : s < helperSize c) (inputs : List (Fin (stackCount c) × Fin s))
    (outputs : List (Fin s × Fin (stackCount c))) (a : SetupState c) (out : State r s)
    (ho : ∀ q ∈ outputs, Protected c q.2) (hd : (outputs.map Prod.snd).Nodup)
    (p : Fin s × Fin (stackCount c)) (hp : p ∈ outputs) :
    (returned c register hs inputs outputs a out).stacks p.2 = out.stacks p.1 := by
  have hd' : ((outputCopies c hs outputs).map Prod.snd).Nodup := by
    simpa only [outputCopies, List.map_map, Function.comp_def] using hd
  have hsep : ∀ q ∈ outputCopies c hs outputs, ∀ z ∈ outputCopies c hs outputs, q.1 ≠ z.2 := by
    intro q hq z hz
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hq
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    exact (protected_ne_work c hs (ho z' hz') q'.1).symm
  exact (finish_value (localPorts c hs) (outputCopies c hs outputs) _ hd' hsep
    (workPort c hs p.1, p.2) (List.mem_map.mpr ⟨p, hp, rfl⟩)
    (protected_not_localPorts c hs (ho p hp))).trans
      (embedState_stack register (workPort c hs) _ out (workPort_injective c hs) p.1)

theorem returned_frame (c : Config) {r s : ℕ} (register : Fin r → Fin 16)
    (hs : s < helperSize c) (inputs : List (Fin (stackCount c) × Fin s))
    (outputs : List (Fin s × Fin (stackCount c))) (a : SetupState c) (out : State r s)
    (i : Fin (stackCount c)) (hi : Protected c i)
    (hne : ∀ p ∈ outputs, i ≠ p.2) :
    (returned c register hs inputs outputs a out).stacks i = a.stacks i := by
  have hno : ∀ p ∈ outputCopies c hs outputs, i ≠ p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact hne q hq
  exact (finish_frame (localPorts c hs) (outputCopies c hs outputs) _ i
    (protected_not_localPorts c hs hi) hno).trans
      ((embedState_stack_frame register (workPort c hs) _ out i (by
        rintro ⟨j, hj⟩; exact protected_ne_work c hs hi j hj.symm)).trans
          (prepared_frame c hs inputs a i hi))

theorem returned_flag (c : Config) {r s : ℕ} (hr : r ≤ 9)
    (hs : s < helperSize c) (inputs : List (Fin (stackCount c) × Fin s))
    (outputs : List (Fin s × Fin (stackCount c))) (a : SetupState c) (out : State r s) :
    (returned c (registerPort hr) hs inputs outputs a out).regs 15 = a.regs 15 := by
  unfold returned
  rw [finish_flag]
  rw [embedState_register_frame]
  · exact prepare_flag _ _ _ _
  · rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = 15 at hv
    have := j.isLt
    omega

theorem returned_guard_flag (c : Config) {s : ℕ}
    (hs : s < helperSize c) (inputs : List (Fin (stackCount c) × Fin s))
    (outputs : List (Fin s × Fin (stackCount c))) (a : SetupState c) (out : State 9 s) :
    (returned c guardRegister hs inputs outputs a out).regs 15 = out.regs 8 := by
  unfold returned
  rw [finish_flag]
  exact embedState_register guardRegister (workPort c hs) _ out guardRegister_injective 8

theorem returned_workReg (c : Config) {r s : ℕ} (register : Fin r → Fin 16)
    (hs : s < helperSize c) (inputs : List (Fin (stackCount c) × Fin s))
    (outputs : List (Fin s × Fin (stackCount c))) (a : SetupState c) (out : State r s)
    (j : Fin 9) :
    (returned c register hs inputs outputs a out).regs (j.castLE (by decide)) = false :=
  finish_workReg _ _ _ j

theorem returned_preserves (c : Config) {r s : ℕ} (hr : r ≤ 9)
    (hs : s < helperSize c) (inputs : List (Fin (stackCount c) × Fin s))
    (outputs : List (Fin s × Fin (stackCount c))) (a : SetupState c) (out : State r s) :
    Preserves c (outputs.map Prod.snd) a
      (returned c (registerPort hr) hs inputs outputs a out) := by
  refine ⟨returned_flag c hr hs inputs outputs a out, ?_⟩
  intro i hi hm
  apply returned_frame c _ hs inputs outputs a out i hi
  intro p hp he
  exact hm (List.mem_map.mpr ⟨p, hp, he.symm⟩)

end SubexponentialSAT.SubexpSetupProgram

end

end OAI.Algorithms
