import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramCofactorOuter
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramScalarSteps
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramHorner
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramLocal

namespace OAI.Algorithms

/-! Composition of the physical arithmetic stages for one Hermite node. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram
open CRTLocalProgram (LowFrame ServiceSpec)

private def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

abbrev command (localCode multiply add : Cmd 16 256) : Code :=
  CofactorOuter.command multiply ;; Scalar.negative multiply ;; Local.command localCode ;;
    Horner.command multiply add ;; Scalar.accumulate multiply add

def budget (Q J W Km Ka Kl : ℕ) : ℕ :=
  CofactorOuter.budget Q Km W J + (Km + 26 * W + 26) + Local.budget (J*W) J Kl +
    Horner.budget J W Km Ka + (Km + Ka + 58 * W + 61)

def cleanPorts : List (Fin 320) :=
  CofactorOuter.cleanPorts ++ Scalar.cleanPorts ++ Horner.cleanPorts ++ [192,193,262,263,264]

theorem lowFrame_update_outer (s : Fin 320 → List Bool) (j : Fin 320) (hj : 205 ≤ j.val)
    (word : List Bool) : LowFrame (s ∘ localPorts) ((Function.update s j word) ∘ localPorts) := by
  intro i hi
  have hne : localPorts i ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    change i.val = j.val at hv
    omega
  simp [ hne]

def nodeValue {C : Type*} (mul add : C → C → C) (minusOne zero unit node acc : C)
    (J : ℕ) (remaining processed correction : List C) : C :=
  add acc (mul ((remaining ++ processed).foldl (Cofactor.includeValue mul minusOne J) unit)
    (HornerProgram.fold (HornerProgram.stepValue mul add (mul node minusOne)) correction.reverse zero))

theorem command_run {C : Type*} (encode : C → List Bool)
    (localCode multiply add : Cmd 16 256) (mulOp addOp : C → C → C)
    (Km Ka Kl W J : ℕ) (d : Data) (remaining processed correction : List C)
    (unit minusOne zero node acc : C)
    (hm : ServiceSpec (d.stacks ∘ localPorts) encode multiply mulOp Km)
    (ha : ServiceSpec (d.stacks ∘ localPorts) encode add addOp Ka)
    (hw : ∀ a, (encode a).length = W) (hW : 0 < W)
    (hr : d.stacks 257 = remaining.flatMap encode) (hp : d.stacks 258 = processed.flatMap encode)
    (hu : d.stacks 207 = encode unit) (hn : d.stacks 211 = encode minusOne)
    (hz : d.stacks 104 = encode zero) (hx : d.stacks 259 = encode node)
    (hacc : d.stacks 261 = encode acc) (hJ : d.stacks 243 = List.replicate J true)
    (hcorr : correction.length = J) (h277 : (d.stacks 277).length = J * W)
    (hc : ∀ i ∈ cleanPorts, d.stacks i = [])
    (hlocal : SubexpConvolutionControl.ExecutesIn localCode Kl
      ((Local.prepared d).stacks ∘ localPorts)
      (Function.update ((Local.prepared d).stacks ∘ localPorts) 244
        (HornerProgram.encodePolynomial encode correction))) :
    ∃ n ≤ budget (remaining.length + processed.length) J W Km Ka Kl, ∃ rf,
      Eval (command localCode multiply add) n d
        ⟨rf, Function.update d.stacks 261
          (encode (nodeValue mulOp addOp minusOne zero unit node acc J remaining processed correction))⟩ := by
  have hzero (i : Fin 320) (hi : i ∈ cleanPorts) := hc i hi
  have hco : ∀ i ∈ CofactorOuter.cleanPorts, d.stacks i = [] := by
    intro i hi; apply hc i; simp only [cleanPorts, List.mem_append]; tauto
  obtain ⟨n1, hn1, r1, h1⟩ := CofactorOuter.command_run encode multiply mulOp Km W J d
    remaining processed unit minusOne hm hw hW hr hp hu hn hJ (by simp [hz, hw]) hco
  let factor := (remaining ++ processed).foldl (Cofactor.includeValue mulOp minusOne J) unit
  let point := mulOp node minusOne
  let value := HornerProgram.fold (HornerProgram.stepValue mulOp addOp point) correction.reverse zero
  let d1 : Data := ⟨r1, Function.update d.stacks 262 (encode factor)⟩
  have hm1 : ServiceSpec (d1.stacks ∘ localPorts) encode multiply mulOp Km := by
    simpa only [d1, Scalar.lower_update_high d.stacks 262 (by decide)] using hm
  have hsc1 : ∀ i ∈ Scalar.cleanPorts, d1.stacks i = [] := by
    intro i hi
    simp only [Scalar.cleanPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [d1] using hc _ (by simp [cleanPorts, Scalar.cleanPorts])
  obtain ⟨n2, hn2, r2, h2⟩ := Scalar.negative_run encode multiply mulOp Km W d1 node minusOne
    hm1 hw (by simpa [d1] using hx) (by simpa [d1] using hn)
    (by simpa [d1] using hc 263 (by simp [cleanPorts])) hsc1
  let d2 : Data := ⟨r2, Function.update d1.stacks 263 (encode point)⟩
  have hpre : (Local.prepared d2).stacks ∘ localPorts = (Local.prepared d).stacks ∘ localPorts := by
    funext i
    have h262 : localPorts i ≠ (262 : Fin 320) := by
      intro he; have hv := congrArg Fin.val he; change i.val = 262 at hv; omega
    have h263 : localPorts i ≠ (263 : Fin 320) := by
      intro he; have hv := congrArg Fin.val he; change i.val = 263 at hv; omega
    simp [Local.prepared, d2, d1, afterCopy, StackRoutines.copyStacks,
 Function.update_apply, h262, h263]
  have hlocal2 : SubexpConvolutionControl.ExecutesIn localCode Kl
      ((Local.prepared d2).stacks ∘ localPorts)
      (Function.update ((Local.prepared d2).stacks ∘ localPorts) 244
        (HornerProgram.encodePolynomial encode correction)) := by simpa only [hpre] using hlocal
  obtain ⟨n3, hn3, r3, h3⟩ := Local.command_run localCode d2
    (HornerProgram.encodePolynomial encode correction) Kl
    (by simpa [d2, d1] using hc 192 (by simp [cleanPorts]))
    (by simpa [d2, d1] using hc 193 (by simp [cleanPorts]))
    (by simpa [d2, d1] using hc 318 (by simp [cleanPorts, Scalar.cleanPorts])) hlocal2
  let d3 : Data := ⟨r3, Function.update d2.stacks 244 (HornerProgram.encodePolynomial encode correction)⟩
  have hlow2 : d2.stacks ∘ localPorts = d.stacks ∘ localPorts := by
    simp only [d2, d1, Scalar.lower_update_high _ 263 (by decide), Scalar.lower_update_high _ 262 (by decide)]
  have hm3 : ServiceSpec (d3.stacks ∘ localPorts) encode multiply mulOp Km := by
    apply CRTLocalProgram.serviceSpec_frame (show ServiceSpec (d2.stacks ∘ localPorts) encode multiply mulOp Km by rw [hlow2]; exact hm)
    exact lowFrame_update_outer d2.stacks 244 (by decide) _
  have ha3 : ServiceSpec (d3.stacks ∘ localPorts) encode add addOp Ka := by
    apply CRTLocalProgram.serviceSpec_frame (show ServiceSpec (d2.stacks ∘ localPorts) encode add addOp Ka by rw [hlow2]; exact ha)
    exact lowFrame_update_outer d2.stacks 244 (by decide) _
  have hhc3 : ∀ i ∈ Horner.cleanPorts, d3.stacks i = [] := by
    intro i hi
    simp only [Horner.cleanPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [d3, d2, d1] using hc _ (by simp [cleanPorts, Horner.cleanPorts])
  obtain ⟨n4, hn4, r4, h4⟩ := Horner.command_run encode multiply add mulOp addOp Km Ka W d3
    correction point zero hm3 ha3 hw (by simp [d3]) (by simp [d3, d2])
    (by simpa [d3, d2, d1] using hz)
    (by simpa [d3, d2, d1, hJ] using hcorr.symm) hhc3
  let d4 : Data := ⟨r4, Function.update (Function.update d3.stacks 244 []) 264 (encode value)⟩
  have hlow4 : d4.stacks ∘ localPorts = d.stacks ∘ localPorts := by
    have hz244 : d.stacks 244 = [] := hc 244 (by simp [cleanPorts, Scalar.cleanPorts])
    funext i
    have h262 : localPorts i ≠ (262 : Fin 320) := by
      intro he; have hv := congrArg Fin.val he; change i.val = 262 at hv; omega
    have h263 : localPorts i ≠ (263 : Fin 320) := by
      intro he; have hv := congrArg Fin.val he; change i.val = 263 at hv; omega
    have h264 : localPorts i ≠ (264 : Fin 320) := by
      intro he; have hv := congrArg Fin.val he; change i.val = 264 at hv; omega
    by_cases h244 : localPorts i = (244 : Fin 320)
    · simp [d4, d3, d2, d1, h244, hz244]
    · simp [d4, d3, d2, d1, h244, h262, h263, h264]
  have hsc4 : ∀ i ∈ Scalar.cleanPorts, d4.stacks i = [] := by
    intro i hi
    have hci := hc i (by simp only [cleanPorts, List.mem_append]; tauto)
    simp only [Scalar.cleanPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [d4, d3, d2, d1, hci]
  obtain ⟨n5, hn5, r5, h5⟩ := Scalar.accumulate_run encode multiply add mulOp addOp Km Ka W d4
    acc factor value point (by rw [hlow4]; exact hm) (by rw [hlow4]; exact ha) hw
    (by simpa [d4, d3, d2, d1] using hacc) (by simp [d4, d3, d2, d1])
    (by simp [d4]) (by simp [d4, d3, d2]) hsc4
  have hfinal : Function.update (Function.update (Function.update (Function.update d4.stacks
        261 (encode (addOp acc (mulOp factor value)))) 262 []) 263 []) 264 [] =
      Function.update d.stacks 261 (encode (addOp acc (mulOp factor value))) := by
    funext i
    by_cases h244 : i = 244 <;> by_cases h262 : i = 262 <;>
      by_cases h263 : i = 263 <;> by_cases h264 : i = 264 <;>
      simp [d4, d3, d2, d1, Function.update_apply, h244, h262, h263, h264,
        hc 244 (by simp [cleanPorts, Scalar.cleanPorts]), hc 262 (by simp [cleanPorts]),
        hc 263 (by simp [cleanPorts]), hc 264 (by simp [cleanPorts])]
  rw [hfinal] at h5
  have hrun := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  refine ⟨_, ?_, r5, hrun⟩
  have hh277 : (d2.stacks 277).length = J * W := by simpa [d2, d1] using h277
  have hh243 : (d2.stacks 243).length = J := by simp [d2, d1, hJ]
  rw [hh277, hh243] at hn3
  rw [hcorr] at hn4
  unfold budget
  omega

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Middle

end OAI.Algorithms
