import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeCacheSetup
import OAI.Algorithms.SubexponentialSAT.SubexpNodeMomentLoop
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorCacheMap

namespace OAI.Algorithms

/-!
# Installing the actual Taylor cache without clobbering dense metadata

The cache's temporary local ports 5, 10, 25 and 109 are moved to 112--115.
The dense modulus, scalar width, slot master and dimension therefore remain
outside the cache's instruction image. All copied inputs come from the
concrete preparation program, and the cache result comes from CacheMap's
actual nested traversal.
-/

namespace SubexponentialSAT.SubexpNodeCacheStage

open BitProgram StructuredCalls SubexpScanPrimitives SubexpLiftRing

abbrev Data := State 16 256

def regPorts : Fin 14 → Fin 16 := Fin.castAdd 2

def stackPorts (i : Fin 112) : Fin 256 :=
  if i = 5 then 112 else if i = 10 then 113 else if i = 25 then 114 else
    if i = 109 then 115 else ⟨i.val, by omega⟩

theorem regPorts_injective : Function.Injective regPorts := Fin.castAdd_injective _ _
theorem stackPorts_injective : Function.Injective stackPorts := by
  intro i j he
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  have hv := congrArg Fin.val he
  simp only [stackPorts] at hv
  split_ifs at hv <;> simp_all only [Fin.coe_ofNat_eq_mod] <;> omega

@[simp] theorem stackPorts_output : stackPorts 102 = 102 := rfl
@[simp] theorem stackPorts_rows : stackPorts 100 = 100 := rfl

def localState (d : Data) : SubexpTaylorCacheCalls.Data :=
  ⟨d.regs ∘ regPorts, d.stacks ∘ stackPorts⟩

theorem localState_embed (d : Data) :
    embedState regPorts stackPorts d (localState d) = d := by
  apply embedState_eq _ _ regPorts_injective stackPorts_injective
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl

theorem output_embed (d : Data) (regs : Fin 14 → Bool) (bits : List Bool) :
    (embedState regPorts stackPorts d
      (⟨regs, Function.update (localState d).stacks 102 bits⟩ : SubexpTaylorCacheCalls.Data)).stacks =
        Function.update d.stacks 102 bits := by
  funext j
  by_cases hj : ∃ i, stackPorts i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [embedState_stack _ _ _ _ stackPorts_injective]
    have h102 : stackPorts i = 102 ↔ i = 102 := by
      change stackPorts i = stackPorts 102 ↔ i = 102
      exact stackPorts_injective.eq_iff
    simp [Function.update_apply, h102, localState]
  · rw [embedState_stack_frame _ _ _ _ j hj]
    have h102 : j ≠ 102 := by
      intro he
      exact hj ⟨102, he.symm⟩
    simp [h102]

abbrev cacheCall : Cmd 16 256 :=
  .call (ProgramLinking.liftProgram SubexpTaylorCacheControl.program regPorts stackPorts)

abbrev command : Cmd 16 256 := .seq SubexpNodeCacheSetup.prepare cacheCall
abbrev program : Program 16 256 (size command + 1) := compiled command 255 102
def stage : SubexpNodeMomentLoop.Stage := ⟨_, program⟩

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

theorem cache_eval (hμ : 0 < μ) (t theta : SubexpTaylorRow.Code p μ)
    (width blockWidth : List Bool) (hw : width.length = baseWidth p μ)
    (hblock : blockWidth.length = 4 * baseWidth p μ) (N C R : ℕ)
    (rows : List (List (List (SubexpTaylorRow.Code p μ))))
    (hC : ∀ coordinates ∈ rows, coordinates.length ≤ C)
    (hR : ∀ coordinates ∈ rows, ∀ P ∈ coordinates, P.length ≤ R)
    (d : Data)
    (hi : SubexpTaylorCacheMap.incidenceInvariant
      (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) N (localState d))
    (hm : d.stacks 100 = SubexpTaylorCacheControl.encodeRows SubexpTaylorRow.flat rows)
    (h102 : d.stacks 102 = []) (h103 : d.stacks 103 = [])
    (h104 : d.stacks 104 = []) (h108 : d.stacks 108 = []) :
    ∃ n ≤ SubexpTaylorCacheMap.tableBudget rows.length C R N (baseWidth p μ),
      ∃ out : Data, Eval cacheCall n d out ∧
      out.stacks = Function.update d.stacks 102
        (SubexpTaylorCacheControl.encodeCache SubexpTaylorRow.flat
          (SubexpTaylorCacheMap.caches p μ M t theta N rows)) := by
  obtain ⟨n, hn, regs, ht⟩ := SubexpTaylorCacheMap.program_trace p μ M hμ t theta
    width blockWidth hw hblock N C R rows hC hR (localState d) hi hm h102 h103 h104 h108
  let result : SubexpTaylorCacheCalls.Data := ⟨regs, Function.update (localState d).stacks 102
    (SubexpTaylorCacheControl.encodeCache SubexpTaylorRow.flat
      (SubexpTaylorCacheMap.caches p μ M t theta N rows))⟩
  refine ⟨n, hn, embedState regPorts stackPorts d result, ?_, output_embed d regs _⟩
  have he := eval_call_lifted SubexpTaylorCacheControl.program regPorts stackPorts d
    regPorts_injective stackPorts_injective ht
  simpa only [cacheCall, localState_embed] using he

/-- The row master is physically copied before the real nested cache map.
The remaining invariant states only the prepared workspace layout. -/
theorem command_eval (hμ : 0 < μ) (t theta : SubexpTaylorRow.Code p μ)
    (width blockWidth : List Bool) (hw : width.length = baseWidth p μ)
    (hblock : blockWidth.length = 4 * baseWidth p μ) (N C R : ℕ)
    (rows : List (List (List (SubexpTaylorRow.Code p μ))))
    (hC : ∀ coordinates ∈ rows, coordinates.length ≤ C)
    (hR : ∀ coordinates ∈ rows, ∀ P ∈ coordinates, P.length ≤ R)
    (d : Data) (h0 : d.stacks 0 = [])
    (h100 : d.stacks 100 = []) (h101 : d.stacks 101 = [])
    (h66 : d.stacks 66 = []) (h73 : d.stacks 73 = [])
    (h74 : d.stacks 74 = []) (h81 : d.stacks 81 = [])
    (hi : SubexpTaylorCacheMap.incidenceInvariant
      (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) N
        (localState (SubexpNodeCacheSetup.prepared d)))
    (hm : d.stacks 255 = SubexpTaylorCacheControl.encodeRows SubexpTaylorRow.flat rows)
    (h102 : d.stacks 102 = []) (h103 : d.stacks 103 = [])
    (h104 : d.stacks 104 = []) (h108 : d.stacks 108 = []) :
    ∃ n ≤ SubexpNodeCacheSetup.prepareCost d +
      SubexpTaylorCacheMap.tableBudget rows.length C R N (baseWidth p μ),
      ∃ out : Data, Eval command n d out ∧
      out.stacks = Function.update (SubexpNodeCacheSetup.preparedStacks d.stacks) 102
        (SubexpTaylorCacheControl.encodeCache SubexpTaylorRow.flat
          (SubexpTaylorCacheMap.caches p μ M t theta N rows)) := by
  have hp := SubexpNodeCacheSetup.prepare_eval d h0 h100 h101 h66 h73 h74 h81
  obtain ⟨n, hn, out, he, hs⟩ := cache_eval p μ M hμ t theta width blockWidth hw hblock
    N C R rows hC hR (SubexpNodeCacheSetup.prepared d) hi
    (by simpa [SubexpNodeCacheSetup.prepared, SubexpNodeCacheSetup.preparedStacks] using hm)
    (by simpa [SubexpNodeCacheSetup.prepared, SubexpNodeCacheSetup.preparedStacks] using h102)
    (by simpa [SubexpNodeCacheSetup.prepared, SubexpNodeCacheSetup.preparedStacks] using h103)
    (by simpa [SubexpNodeCacheSetup.prepared, SubexpNodeCacheSetup.preparedStacks] using h104)
    (by simpa [SubexpNodeCacheSetup.prepared, SubexpNodeCacheSetup.preparedStacks] using h108)
  exact ⟨_, Nat.add_le_add_left hn _, out, hp.seq he, hs⟩

end SubexponentialSAT.SubexpNodeCacheStage

end OAI.Algorithms
