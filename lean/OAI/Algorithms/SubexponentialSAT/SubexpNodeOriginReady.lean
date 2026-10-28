import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeCacheTyped
import OAI.Algorithms.SubexponentialSAT.SubexpNodeOriginExecution

namespace OAI.Algorithms

/-! Readiness for origin extraction follows from the actual cache-stage
stack equation, preserved source masters, and the cleared shared workspace. -/

namespace SubexponentialSAT.SubexpNodeOriginReady

open BitProgram StructuredCalls SubexpScanPrimitives SubexpLiftRing

abbrev Data := State 16 288
abbrev CacheData := State 16 256

structure Ready (d : Data) (modulus targetWidth sourceWidth cache : List Bool) : Prop where
  modulus : d.stacks 128 = modulus
  targetWidth : d.stacks 74 = targetWidth
  sourceWidth : d.stacks 129 = sourceWidth
  cache : d.stacks 102 = cache
  work : ∀ i : Fin 288, 138 ≤ i.val → i.val < 202 → d.stacks i = []
  output : d.stacks 227 = []

theorem Ready.invariant {d : Data} {modulus targetWidth sourceWidth cache : List Bool}
    (h : Ready d modulus targetWidth sourceWidth cache) :
    SubexpOriginMap.incidenceInvariant modulus targetWidth sourceWidth
      (SubexpNodeOriginStage.localState d) := by
  have low : ∀ i : Fin 14,
      (SubexpNodeOriginStage.localState d).stacks (SubexpOriginCalls.lowPort i) =
        if i = 5 then modulus else if i = 10 then targetWidth
        else if i = 11 then sourceWidth else [] := by
    intro i
    by_cases h5 : i = 5
    · subst i; exact h.modulus
    by_cases h10 : i = 10
    · subst i; exact h.targetWidth
    by_cases h11 : i = 11
    · subst i; exact h.sourceWidth
    have hn (j : Fin 32) (hj : i.val ≠ j.val) : SubexpOriginCalls.lowPort i ≠ j := by
      intro he
      exact hj (congrArg Fin.val he)
    have h5' : SubexpOriginCalls.lowPort i ≠ 5 := hn 5 (fun he => h5 (Fin.ext he))
    have h10' : SubexpOriginCalls.lowPort i ≠ 10 := hn 10 (fun he => h10 (Fin.ext he))
    have h11' : SubexpOriginCalls.lowPort i ≠ 11 := hn 11 (fun he => h11 (Fin.ext he))
    have h14' : SubexpOriginCalls.lowPort i ≠ 14 := hn 14 (by have := i.isLt; omega)
    have h24' : SubexpOriginCalls.lowPort i ≠ 24 := hn 24 (by have := i.isLt; omega)
    change d.stacks (SubexpNodeOriginStage.ports (SubexpOriginCalls.lowPort i)) = _
    simp only [SubexpNodeOriginStage.ports, h5', h10', h11', h14', h24',
      h5, h10, h11, ite_false]
    apply h.work
    · change 138 ≤ 138 + i.val; omega
    · change 138 + i.val < 202; have := i.isLt; omega
  refine ⟨⟨low, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  all_goals exact h.work _ (by decide) (by decide)

theorem Ready.cursor15 {d : Data} {m b w c : List Bool} (h : Ready d m b w c) :
    d.stacks 153 = [] := h.work _ (by decide) (by decide)
theorem Ready.cursor16 {d : Data} {m b w c : List Bool} (h : Ready d m b w c) :
    d.stacks 154 = [] := h.work _ (by decide) (by decide)
theorem Ready.accumulator {d : Data} {m b w c : List Bool} (h : Ready d m b w c) :
    d.stacks 161 = [] := h.work _ (by decide) (by decide)

/-- Source masters and empty work, before the real cache preparation copies. -/
structure CacheStatics (d : CacheData) (modulus targetWidth sourceWidth : List Bool) : Prop where
  modulus : d.stacks 128 = modulus
  targetWidth : d.stacks 10 = targetWidth
  sourceWidth : d.stacks 129 = sourceWidth
  work : ∀ i : Fin 256, 138 ≤ i.val → i.val < 202 → d.stacks i = []
  output : d.stacks 227 = []

def lower : Fin 256 → Fin 288 := Fin.castAdd 32
noncomputable def liftState (frame : Data) (small : CacheData) : Data :=
  embedState id lower frame small

theorem liftState_stack (frame : Data) (small : CacheData) (i : Fin 256) :
    (liftState frame small).stacks (lower i) = small.stacks i :=
  embedState_stack id lower frame small (Fin.castAdd_injective _ _) i

private theorem cacheOutput_high (s : Fin 256 → List Bool) (cache : List Bool)
    (i : Fin 256) (hi : 138 ≤ i.val) :
    (Function.update (SubexpNodeCacheSetup.preparedStacks s) 102 cache) i = s i := by
  have hn (j : Fin 256) (hj : j.val < 138) : i ≠ j := by
    intro he
    have := congrArg Fin.val he
    omega
  simp [SubexpNodeCacheSetup.preparedStacks,
    hn 102 (by decide), hn 81 (by decide), hn 74 (by decide), hn 73 (by decide),
    hn 66 (by decide), hn 101 (by decide), hn 100 (by decide)]

/-- The exact output equation proved by `NodeCacheTyped.command_eval`
establishes every origin extraction input port. -/
theorem ready_of_cache_stacks {d out : CacheData} (frame : Data)
    {modulus targetWidth sourceWidth cache : List Bool}
    (h : CacheStatics d modulus targetWidth sourceWidth)
    (hs : out.stacks = Function.update (SubexpNodeCacheSetup.preparedStacks d.stacks) 102 cache) :
    Ready (liftState frame out) modulus targetWidth sourceWidth cache := by
  have hp (i : Fin 256) := (liftState_stack frame out i).trans (congrFun hs i)
  constructor
  · simpa [SubexpNodeCacheSetup.preparedStacks, lower, h.modulus] using hp 128
  · simpa [SubexpNodeCacheSetup.preparedStacks, lower, h.targetWidth] using hp 74
  · simpa [SubexpNodeCacheSetup.preparedStacks, lower, h.sourceWidth] using hp 129
  · simpa [lower] using hp 102
  · intro i hi0 hi1
    let j : Fin 256 := ⟨i.val, by omega⟩
    have hij : lower j = i := Fin.ext rfl
    rw [← hij, hp, cacheOutput_high _ _ j hi0]
    exact h.work j hi0 hi1
  · have he := hp 227
    rw [cacheOutput_high _ _ 227 (by decide)] at he
    exact he.trans h.output

/-- Basis and bank construction may change 201 and 204 between cache
creation and origin extraction. Their checked final stack equation restores
the origin workspace and preserves all its masters. -/
theorem Ready.after_banks {d e : Data} {modulus targetWidth sourceWidth cache banks : List Bool}
    (h : Ready d modulus targetWidth sourceWidth cache)
    (hs : e.stacks = Function.update (Function.update d.stacks 201 []) 204 banks) :
    Ready e modulus targetWidth sourceWidth cache := by
  constructor
  · simpa [hs] using h.modulus
  · simpa [hs] using h.targetWidth
  · simpa [hs] using h.sourceWidth
  · simpa [hs] using h.cache
  · intro i hi0 hi1
    by_cases h201 : i = 201
    · subst i; simp [hs]
    have h204 : i ≠ 204 := by intro he; subst i; change 204 < 202 at hi1; omega
    simpa [hs, h201, h204] using h.work i hi0 hi1
  · simpa [hs] using h.output

variable (p μ : ℕ) [Fact p.Prime]
variable (source : SubexpSelectedConversions.Prepared p 0)
variable (target : SubexpPreparedQuartic.Modulus p μ)
variable (reduction theta : SubexpTaylorRow.Code p μ)

/-- The real cache computation supplies the stack equation used above;
the caller supplies only the stored masters and initially clear work. -/
theorem cache_command_ready (hμ : 0 < μ)
    (width blockWidth sourceWidth : List Bool) (hw : width.length = baseWidth p μ)
    (hblock : blockWidth.length = 4 * baseWidth p μ) (R N C : ℕ)
    (es : List (List (SubexpTaylorRowCorrectness.RowExpr p)))
    (hC : ∀ incidence ∈ es, incidence.length ≤ C)
    (d : CacheData) (frame : Data)
    (hmasters : CacheStatics d source.modulus.bits width sourceWidth)
    (h0 : d.stacks 0 = []) (h100 : d.stacks 100 = []) (h101 : d.stacks 101 = [])
    (h66 : d.stacks 66 = []) (h73 : d.stacks 73 = [])
    (h74 : d.stacks 74 = []) (h81 : d.stacks 81 = [])
    (hi : SubexpTaylorCacheMap.incidenceInvariant
      (SubexpHornerMachine.baseWords p μ target reduction theta width blockWidth) N
        (SubexpNodeCacheStage.localState (SubexpNodeCacheSetup.prepared d)))
    (hm : d.stacks 255 = SubexpTaylorCacheControl.encodeRows SubexpTaylorRow.flat
      (SubexpNodeCacheTyped.rows p μ source R es))
    (h102 : d.stacks 102 = []) (h103 : d.stacks 103 = [])
    (h104 : d.stacks 104 = []) (h108 : d.stacks 108 = []) :
    ∃ n ≤ SubexpNodeCacheSetup.prepareCost d +
      SubexpTaylorCacheMap.tableBudget es.length C (R + 1) N (baseWidth p μ),
      ∃ out : CacheData, Eval SubexpNodeCacheStage.command n d out ∧
        Ready (liftState frame out) source.modulus.bits width sourceWidth
          (SubexpOriginCacheSemantics.taylorBytes p μ source target reduction theta R N es) ∧
        out.stacks = Function.update (SubexpNodeCacheSetup.preparedStacks d.stacks) 102
          (SubexpOriginCacheSemantics.taylorBytes p μ source target reduction theta R N es) := by
  obtain ⟨n, hn, out, he, hs⟩ := SubexpNodeCacheTyped.command_eval p μ source target
    reduction theta hμ width blockWidth hw hblock R N C es hC d h0 h100 h101 h66 h73 h74 h81
      hi hm h102 h103 h104 h108
  exact ⟨n, hn, out, he, ready_of_cache_stacks frame hmasters hs, hs⟩

end SubexponentialSAT.SubexpNodeOriginReady

end OAI.Algorithms
