import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramModel

namespace OAI.Algorithms

/-! All local computation is now composed: native plans and pairs, actual
word selection, and the native layout metadata suffix. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput

def core : Code := .seq produce (.seq PackingLoaderProgram.command (.seq selection suffix))
def coreProgram := compiled core 32 63

def planStore (outside : Store) (p : Problem) :=
  Function.update outside 61 (planBits p.scopes p.n p.mask)
def loadedStore (outside : Store) (p : Problem) :=
  Function.update (planStore outside p) 60 (Scan.scopeBits p.scopes)
def selectedStore (outside : Store) (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :=
  Function.update (cached (loadedStore outside p) (List.replicate (p.Q*p.r) true)
    (ProgramEncoding.encodeRecords (AssignmentAlphabetSemantics.wordBytes p.r p.Q)))
      62 ((p.words a tail).map ReadPlan.encodeWord).flatten
noncomputable def outputStore (outside : Store) (p : Problem)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :=
  Function.update (selectedStore outside p a tail) 63 (p.spec a tail).suffix.metadata

def ready (outside : Store) (p : Problem) (regs : Fin 16 → Bool) : Small :=
  readyLocal regs p.r p.Q p.n p.factors (PairScoreProgram.pairRecords p.raw)
    (outside 56) (outside 57) (outside 58) (outside 59)

noncomputable def coreBudget (outside : Store) (p : Problem)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :=
  produceBudget p.scopes p.n p.mask +
  PackingLoaderProgram.budget (planStore outside p) (Scan.scopeBits p.scopes) p.n p.mask.length
    p.factors (PairScoreProgram.pairRecords p.raw) +
  selectionBudget (ready outside p (fun _=>false)) ((p.words a tail).map ReadPlan.encodeWord)
    (PackingProgram.Assembly.Scope.cost p.scopes p.n p.mask a tail p.s
      (outside 56) (outside 57) (outside 58) (outside 59)) +
  suffixBudget (selectedStore outside p a tail) (p.spec a tail)

theorem core_eval (outside : Store) (p : Problem) (hp : Parameters outside p)
    (hw : Workspace outside) (regs : Fin 16 → Bool)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (hrows : (a::tail).map ReadPlan.encodeWord=AssignmentAlphabetSemantics.wordBytes p.r p.Q)
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) :
    ∃ t rf, t+1 ≤ coreBudget outside p a tail ∧ Eval core t
      (framed outside (Install.input regs p.scopes p.n p.mask))
      (framed (outputStore outside p a tail) (⟨rf,fun _=>[]⟩ : Small)) := by
  let : NeZero p.r := ⟨Nat.ne_of_gt p.hr⟩
  obtain ⟨tp,rp,htp,hpRun⟩ := produce_eval outside regs p.scopes p.n p.mask hw.temp hw.plans
  obtain ⟨tl,rl,htl,hl⟩ := PackingLoaderProgram.command_eval (planStore outside p) rp
    (Scan.scopeBits p.scopes) p.n p.mask.length p.factors (PairScoreProgram.pairRecords p.raw)
    (by simpa [planStore] using hw.scopes)
    (by simpa [planStore,hp.radius] using p.hr)
  have hinput : rawInput (planStore outside p) rp (Scan.scopeBits p.scopes) p.n
      p.mask.length p.factors (PairScoreProgram.pairRecords p.raw) =
      framed (planStore outside p) (Endpoint.result rp p.scopes p.n p.mask) := rfl
  have hl' : Eval PackingLoaderProgram.command tl
      (framed (planStore outside p) (Endpoint.result rp p.scopes p.n p.mask))
      (framed (loadedStore outside p) (ready outside p rl)) := by
    rw [← hinput]
    simpa [loadedStore,planStore,ready,
      Problem.factors,Problem.raw,PackingProgram.Assembly.Scope.raw,hp.radius,hp.coordinate]
      using hl
  have hm := ready_memory rl a tail hrows p.n p.factors
    (PairScoreProgram.pairRecords p.raw) (outside 56) (outside 57) (outside 58) (outside 59)
  have hc := ready_remaining rl p.r p.Q p.n p.factors
    (PairScoreProgram.pairRecords p.raw) (outside 56) (outside 57) (outside 58) (outside 59)
  have he := ready_high rl a tail hrows p.n p.factors p.raw
    (outside 56) (outside 57) (outside 58) (outside 59)
  obtain ⟨ts,rs,hts,hsRun⟩ := selection_eval (loadedStore outside p) (ready outside p rl)
    (by simpa [loadedStore,planStore] using hw.temp)
    (by simpa [loadedStore,planStore] using hw.width)
    (by simpa [loadedStore,planStore] using hw.alphabet)
    (by simpa [loadedStore,planStore] using hw.words)
    p.scopes p.n p.mask p.mask_le a tail haN haC p.s p.hs
    (by simpa [loadedStore,planStore] using hp.ambient)
    (by simpa [loadedStore,planStore] using hp.epsilon)
    (by simpa [loadedStore,planStore,Problem.incidences] using hp.incidence)
    (by simpa [loadedStore,planStore] using hp.radius)
    hm hc (by simpa [loadedStore,planStore,ready,PackingProgram.Assembly.Scope.env,Problem.raw,
      Problem.factors] using he)
  have h10 : (ready outside p rl).stacks 10=List.replicate (p.Q*p.r) true := by
    simp [ready,readyLocal,AssignmentInitProgram.outputState,AssignmentInitProgram.state,
      PackingLoaderProgram.context,AssignmentInputProgram.context,AssignmentInputProgram.unary]
  have h39 : (ready outside p rl).stacks 39=
      ProgramEncoding.encodeRecords (AssignmentAlphabetSemantics.wordBytes p.r p.Q) := by
    simp [ready,readyLocal,AssignmentInitProgram.outputState,AssignmentInitProgram.state,
      PackingLoaderProgram.context,AssignmentInputProgram.context]
  have hsRun' : Eval selection ts (framed (loadedStore outside p) (ready outside p rl))
      (framed (selectedStore outside p a tail) (⟨rs,fun _=>[]⟩ : Small)) := by
    simpa only [h10,h39,selectedStore,Problem.words,PackingProgram.Assembly.Scope.rows] using hsRun
  obtain ⟨tf,rf,htf,hf⟩ := suffix_eval (selectedStore outside p a tail) rs (p.spec a tail)
    (p.spec_depth a tail)
    (by simpa [selectedStore,cached,loadedStore,planStore] using hw.temp)
    (by simpa [selectedStore,cached,loadedStore,planStore] using hw.metadata)
    (by simpa [selectedStore,cached,loadedStore,planStore] using hp.incidence)
    (by simp [selectedStore,cached])
    (by simp [selectedStore,cached])
    (by rw [p.spec_plans]; simp [selectedStore,cached,loadedStore,planStore])
    (by simp [selectedStore])
  refine ⟨tp+(tl+(ts+tf)),rf,?_,hpRun.seq (hl'.seq (hsRun'.seq hf))⟩
  have hreadyBudget (rows : List (List Bool)) (cost : ℕ) :
      selectionBudget (ready outside p rl) rows cost =
        selectionBudget (ready outside p (fun _=>false)) rows cost := rfl
  rw [hreadyBudget] at hts
  have hts' : ts ≤ selectionBudget (ready outside p (fun _=>false))
      ((p.words a tail).map ReadPlan.encodeWord)
      (PackingProgram.Assembly.Scope.cost p.scopes p.n p.mask a tail p.s
        (outside 56) (outside 57) (outside 58) (outside 59)) := by
    simpa [selectionBudget,selectionSize,dataMass,ready,loadedStore,planStore,
      Problem.words,PackingProgram.Assembly.Scope.rows] using hts
  unfold coreBudget
  omega

theorem core_run (outside : Store) (p : Problem) (hp : Parameters outside p)
    (hw : Workspace outside) (regs : Fin 16 → Bool)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (hrows : (a::tail).map ReadPlan.encodeWord=AssignmentAlphabetSemantics.wordBytes p.r p.Q)
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) :
    ∃ rf, RunsIn coreProgram (coreBudget outside p a tail)
      ((framed outside (Install.input regs p.scopes p.n p.mask)).withPC (some coreProgram.entry))
      ((framed (outputStore outside p a tail) (⟨rf,fun _=>[]⟩ : Small)).withPC none) := by
  obtain ⟨t,rf,ht,he⟩ := core_eval outside p hp hw regs a tail hrows haN haC
  exact ⟨rf,t+1,ht,compiled_halt_trace he 32 63⟩

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
