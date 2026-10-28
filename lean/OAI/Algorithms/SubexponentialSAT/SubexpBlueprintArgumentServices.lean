import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpBlueprintBetaServices

namespace OAI.Algorithms

/-!
# Actual incidence-argument service inside the factor blueprint

The caller supplies the beta word and a physical coordinate-major Taylor
cache. The called program computes negative beta and serializes the raw Ce
literal. The interface records exactly the two changed Work fields.
-/

namespace SubexponentialSAT.SubexpBlueprintArgumentServices

open BitProgram StructuredCalls SubexpScanPrimitives SubexpBlueprintFactor
open SubexpBlueprintBetaServices
open SubexpLiftRing SubexpQuarticRing

attribute [local simp] Fin.coe_ofNat_eq_mod

private def argumentPortSource (i : Fin 128) : ℕ := match i.val with
  | 93 => 4 | 92 => 14 | 77 => 18 | 103 => 19 | 79 => 20
  | 104 => 24 | 94 => 25 | 95 => 26 | 106 => 27 | n => n

private theorem argumentPortSource_left (i : Fin 46) :
    argumentPortSource (argumentPorts i) = i.val := by
  fin_cases i <;> rfl

theorem argumentPorts_injective : Function.Injective argumentPorts := by
  intro i j h
  apply Fin.ext
  simpa only [argumentPortSource_left] using congrArg argumentPortSource h

def argumentWork (w : Work) (negative argument : List Bool) : Work :=
  {w with negative := negative, argument := argument}

/-- The producer's local data view, before interpreting any coefficient words. -/
def argumentNative (ctx : Context) (regs : Fin 8 → Bool) (w : Work) : State 8 46 :=
  SubexpArgumentProducer.state regs
    (SubexpQuarticFlatNeg.bankStore (SubexpQuarticFlatNeg.emptyBank ctx.targetMinusOne)
      ctx.targetModulus w.beta ctx.targetWidth w.negative)
    (SubexpArgumentProducer.extras w.taylor (List.replicate ctx.dimension true)
      (List.replicate ctx.indexWidth true) w.argument)

theorem project_argument (ctx : Context) (regs : Fin 8 → Bool) (w : Work) :
    projectState id argumentPorts (state ctx regs w) = argumentNative ctx regs w := by
  apply state_ext
  · rfl
  · funext i
    change (state ctx regs w).stacks (argumentPorts i) = _
    rw [state_stack_eq]
    fin_cases i <;>
      simp [argumentPorts, argumentNative, SubexpArgumentProducer.state,
        SubexpArgumentProducer.extras, Fin.addCases, SubexpQuarticFlatNeg.bankStore,
        SubexpQuarticFlatNeg.emptyBank]

theorem embed_argument (ctx : Context) (regs oldRegs : Fin 8 → Bool) (w : Work)
    (negative argument : List Bool) :
    embedState id argumentPorts (state ctx oldRegs w)
      (argumentNative ctx regs (argumentWork w negative argument)) =
      state ctx regs (argumentWork w negative argument) := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id argumentPorts_injective
  · intros; rfl
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i
    exact congrArg (fun d : State 8 46 => d.stacks i)
      (project_argument ctx regs (argumentWork w negative argument))
  · intro i hi
    have h103 : i ≠ 103 := fun h => hi ⟨19,h.symm⟩
    have h106 : i ≠ 106 := fun h => hi ⟨27,h.symm⟩
    simp only [state_stack_eq,argumentWork,h103,h106,ite_false]

theorem push_argument (ctx : Context) (regs : Fin 8 → Bool) (w : Work)
    (hargument : w.argument = []) :
    Eval (pushBit 106 false) 2 (state ctx regs w)
      (state ctx (Function.update regs 0 false) (argumentWork w w.negative [false])) := by
  let d := state ctx regs w
  have h := Eval.seq
    (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set 0 false) d))
    (Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push 106 0)
      ((StructuredProgram.Atom.set (s := 128) 0 false).eval d)))
  have he : (⟨Function.update d.regs 0 false,
      Function.update d.stacks 106 (false :: d.stacks 106)⟩ : State 8 128) =
      state ctx (Function.update regs 0 false) (argumentWork w w.negative [false]) := by
    apply state_ext
    · rfl
    · funext i
      by_cases hi : i = 106
      · subst i; simp [d,state_stack_eq,argumentWork,hargument]
      · simp [d,state_stack_eq,argumentWork,hi]
  simpa only [pushBit,atom,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr,
    Function.update_same,he] using h

/-- The complete enclosing service starts with no supplied negative word or
argument literal. All other Work fields and all Context data are preserved. -/
theorem computeArgument_eval (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ)
    (a : Quad (SubexpQuarticRing.Word (baseWidth p μ)))
    (one : SubexpQuarticRing.Word (baseWidth p μ))
    (columns : List (List (List Bool))) (B : ℕ)
    (ctx : Context) (regs : Fin 8 → Bool) (w : Work)
    (hmodulus : ctx.targetModulus = M.bits)
    (hminusOne : ctx.targetMinusOne = one.val)
    (hwidth : ctx.targetWidth.length = baseWidth p μ)
    (hdimension : ctx.dimension = columns.length)
    (hindex : ctx.indexWidth = B)
    (hbeta : w.beta = SubexpQuarticFlatNeg.flat a)
    (hnegative : w.negative = [])
    (htaylor : w.taylor = Encoding.encodeList id (SubexpCacheArgument.columnRecords columns))
    (hargument : w.argument = []) :
    let negative := SubexpQuarticNegMachine.negateWords p μ M one a
    let output := SubexpCacheArgument.resultBits (SubexpQuarticFlatNeg.flat a)
      (SubexpQuarticFlatNeg.flat negative) columns B [false]
    ∃ (n : ℕ) (rf : Fin 8 → Bool),
      n ≤ 25000*(baseWidth p μ+1)^2 +
        SubexpCacheArgument.totalCost (SubexpQuarticFlatNeg.flat a)
          (SubexpQuarticFlatNeg.flat negative) columns B + 4 ∧
      Eval computeArgument n (state ctx regs w)
        (state ctx rf (argumentWork w (SubexpQuarticFlatNeg.flat negative) output)) := by
  dsimp only
  let r0 := Function.update regs 0 false
  let negative := SubexpQuarticNegMachine.negateWords p μ M one a
  let output := SubexpCacheArgument.resultBits (SubexpQuarticFlatNeg.flat a)
    (SubexpQuarticFlatNeg.flat negative) columns B [false]
  have hp := push_argument ctx regs w hargument
  obtain ⟨rf,n,hn,ht⟩ := SubexpArgumentProducer.program_run p μ M a one
    ctx.targetWidth hwidth columns B r0
  have ht' : Trace SubexpArgumentProducer.program n
      ((argumentNative ctx r0 (argumentWork w w.negative [false])).withPC
        (some SubexpArgumentProducer.program.entry))
      ((argumentNative ctx rf (argumentWork w (SubexpQuarticFlatNeg.flat negative) output)).withPC none) := by
    simpa only [argumentNative,argumentWork,SubexpArgumentProducer.cacheExtra,
      SubexpQuarticFlatNeg.initialStore,SubexpQuarticFlatNeg.finalStore,
      hmodulus,hminusOne,hdimension,hindex,hbeta,hnegative,htaylor,output,negative] using ht
  have hc := eval_call_lifted SubexpArgumentProducer.program id argumentPorts
    (state ctx r0 w) Function.injective_id argumentPorts_injective ht'
  rw [embed_argument,embed_argument] at hc
  exact ⟨2+n,rf,by omega,hp.seq hc⟩

end SubexponentialSAT.SubexpBlueprintArgumentServices

end OAI.Algorithms
