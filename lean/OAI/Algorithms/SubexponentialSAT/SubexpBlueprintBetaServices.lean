import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpBlueprintFactorProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-!
# Concrete beta service inside the raw factor blueprint controller

The service copies the stored zero and point stream, invokes the actual
residue dot-product and canonical-lift program, and preserves all unrelated
blueprint work. Its result bytes are fixed independently of caller registers.
-/

namespace SubexponentialSAT.SubexpBlueprintBetaServices

open BitProgram StructuredCalls SubexpScanPrimitives SubexpBlueprintFactor
open SubexpInputBitProgram SubexpSelectedConversions SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

/-- A shared normalization rule for physical blueprint state proofs. -/
theorem state_stack_eq (ctx : Context) (regs : Fin 8 → Bool) (w : Work) (i : Fin 128) :
    (state ctx regs w).stacks i =
      if i = 66 then ctx.sourceModulus else if i = 73 then ctx.sourceReduction
      else if i = 74 then ctx.sourceWidth else if i = 77 then w.beta
      else if i = 79 then ctx.targetWidth else if i = 80 then w.origin
      else if i = 81 then w.pointCopy else if i = 90 then ctx.sourceZero
      else if i = 91 then ctx.pointStream else if i = 92 then ctx.targetModulus
      else if i = 93 then ctx.targetMinusOne else if i = 94 then List.replicate ctx.dimension true
      else if i = 95 then List.replicate ctx.indexWidth true else if i = 100 then w.input
      else if i = 103 then w.negative else if i = 104 then w.taylor
      else if i = 105 then w.coefficients else if i = 106 then w.argument
      else if i = 107 then w.payload else if i = 108 then w.scratch
      else if i = 109 then w.parser else if i = 110 then w.coordinate
      else if i = 111 then w.row else if i = 112 then w.factor else [] := by
  simp only [state]
  split <;> simp_all [Fin.ext_iff]

theorem betaPorts_injective : Function.Injective betaPorts := Fin.castAdd_injective _ _

def betaWork (w : Work) (beta origin point : List Bool) : Work :=
  { w with beta := beta, origin := origin, pointCopy := point }

theorem project_beta (ctx : Context) (regs : Fin 8 → Bool) (w : Work) :
    projectState id betaPorts (state ctx regs w) =
      sourceState regs ctx.sourceModulus ctx.sourceReduction ctx.sourceWidth ctx.targetWidth
        w.beta [] w.origin w.pointCopy := by
  apply state_ext
  · rfl
  · funext i
    change (state ctx regs w).stacks (betaPorts i) = _
    rw [state_stack_eq]
    by_cases h66 : i.val = 66
    · have : i = 66 := Fin.ext h66
      subst i; rfl
    by_cases h73 : i.val = 73
    · have : i = 73 := Fin.ext h73
      subst i; rfl
    by_cases h74 : i.val = 74
    · have : i = 74 := Fin.ext h74
      subst i; rfl
    by_cases h77 : i.val = 77
    · have : i = 77 := Fin.ext h77
      subst i; rfl
    by_cases h79 : i.val = 79
    · have : i = 79 := Fin.ext h79
      subst i; rfl
    by_cases h80 : i.val = 80
    · have : i = 80 := Fin.ext h80
      subst i; rfl
    by_cases h81 : i.val = 81
    · have : i = 81 := Fin.ext h81
      subst i; rfl
    have hi : i.val < 79 := by omega
    have hi80 : i.val < 80 := by omega
    have h90 : i.val ≠ 90 := by omega
    have h91 : i.val ≠ 91 := by omega
    have h92 : i.val ≠ 92 := by omega
    have h93 : i.val ≠ 93 := by omega
    have h94 : i.val ≠ 94 := by omega
    have h95 : i.val ≠ 95 := by omega
    have h100 : i.val ≠ 100 := by omega
    have h103 : i.val ≠ 103 := by omega
    have h104 : i.val ≠ 104 := by omega
    have h105 : i.val ≠ 105 := by omega
    have h106 : i.val ≠ 106 := by omega
    have h107 : i.val ≠ 107 := by omega
    have h108 : i.val ≠ 108 := by omega
    have h109 : i.val ≠ 109 := by omega
    have h110 : i.val ≠ 110 := by omega
    have h111 : i.val ≠ 111 := by omega
    have h112 : i.val ≠ 112 := by omega
    simp [betaPorts, sourceState, betaState, widen, SubexpDotControl.dotStore,
      Fin.ext_iff, h66, h73, h74, h77, h79, h80, h81, hi, hi80,
      h90, h91, h92, h93, h94, h95, h100, h103, h104, h105, h106, h107,
      h108, h109, h110, h111, h112]

theorem embed_beta (ctx : Context) (regs oldRegs : Fin 8 → Bool) (w : Work)
    (beta origin point : List Bool) :
    embedState id betaPorts (state ctx oldRegs w)
      (sourceState regs ctx.sourceModulus ctx.sourceReduction ctx.sourceWidth ctx.targetWidth
        beta [] origin point) = state ctx regs (betaWork w beta origin point) := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id betaPorts_injective
  · intros; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    have h := congrArg (fun d : State 8 82 => d.stacks i)
      (project_beta ctx regs (betaWork w beta origin point))
    exact h
  · intro i hi
    have h77 : i ≠ 77 := fun h => hi ⟨77, h.symm⟩
    have h80 : i ≠ 80 := fun h => hi ⟨80, h.symm⟩
    have h81 : i ≠ 81 := fun h => hi ⟨81, h.symm⟩
    simp only [state_stack_eq, betaWork, h77, h80, h81, ite_false]

theorem copy_zero (ctx : Context) (regs : Fin 8 → Bool) (w : Work)
    (hb : w.beta = []) (hs : w.scratch = []) :
    Eval (copy 90 77) (7 * ctx.sourceZero.length + 5) (state ctx regs w)
      (state ctx (readRegs regs 0 1 none) {w with beta := ctx.sourceZero}) := by
  have h := copy_eval (state ctx regs w) 90 77 108 0 1
    (by decide) (by decide) (by decide) (by decide) (by simp [state_stack_eq, hs])
  have he : afterCopy (state ctx regs w) 90 77 0 1 =
      state ctx (readRegs regs 0 1 none) {w with beta := ctx.sourceZero} := by
    apply state_ext
    · rfl
    · funext i
      by_cases hi : i = 77
      · subst i; simp [afterCopy, StackRoutines.copyStacks, state_stack_eq, hb]
      · simp [afterCopy, StackRoutines.copyStacks, state_stack_eq, hi]
  rw [he] at h
  have hlen : ((state ctx regs w).stacks (90 : Fin 128)).length =
      ctx.sourceZero.length := by simp [state_stack_eq]
  rw [hlen] at h
  simpa only [copy] using h

theorem copy_point (ctx : Context) (regs : Fin 8 → Bool) (w : Work)
    (hp : w.pointCopy = []) (hs : w.scratch = []) :
    Eval (copy 91 81) (7 * ctx.pointStream.length + 5) (state ctx regs w)
      (state ctx (readRegs regs 0 1 none) {w with pointCopy := ctx.pointStream}) := by
  have h := copy_eval (state ctx regs w) 91 81 108 0 1
    (by decide) (by decide) (by decide) (by decide) (by simp [state_stack_eq, hs])
  have he : afterCopy (state ctx regs w) 91 81 0 1 =
      state ctx (readRegs regs 0 1 none) {w with pointCopy := ctx.pointStream} := by
    apply state_ext
    · rfl
    · funext i
      by_cases hi : i = 81
      · subst i; simp [afterCopy, StackRoutines.copyStacks, state_stack_eq, hp]
      · simp [afterCopy, StackRoutines.copyStacks, state_stack_eq, hi]
  rw [he] at h
  have hlen : ((state ctx regs w).stacks (91 : Fin 128)).length =
      ctx.pointStream.length := by simp [state_stack_eq]
  rw [hlen] at h
  simpa only [copy] using h

/-- Complete local execution; all other Work and Context fields are preserved. -/
theorem computeBeta_eval {p D : ℕ} [Fact p.Prime]
    (source : Prepared p 0) (target : Prepared p D)
    (row x : Fin D → ResidueCode p) (ctx : Context) (regs : Fin 8 → Bool) (w : Work)
    (hm : ctx.sourceModulus = source.modulus.bits)
    (hr : ctx.sourceReduction = SubexpQuarticFlatMul.flat source.reduction)
    (hz : ctx.sourceZero = SubexpQuarticFlatMul.flat source.zero)
    (hx : ctx.pointStream = Encoding.encodeList SubexpQuarticFlatMul.flat ((List.finRange D).map x))
    (ho : w.origin = Encoding.encodeList SubexpQuarticFlatMul.flat ((List.finRange D).map row))
    (hsw : ctx.sourceWidth.length = baseWidth p 1)
    (htw : ctx.targetWidth.length = baseWidth p (D + 1))
    (hb : w.beta = []) (hp : w.pointCopy = []) (hsc : w.scratch = []) :
    ∃ (n : ℕ) (rf : Fin 8 → Bool),
      n ≤ 7 * ctx.sourceZero.length + 7 * ctx.pointStream.length + 10 + sourceSteps D p ∧
      Eval computeBeta n (state ctx regs w)
        (state ctx rf (betaWork w (SubexpQuarticFlatMul.flat (betaOutput source row x)) [] [])) ∧
      target.ring.decode (betaOutput source row x) =
        SubexpInputCode.beta (SubexpActualRing.residueSection p (D + 1) (Nat.succ_pos D)).lift
          (fun i => source.residueRing.decode (row i))
          (fun i => source.residueRing.decode (x i)) := by
  let r1 := readRegs regs 0 1 none
  let r2 := readRegs r1 0 1 none
  have h1 := copy_zero ctx regs w hb hsc
  have h2 := copy_point ctx r1 {w with beta := ctx.sourceZero} hp hsc
  obtain ⟨rf, ⟨n, hn, hrun⟩, hv⟩ :=
    source_execute_exact source target row x ctx.sourceWidth ctx.targetWidth [] [] [] hsw htw r2
  simp only [List.append_nil] at hrun
  rw [← hm, ← hr, ← hz, ← hx, ← ho] at hrun
  have hcall := eval_call_lifted sourceProgram id betaPorts (state ctx r2 w)
    Function.injective_id betaPorts_injective hrun
  rw [embed_beta, embed_beta] at hcall
  have hall := Eval.seq h1 (Eval.seq h2 hcall)
  refine ⟨_, rf, ?_, hall, hv⟩
  omega

end SubexponentialSAT.SubexpBlueprintBetaServices

end OAI.Algorithms
