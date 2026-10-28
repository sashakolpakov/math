import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramExecution

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

theorem localCommand_run {C P : Type*} (s : Store)
    (encC : C → List Bool) (encP : P → List Bool)
    (constant linear : C → P) (sm sa pm pa : Code)
    (cm ca : C → C → C) (mulP addP : P → P → P)
    (Km Ka Kp Kap W V J : ℕ) (hW : 0 < W)
    (hsm : ServiceSpec s encC sm cm Km) (hsa : ServiceSpec s encC sa ca Ka)
    (hpm : ServiceSpec s encP pm mulP Kp) (hpa : ServiceSpec s encP pa addP Kap)
    (hcwidth : ∀ c, (encC c).length = W) (hpwidth : ∀ p, (encP p).length ≤ V)
    (zero one minusOne theta c : C) (cs : List C) (jet : P) (rest : List Bool)
    (hconstant : ∀ a, encP (constant a) =
      DensePolynomialProgram.Constructor.Counter.paddedBits W (encC a) (encC zero) J)
    (hlinear : ∀ a, encP (linear a) =
      DensePolynomialProgram.Constructor.Counter.paddedBits W (encC a) (encC one) J)
    (hzero : s 104 = encC zero) (hzeroBits : encC zero = List.replicate W false)
    (hone : s 207 = encC one) (hminus : s 211 = encC minusOne)
    (htheta : s 213 = encC theta) (hcs : s 214 = cs.flatMap encC)
    (hJ : s 243 = List.replicate J true) (hjet : s 225 = encP jet)
    (hpolyZero : s 192 = encP (constant zero))
    (hclean : ∀ i ∈ localWork, s i = [])
    (hhead : 0 < J → encP ((cs.eraseIdx (s 216).length).foldl
      (localUpdate cm ca mulP linear theta minusOne J) (constant one)) = encC c ++ rest) :
    let factor := (cs.eraseIdx (s 216).length).foldl
      (localUpdate cm ca mulP linear theta minusOne J) (constant one)
    let inv := inverseValue cm ca zero one minusOne c (s 209).length (s 212).length
    let out := if J = 0 then [] else encP (correctionValue mulP addP (constant zero) (constant one)
        (constant (cm inv minusOne)) (constant inv) factor jet J)
    ExecutesIn (localCommand sm sa pm pa)
      (localBudget cs.length (s 216).length (s 209).length (s 212).length J Km Ka Kp Kap W V)
      s (Function.update s 244 out) := by
  dsimp only
  have hbudget : 2 ≤ localBudget cs.length (s 216).length (s 209).length
      (s 212).length J Km Ka Kp Kap W V := by unfold localBudget; omega
  by_cases hJ0 : J = 0
  · have hskip : ExecutesIn (.base .skip) 0 s s := by
      intro regs
      exact ⟨0, regs, le_rfl, .base (.skip _)⟩
    have h := SubexpNodeScanControl.branch_false 243 15 (positiveLocal sm sa pm pa)
      (.base .skip) 0 s s (by simp [hJ, hJ0]) hskip
    have he : Function.update s 244 [] = s :=
      Function.update_eq_self_iff.mpr (hclean 244 (by simp [localWork])).symm
    change ExecutesIn (.seq (test 243 15)
      (.ite 15 (positiveLocal sm sa pm pa) (.base .skip))) _ _ _
    simpa [hJ0, he] using h.mono hbudget
  · have hpos : 0 < J := Nat.pos_of_ne_zero hJ0
    have hp := positiveLocal_run s encC encP constant linear sm sa pm pa cm ca mulP addP
      Km Ka Kp Kap W V J hW hsm hsa hpm hpa hcwidth hpwidth zero one minusOne theta c cs jet rest
      hconstant hlinear hzero hzeroBits hone hminus htheta hcs hJ hjet hpolyZero hclean (hhead hpos)
    have h := SubexpNodeScanControl.branch_true 243 15 (positiveLocal sm sa pm pa)
      (.base .skip) _ _ _ (by simp [hJ, hpos]) hp
    change ExecutesIn (.seq (test 243 15)
      (.ite 15 (positiveLocal sm sa pm pa) (.base .skip))) _ _ _
    simpa [hJ0, Nat.sub_add_cancel hbudget] using h

/-- Transfer an already proved local-command trace to the finite compiled
program. The preceding theorem supplies the trace without an execution oracle. -/
theorem localProgram_run_of_command (sm sa pm pa : Code) (K : ℕ)
    (s : Store) (out : List Bool)
    (h : ExecutesIn (localCommand sm sa pm pa) K s (Function.update s 244 out))
    (regs : Fin 16 → Bool) :
    ∃ finalRegs, RunsIn (localProgram sm sa pm pa) (K + 1)
      ((⟨regs, s⟩ : Data).withPC (some (localProgram sm sa pm pa).entry))
      ((⟨finalRegs, Function.update s 244 out⟩ : Data).withPC none) := by
  obtain ⟨n, finalRegs, hn, he⟩ := h regs
  exact ⟨finalRegs, n + 1, by omega, compiled_halt_trace he 225 244⟩

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
