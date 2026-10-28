import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixInterpreter
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Small, extensional frame facts for the row interpreter. These proofs
split only its four control ports; they never enumerate the 256-stack frame. -/

namespace SubexponentialSAT.SubexpRowPostfixInterpreter

open BitProgram StructuredCalls
open SubexpPostfixGlobal (reindexCfg)
open SubexpPostfixInterpreter (cfg)

def contextStore (context : Fin 252 → List Bool) : Fin 256 → List Bool :=
  (physicalCfg (l := 1) none false false false [] [] [] context).stacks

theorem physicalCfg_frame {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 252 → List Bool)
    (i : Fin 256) (h26 : i ≠ 26) (h28 : i ≠ 28) (h27 : i ≠ 27) :
    (physicalCfg pc v p op code depth operands context).stacks i = contextStore context i := by
  obtain ⟨j, rfl⟩ := ports.surjective i
  revert h26 h28 h27
  refine Fin.addCases (m := 4) (n := 252) ?_ ?_ j
  · intro k
    fin_cases k
    · intro h _ _; exact False.elim (h ports_zero)
    · intro _ h _; exact False.elim (h ports_one)
    · intro _ _ h; exact False.elim (h ports_two)
    · intro _ _ _
      simp [physicalCfg, contextStore, reindexCfg, cfg, Fin.addCases,
        SubexpPostfixControl.quadruple]
  · intro k _ _ _
    simp [physicalCfg, contextStore, reindexCfg, cfg]

private theorem local_update {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth old new : List Bool) (context : Fin 252 → List Bool) :
    (cfg (r := 13) pc v p op code depth new context).stacks =
      Function.update (cfg (r := 13) pc v p op code depth old context).stacks
        (2 : Fin 256) new := by
  funext i
  refine Fin.addCases (m := 4) (n := 252) ?_ ?_ i
  · intro j
    fin_cases j <;> rfl
  · intro j
    have hj : Fin.natAdd 4 j ≠ (2 : Fin 256) := by
      intro h
      have hv := congrArg Fin.val h
      change 4 + j.val = 2 at hv
      omega
    simp [cfg, hj]

theorem physicalCfg_update {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth old new : List Bool) (context : Fin 252 → List Bool) :
    (physicalCfg pc v p op code depth new context).stacks =
      Function.update (physicalCfg pc v p op code depth old context).stacks 27 new := by
  funext i
  have hi : ports.symm i = (2 : Fin 256) ↔ i = 27 := by
    constructor
    · intro h
      have hh := congrArg ports h
      simpa only [Equiv.apply_symm_apply, ports_two] using hh
    · intro h
      subst i
      exact ports_symm_27
  change (cfg (r := 13) pc v p op code depth new context).stacks (ports.symm i) = _
  rw [local_update pc v p op code depth old new context]
  simp only [Function.update_apply, hi, physicalCfg, reindexCfg]

theorem physicalCfg_false_regs {l : ℕ} (pc : Option (Fin l))
    (code depth operands : List Bool) (context : Fin 252 → List Bool) :
    (physicalCfg pc false false false code depth operands context).regs = fun _ => false := by
  funext i
  refine Fin.addCases (m := 3) (n := 13) ?_ ?_ i
  · intro j; fin_cases j <;> rfl
  · intro j; simp [physicalCfg, reindexCfg, cfg]

/-- The framed service endpoint is exactly the interpreter's next boundary. -/
theorem physicalCfg_after {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth old new : List Bool) (context : Fin 252 → List Bool) :
    ((⟨fun _ => false,
      Function.update (physicalCfg pc v p op code depth old context).stacks 27 new⟩ :
      State 16 256).withPC (l := l) none) =
      physicalCfg (l := l) none false false false code depth new context := by
  have hs := physicalCfg_update pc v p op code depth old new context
  have hregs := physicalCfg_false_regs (l := l) none code depth new context
  apply congrArg₂ (Cfg.mk none)
  · exact hregs.symm
  · exact hs.symm

end SubexponentialSAT.SubexpRowPostfixInterpreter

end OAI.Algorithms
