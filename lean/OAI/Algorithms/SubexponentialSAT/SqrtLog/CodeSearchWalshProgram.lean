import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgramChecks

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchWalshProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def good (q D h : ℕ) : Prop := q * D ≤ D + 2 * q * h ∧ 2 * q * h ≤ q * D + D
instance (q D h : ℕ) : Decidable (good q D h) := by unfold good; infer_instance
def pass (d : Data) : Bool := decide (good (BinaryArithmetic.toNat (d.stacks 0))
  (BinaryArithmetic.toNat (d.stacks 1)) (d.stacks 2).length)

def init (d : Data) : Data := ⟨Function.update d.regs 8 true, d.stacks⟩
theorem init_eval (d : Data) : Eval (.base (.atom (.set 8 true))) 1 d (init d) := by
  simpa [init, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using
    Eval.base (StructuredProgram.Eval.atom (.set (8 : Fin 9) true) d)

/-- Source-preserving Walsh check. The three inputs are q,D and a unary h word;
all other stacks start and finish empty. The answer is register8. -/
def command : Code := .seq prepare (.seq (.base (.atom (.set 8 true)))
  (.seq (check 0) (.seq (check 1) clearCount)))
def program := compiled command 0 0

theorem command_eval (d : Data) (hd : ∀ j : Fin 14, 3 ≤ j.val → d.stacks j = []) :
    ∃ t ≤ 700 * (2 * size d + 4)^2, ∃ z : Data,
      Eval command t d z ∧ z.regs 8 = pass d ∧ z.stacks = d.stacks := by
  obtain ⟨tp, htp, p, hp, hv3, hv4, hv5, hv6, hv7, hlen, hframe⟩ := prepare_eval d hd
  let a := init p
  have ha := init_eval p
  obtain ⟨b, hb, hbr, hbf, hbz⟩ := check_eval 0 a
  obtain ⟨c, hc, hcr, hcf, hcz⟩ := check_eval 1 b
  let z := cleared c
  have hz := clearCount_eval c
  have hb5 : b.stacks 5 = p.stacks 5 := hbf 5 (by decide) (by decide)
  have hb7 : b.stacks 7 = p.stacks 7 := hbf 7 (by decide) (by decide)
  have hc3 : c.stacks 3 = p.stacks 3 :=
    (hcf 3 (by decide) (by decide)).trans (hbf 3 (by decide) (by decide))
  have ht0 : 10 * max (a.stacks (pairPorts 0 0)).length (a.stacks (pairPorts 0 1)).length + 9 ≤
      10 * (2 * size d + 4) + 9 := by
    have h := max_le (hlen 6 (by decide) (by decide)) (hlen 4 (by decide) (by decide))
    change max (a.stacks (pairPorts 0 0)).length (a.stacks (pairPorts 0 1)).length ≤ _ at h
    omega
  have ht1 : 10 * max (b.stacks (pairPorts 1 0)).length (b.stacks (pairPorts 1 1)).length + 9 ≤
      10 * (2 * size d + 4) + 9 := by
    change 10 * max (b.stacks 7).length (b.stacks 5).length + 9 ≤ _
    rw [hb7, hb5]
    have h := max_le (hlen 7 (by decide) (by decide)) (hlen 5 (by decide) (by decide))
    omega
  have hcl : (c.stacks 3).length ≤ 2 * size d + 4 := by
    rw [hc3]; exact hlen 3 (by decide) (by decide)
  refine ⟨tp + (1 + ((10 * max (a.stacks (pairPorts 0 0)).length (a.stacks (pairPorts 0 1)).length + 9) +
    ((10 * max (b.stacks (pairPorts 1 0)).length (b.stacks (pairPorts 1 1)).length + 9) +
      (2 * (c.stacks 3).length + 3)))), ?_, z, hp.seq (ha.seq (hb.seq (hc.seq hz))), ?_, ?_⟩
  · nlinarith only [htp, ht0, ht1, hcl, Nat.zero_le (size d)]
  · have hpa : a.regs 8 = true := by simp [a, init]
    change b.regs 8 = (a.regs 8 && decide (BinaryArithmetic.toNat (a.stacks 4) ≤ BinaryArithmetic.toNat (a.stacks 6))) at hbr
    change c.regs 8 = (b.regs 8 && decide (BinaryArithmetic.toNat (b.stacks 5) ≤ BinaryArithmetic.toNat (b.stacks 7))) at hcr
    have hcv : c.regs 8 = pass d := by
      rw [hcr, hbr, hpa, hb5, hb7]
      change ((true && decide (BinaryArithmetic.toNat (p.stacks 4) ≤ BinaryArithmetic.toNat (p.stacks 6))) &&
        decide (BinaryArithmetic.toNat (p.stacks 5) ≤ BinaryArithmetic.toNat (p.stacks 7))) = pass d
      rw [hv4, hv5, hv6, hv7]
      unfold pass good
      by_cases h₁ : BinaryArithmetic.toNat (d.stacks 0) * BinaryArithmetic.toNat (d.stacks 1) ≤
          BinaryArithmetic.toNat (d.stacks 1) +
            2 * BinaryArithmetic.toNat (d.stacks 0) * (d.stacks 2).length
      · by_cases h₂ : 2 * BinaryArithmetic.toNat (d.stacks 0) * (d.stacks 2).length ≤
            BinaryArithmetic.toNat (d.stacks 0) * BinaryArithmetic.toNat (d.stacks 1) +
              BinaryArithmetic.toNat (d.stacks 1) <;> simp [h₁, h₂]
      · simp [h₁]
    simpa [z, cleared, readRegs] using hcv
  · funext j
    by_cases hj3 : j = 3
    · subst j; simp [z, cleared, hd 3 (by decide)]
    have hzc : z.stacks j = c.stacks j := by simp [z, cleared, hj3]
    rw [hzc]
    by_cases hj5 : j = 5
    · subst j; exact (hcz 1).trans (hd 5 (by decide)).symm
    by_cases hj7 : j = 7
    · subst j; exact (hcz 0).trans (hd 7 (by decide)).symm
    rw [hcf j hj7 hj5]
    by_cases hj4 : j = 4
    · subst j; exact (hbz 1).trans (hd 4 (by decide)).symm
    by_cases hj6 : j = 6
    · subst j; exact (hbz 0).trans (hd 6 (by decide)).symm
    rw [hbf j hj6 hj4]
    apply hframe j
    have h3 : j.val ≠ 3 := by intro h; apply hj3; exact Fin.ext h
    have h4 : j.val ≠ 4 := by intro h; apply hj4; exact Fin.ext h
    have h5 : j.val ≠ 5 := by intro h; apply hj5; exact Fin.ext h
    have h6 : j.val ≠ 6 := by intro h; apply hj6; exact Fin.ext h
    have h7 : j.val ≠ 7 := by intro h; apply hj7; exact Fin.ext h
    omega

end SubexponentialSAT.SqrtLog.CodeSearchWalshProgram

end OAI.Algorithms
