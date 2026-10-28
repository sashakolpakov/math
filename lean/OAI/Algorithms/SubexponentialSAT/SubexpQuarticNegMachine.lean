import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticMachine

namespace OAI.Algorithms

/-! Componentwise negation uses four base-ring multiplications by a prepared
minus-one word. It does not invoke the 49-call quartic multiplication routine. -/

namespace SubexponentialSAT.SubexpQuarticNegMachine

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing SubexpQuarticMachine

def negCode : List (SubexpQuarticMachine.Instr 9) :=
  [⟨.mul, 5, 0, 4⟩, ⟨.mul, 6, 1, 4⟩, ⟨.mul, 7, 2, 4⟩, ⟨.mul, 8, 3, 4⟩]

def input {A : Type*} (bank : Fin 9 → A) : Quad A :=
  ⟨bank 0, bank 1, bank 2, bank 3⟩

def output {A : Type*} (bank : Fin 9 → A) : Quad A :=
  ⟨bank 5, bank 6, bank 7, bank 8⟩

def negateWords (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (minusOne : Word (baseWidth p μ)) (a : Quad (Word (baseWidth p μ))) :
    Quad (Word (baseWidth p μ)) :=
  ⟨(SubexpPreparedQuartic.wordMul p μ M a.c0 minusOne).1,
   (SubexpPreparedQuartic.wordMul p μ M a.c1 minusOne).1,
   (SubexpPreparedQuartic.wordMul p μ M a.c2 minusOne).1,
   (SubexpPreparedQuartic.wordMul p μ M a.c3 minusOne).1⟩

@[simp] theorem negCode_length : negCode.length = 4 := rfl

theorem negCode_correct (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (bank : Fin 9 → Word (baseWidth p μ)) :
    output (scriptEval p μ M negCode bank) = negateWords p μ M (bank 4) (input bank) := rfl

theorem negateWords_value (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (minusOne : Word (baseWidth p μ))
    (a : Quad (Word (baseWidth p μ))) (hone : wordValue p μ minusOne = -1) :
    (negateWords p μ M minusOne a).map (wordValue p μ) =
      (a.map (wordValue p μ)).map Neg.neg := by
  simp [negateWords, Quad.map, SubexpPreparedQuartic.wordMul_correct, hone]

theorem negateWords_quotient (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (minusOne : Word (baseWidth p μ))
    (a : Quad (Word (baseWidth p μ))) (hone : wordValue p μ minusOne = -1)
    (c : Fin 4 → ZMod (p^μ)) :
    quotientDenote c ((negateWords p μ M minusOne a).map (wordValue p μ)) =
      -quotientDenote c (a.map (wordValue p μ)) := by
  rw [negateWords_value p μ M minusOne a hone, quotientDenote_neg]

theorem negCode_frame (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (bank : Fin 9 → Word (baseWidth p μ))
    (j : Fin 9) (hj : j.val < 5) : scriptEval p μ M negCode bank j = bank j := by
  apply scriptEval_frame
  have hd : ∀ i ∈ negCode, 5 ≤ i.dst.val := by norm_num [negCode, Fin.coe_ofNat_eq_mod]
  intro i hi he
  have := hd i hi
  rw [he] at this
  omega

abbrev program : Program 8 18 (size (scriptCmd negCode) + 1) :=
  compiled (scriptCmd negCode) (bankPort 0) (bankPort 5)

theorem program_size : size (scriptCmd negCode) + 1 = 673 := rfl

def negatedState (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (regs : Fin 8 → Bool)
    (bank : Fin 9 → Word (baseWidth p μ)) : StructuredCalls.State 8 18 :=
  restingState regs (scriptEval p μ M negCode bank) M.bits

theorem program_run (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (regs : Fin 8 → Bool)
    (bank : Fin 9 → Word (baseWidth p μ)) :
    ∃ finalRegs, RunsIn program (24401 * (baseWidth p μ + 1)^2)
      ((restingState regs bank M.bits).withPC (some program.entry))
      ((negatedState p μ M finalRegs bank).withPC none) := by
  obtain ⟨n, rf, hn, he⟩ := script_run p μ M negCode regs bank
  refine ⟨rf, n + 1, ?_, compiled_halt_trace he _ _⟩
  have hs := Nat.le_mul_self (baseWidth p μ + 1)
  rw [← pow_two] at hs
  simp only [negCode_length] at hn
  omega

end SubexponentialSAT.SubexpQuarticNegMachine

end OAI.Algorithms
