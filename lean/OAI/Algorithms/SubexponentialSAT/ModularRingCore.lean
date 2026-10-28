import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ModularDivisionPrograms
import OAI.Algorithms.SubexponentialSAT.BinaryPrograms

namespace OAI.Algorithms

/-! Fixed Boolean-stack programs for arithmetic with a supplied binary modulus. -/

namespace SubexponentialSAT.ModularRingPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.ProgramLinking SubexponentialSAT.StackRoutines
open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularDivisionPrograms

theorem cfg_ext {r s l : ℕ} {a b : Cfg r s l}
    (hp : a.pc = b.pc) (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  simp_all

theorem embed_ports {s S l : ℕ}
    (port : Fin s → Fin S) (hinj : Function.Injective port)
    (pc : Option (Fin l)) (regs frameRegs : Fin 8 → Bool)
    (localStk : Fin s → List Bool) (frame target : Fin S → List Bool)
    (hport : ∀ i, target (port i) = localStk i)
    (hframe : ∀ i, (¬ ∃ j, port j = i) → target i = frame i) :
    embedCfg id port id none (⟨none, frameRegs, frame⟩ : Cfg 8 S l)
      ⟨pc, regs, localStk⟩ = ⟨pc, regs, target⟩ := by
  apply cfg_ext
  · cases pc <;> rfl
  · simp [embedCfg]
  · funext i
    classical
    by_cases hi : ∃ j, port j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (embedCfg_stack id port id none _ _ hinj j).trans (hport j).symm
    · exact (embedCfg_stack_frame id port id none _ _ i hi).trans (hframe i hi).symm

theorem sequence_runs {r s l m n k : ℕ}
    (p : Program r s l) (q : Program r s m)
    (ra rb rc : Fin r → Bool) (sa sb sc : Fin s → List Bool)
    (hp : RunsIn p n ⟨some p.entry, ra, sa⟩ ⟨none, rb, sb⟩)
    (hq : RunsIn q k ⟨some q.entry, rb, sb⟩ ⟨none, rc, sc⟩) :
    RunsIn (link p q) (n + k)
      ⟨some (link p q).entry, ra, sa⟩ ⟨none, rc, sc⟩ :=
  link_runsIn p q hp rfl hq

def scalarInput (xs ys modulus : List Bool) : Fin 7 → List Bool :=
  seven xs modulus [] ys [] [] []

def addPorts : Fin 3 → Fin 7 := ![0, 1, 2]
def mulPorts : Fin 6 → Fin 7 := ![0, 1, 6, 2, 3, 4]

theorem addPorts_injective : Function.Injective addPorts := by decide
theorem mulPorts_injective : Function.Injective mulPorts := by decide

abbrev addWideProgram : Program 8 7 17 :=
  liftProgram SubexponentialSAT.BinaryPrograms.Add.littleEndianProgram id addPorts

private theorem embed_add (pc : Option (Fin 17)) (regs frameRegs : Fin 8 → Bool)
    (xs ys output modulus : List Bool) :
    embedCfg id addPorts id none
      (⟨none, frameRegs, resting [] modulus []⟩ : Cfg 8 7 17)
      ⟨pc, regs, SubexponentialSAT.BinaryPrograms.Add.stackState xs ys output⟩ =
      ⟨pc, regs, seven xs modulus [] ys output [] []⟩ := by
  apply embed_ports addPorts addPorts_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · exact False.elim (hi ⟨0, rfl⟩)
    · exact False.elim (hi ⟨1, rfl⟩)
    · exact False.elim (hi ⟨2, rfl⟩)
    · rfl
    · rfl
    · rfl
    · rfl

theorem addWide_correct (regs : Fin 8 → Bool) (hzero : regs 0 = false)
    (xs ys modulus : List Bool) :
    ∃ finalRegs,
      RunsIn addWideProgram (16 * (max xs.length ys.length + 1))
        ⟨some 0, regs, scalarInput xs ys modulus⟩
        ⟨none, finalRegs, resting (add xs ys) modulus []⟩ := by
  obtain ⟨finalRegs, hr⟩ := SubexponentialSAT.BinaryPrograms.Add.littleEndian_run regs xs ys
  have hw := liftProgram_runsIn SubexponentialSAT.BinaryPrograms.Add.littleEndianProgram id addPorts
    (⟨none, regs, resting [] modulus []⟩ : Cfg 8 7 17)
    Function.injective_id addPorts_injective hr
  rw [embed_add, embed_add, hzero] at hw
  exact ⟨finalRegs, hw⟩

abbrev firstMoveProgram : Program 8 7 4 := transferProgram 0 2 1 3
abbrev secondMoveProgram : Program 8 7 4 := transferProgram 2 6 1 3
abbrev moveSumProgram : Program 8 7 8 := link firstMoveProgram secondMoveProgram

private theorem move_sum_first (word modulus : List Bool) :
    transferStacks (0 : Fin 7) 2 (resting word modulus []) =
      seven [] modulus [] [] word.reverse [] [] := by
  funext i; fin_cases i <;> simp [transferStacks, resting, seven]

private theorem move_sum_second (word modulus : List Bool) :
    transferStacks (2 : Fin 7) 6 (seven [] modulus [] [] word.reverse [] []) =
      resting [] modulus word := by
  funext i; fin_cases i <;> simp [transferStacks, resting, seven]

theorem moveSum_correct (regs : Fin 8 → Bool) (word modulus : List Bool) :
    Trace moveSumProgram (6 * word.length + 6)
      ⟨some 0, regs, resting word modulus []⟩
      ⟨none, readRegs regs 1 3 none, resting [] modulus word⟩ := by
  have t1 := transferProgram_trace (0 : Fin 7) 2 (1 : Fin 8) 3
    (by decide) (by decide) regs (resting word modulus [])
  have h1 := halt_after_trace firstMoveProgram t1 (3 : Fin 4) rfl rfl
  simp only [transferResult, move_sum_first] at h1
  have t2 := transferProgram_trace (2 : Fin 7) 6 (1 : Fin 8) 3
    (by decide) (by decide) (readRegs regs 1 3 none)
    (seven [] modulus [] [] word.reverse [] [])
  have h2 := halt_after_trace secondMoveProgram t2 (3 : Fin 4) rfl rfl
  simp only [transferResult, move_sum_second, readRegs_reset] at h2
  have ht := link_trace firstMoveProgram secondMoveProgram h1 rfl h2
  convert ht using 1
  · simp [resting, seven]
    omega
  · simp [relabelCfg, relocatePc]
  · simp [relabelCfg, relocatePc]

abbrev addModProgram : Program 8 7 116 :=
  link (link (link resetBorrowProgram addWideProgram) moveSumProgram) remainderProgram

private theorem add_cost_bound (m a b s k : ℕ) (hs : s ≤ k + 1) (hk : k ≤ a + b) :
    2 + 16 * (k + 1) + (6 * s + 6) + 100 * (m + s + 1) ^ 2 ≤
      600 * (m + a + b + 1) ^ 2 := by
  let T := m + a + b + 1
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hsT : s ≤ T := by dsimp [T]; omega
  have hkT : k + 1 ≤ T := by dsimp [T]; omega
  have hn : m + s + 1 ≤ 2 * T := by dsimp [T] at *; omega
  have hlinear : 2 + 16 * (k + 1) + (6 * s + 6) ≤ 30 * T := by omega
  have hquadratic : 100 * (m + s + 1) ^ 2 ≤ 400 * T ^ 2 := by
    calc
      _ ≤ 100 * (2 * T) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 2)
      _ = _ := by ring
  have hTsq : T ≤ T ^ 2 := by
    have h := Nat.mul_le_mul_left T hT
    simpa only [Nat.mul_one, pow_two] using h
  change _ ≤ 600 * T ^ 2
  omega

theorem addMod_correct (regs : Fin 8 → Bool) (xs ys modulus : List Bool) :
    ∃ finalRegs,
      RunsIn addModProgram (600 * (modulus.length + xs.length + ys.length + 1) ^ 2)
        ⟨some 0, regs, scalarInput xs ys modulus⟩
        ⟨none, finalRegs, resting (reduce modulus (add xs ys)) modulus []⟩ := by
  let r1 := Function.update regs 0 false
  have h1 := resetBorrow_correct regs (scalarInput xs ys modulus)
  obtain ⟨r2, h2⟩ := addWide_correct r1 (by simp [r1]) xs ys modulus
  have h3 := moveSum_correct r2 (add xs ys) modulus
  obtain ⟨r4, h4⟩ := remainder_correct (readRegs r2 1 3 none) modulus (add xs ys)
  have h12 := sequence_runs resetBorrowProgram addWideProgram _ _ _ _ _ _
    ⟨2, le_rfl, h1⟩ h2
  have h123 := sequence_runs _ moveSumProgram _ _ _ _ _ _
    h12 ⟨_, le_rfl, h3⟩
  have ht := sequence_runs _ remainderProgram _ _ _ _ _ _ h123 h4
  refine ⟨r4, ht.mono ?_⟩
  have hlen := length_add xs ys
  have hmax : max xs.length ys.length ≤ xs.length + ys.length := max_le (by omega) (by omega)
  exact add_cost_bound _ _ _ _ _ hlen hmax

theorem addMod_value (regs : Fin 8 → Bool) (xs ys modulus : List Bool)
    (hm : 0 < BinaryArithmetic.toNat modulus) :
    ∃ finalRegs output,
      RunsIn addModProgram (600 * (modulus.length + xs.length + ys.length + 1) ^ 2)
        ⟨some 0, regs, scalarInput xs ys modulus⟩
        ⟨none, finalRegs, resting output modulus []⟩ ∧
      output.length ≤ modulus.length + xs.length + ys.length + 1 ∧
      BinaryArithmetic.toNat output = (BinaryArithmetic.toNat xs + BinaryArithmetic.toNat ys) % BinaryArithmetic.toNat modulus := by
  obtain ⟨finalRegs, hr⟩ := addMod_correct regs xs ys modulus
  refine ⟨finalRegs, reduce modulus (add xs ys), hr, ?_, ?_⟩
  · rw [reduce_length]
    have hl := length_add xs ys
    have hmax : max xs.length ys.length ≤ xs.length + ys.length := max_le (by omega) (by omega)
    omega
  · rw [reduce_correct _ _ hm, toNat_add]

abbrev mulWideProgram : Program 8 7 32 :=
  liftProgram SubexponentialSAT.BinaryPrograms.Mul.program id mulPorts

private theorem embed_mul (pc : Option (Fin 32)) (regs frameRegs : Fin 8 → Bool)
    (xs ys acc cp tmp rev modulus : List Bool) :
    embedCfg id mulPorts id none
      (⟨none, frameRegs, resting [] modulus []⟩ : Cfg 8 7 32)
      (SubexponentialSAT.BinaryPrograms.Mul.cfg pc regs xs ys acc cp tmp rev) =
      ⟨pc, regs, seven xs modulus acc ys cp tmp rev⟩ := by
  apply embed_ports mulPorts mulPorts_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · exact False.elim (hi ⟨0, rfl⟩)
    · exact False.elim (hi ⟨1, rfl⟩)
    · exact False.elim (hi ⟨3, rfl⟩)
    · exact False.elim (hi ⟨4, rfl⟩)
    · exact False.elim (hi ⟨5, rfl⟩)
    · rfl
    · exact False.elim (hi ⟨2, rfl⟩)

theorem mulWide_correct (regs : Fin 8 → Bool) (xs ys modulus : List Bool) :
    ∃ finalRegs,
      RunsIn mulWideProgram (30 * (xs.length + 1) * (ys.length + xs.length + 1))
        ⟨some 0, regs, scalarInput xs ys modulus⟩
        ⟨none, finalRegs,
          resting [] modulus (SubexponentialSAT.BinaryPrograms.Mul.accumulate xs ys [])⟩ := by
  obtain ⟨finalRegs, hr⟩ := SubexponentialSAT.BinaryPrograms.Mul.run regs xs ys [] ys.length le_rfl (by simp)
  have hw := liftProgram_runsIn SubexponentialSAT.BinaryPrograms.Mul.program id mulPorts
    (⟨none, regs, resting [] modulus []⟩ : Cfg 8 7 32)
    Function.injective_id mulPorts_injective hr
  change RunsIn mulWideProgram _ (embedCfg _ _ _ _ _ (SubexponentialSAT.BinaryPrograms.Mul.cfg _ _ _ _ _ _ _ _))
    _ at hw
  rw [embed_mul, embed_mul] at hw
  exact ⟨finalRegs, hw⟩

abbrev mulModProgram : Program 8 7 121 := link mulWideProgram remainderProgram

theorem mulMod_correct (regs : Fin 8 → Bool) (xs ys modulus : List Bool) :
    ∃ finalRegs,
      RunsIn mulModProgram (600 * (modulus.length + xs.length + ys.length + 1) ^ 2)
        ⟨some 0, regs, scalarInput xs ys modulus⟩
        ⟨none, finalRegs,
          resting (reduce modulus (SubexponentialSAT.BinaryPrograms.Mul.accumulate xs ys [])) modulus []⟩ := by
  obtain ⟨r1, h1⟩ := mulWide_correct regs xs ys modulus
  obtain ⟨r2, h2⟩ := remainder_correct r1 modulus (SubexponentialSAT.BinaryPrograms.Mul.accumulate xs ys [])
  have ht := sequence_runs mulWideProgram remainderProgram _ _ _ _ _ _ h1 h2
  refine ⟨r2, ht.mono ?_⟩
  have hl := SubexponentialSAT.BinaryPrograms.Mul.accumulate_length xs ys []
  simp only [List.length_nil, Nat.zero_max] at hl
  have hsquare :
      (modulus.length + (SubexponentialSAT.BinaryPrograms.Mul.accumulate xs ys []).length + 1) ^ 2 ≤
        (modulus.length + xs.length + ys.length + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hprod : (xs.length + 1) * (ys.length + xs.length + 1) ≤
      (modulus.length + xs.length + ys.length + 1) ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  simp only [Nat.mul_assoc]
  omega

theorem mulMod_value (regs : Fin 8 → Bool) (xs ys modulus : List Bool)
    (hm : 0 < BinaryArithmetic.toNat modulus) :
    ∃ finalRegs output,
      RunsIn mulModProgram (600 * (modulus.length + xs.length + ys.length + 1) ^ 2)
        ⟨some 0, regs, scalarInput xs ys modulus⟩
        ⟨none, finalRegs, resting output modulus []⟩ ∧
      output.length ≤ modulus.length + xs.length + ys.length + 1 ∧
      BinaryArithmetic.toNat output = (BinaryArithmetic.toNat xs * BinaryArithmetic.toNat ys) % BinaryArithmetic.toNat modulus := by
  obtain ⟨finalRegs, hr⟩ := mulMod_correct regs xs ys modulus
  refine ⟨finalRegs, reduce modulus (SubexponentialSAT.BinaryPrograms.Mul.accumulate xs ys []), hr, ?_, ?_⟩
  · rw [reduce_length]
    have hl := SubexponentialSAT.BinaryPrograms.Mul.accumulate_length xs ys []
    simp only [List.length_nil, Nat.zero_max] at hl
    omega
  · rw [reduce_correct _ _ hm, SubexponentialSAT.BinaryPrograms.Mul.accumulate_value]
    simp


end SubexponentialSAT.ModularRingPrograms

end OAI.Algorithms
