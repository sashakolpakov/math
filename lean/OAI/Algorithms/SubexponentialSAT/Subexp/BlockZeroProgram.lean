import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.ParserProgram

namespace OAI.Algorithms

/-! A fixed bit program testing whether all payload bits in a sequence of
frames are zero. Frame delimiters are ignored; no scalar arithmetic is hidden
inside this program. -/

namespace SubexponentialSAT.Subexp.BlockZeroProgram

open BitProgram

private theorem update_eq {n : ℕ} {A : Type*} (f g : Fin n → A) (i : Fin n) (a : A)
    (hi : g i = a) (ho : ∀ j, j ≠ i → g j = f j) : Function.update f i a = g := by
  funext j
  by_cases h : j = i
  · subst j; simp [hi]
  · simp [h, ho j h]

@[simp] private theorem update3_0 {A : Type*} (a b c x : A) :
    Function.update ![a,b,c] (0 : Fin 3) x = ![x,b,c] := by
  funext i; fin_cases i <;> simp

@[simp] private theorem update3_1 {A : Type*} (a b c x : A) :
    Function.update ![a,b,c] (1 : Fin 3) x = ![a,x,c] := by
  funext i; fin_cases i <;> simp

@[simp] private theorem update3_2 {A : Type*} (a b c x : A) :
    Function.update ![a,b,c] (2 : Fin 3) x = ![a,b,x] := by
  funext i; fin_cases i <;> simp

@[simp] private theorem update2_0 {A : Type*} (a b x : A) :
    Function.update ![a,b] (0 : Fin 2) x = ![x,b] := by
  funext i; fin_cases i <;> simp

@[simp] private theorem update2_1 {A : Type*} (a b x : A) :
    Function.update ![a,b] (1 : Fin 2) x = ![a,x] := by
  funext i; fin_cases i <;> simp

@[simp] private theorem update1 {A : Type*} (a x : A) :
    Function.update (fun _ : Fin 1 => a) 0 x = fun _ => x := by
  funext i; fin_cases i; simp

@[simp] private theorem update5_4 {A : Type*} (a b c d e x : A) :
    Function.update ![a,b,c,d,e] (4 : Fin 5) x = ![a,b,c,d,x] := by
  funext i; fin_cases i <;> simp

abbrev program : Program 3 1 8 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code := ![.set 2 true 1, .pop 0 0 1 2, .branch 1 3 7, .branch 0 4 1,
    .pop 0 0 1 5, .branch 0 6 1, .set 2 false 1, .halt]

def cfg (pc : Option (Fin 8)) (v present zero : Bool) (input : List Bool) : Cfg 3 1 8 :=
  ⟨pc, ![v, present, zero], fun _ => input⟩

def frameCost : List Bool → ℕ
  | [] => 3
  | b :: bits => (if b then 6 else 5) + frameCost bits

def frames (words : List (List Bool)) : List Bool := words.flatMap Encoding.frame

def isZero (words : List (List Bool)) : Bool := words.all (fun bits => bits.all (! ·))

@[simp] theorem isZero_nil : isZero [] = true := rfl

theorem frame_trace (bits rest : List Bool) (v present zero : Bool) :
    Trace program (frameCost bits)
      (cfg (some 1) v present zero (Encoding.frame bits ++ rest))
      (cfg (some 1) false true (zero && bits.all (! ·)) rest) := by
  induction bits generalizing v present zero with
  | nil =>
      refine .cons (b := cfg (some 2) false true zero rest) ?_ ?_
      · simp [step, cfg, execInstr, readRegs, Encoding.frame]
      refine .cons (b := cfg (some 3) false true zero rest) ?_ ?_
      · simp [step, cfg, execInstr]
      refine .cons ?_ (.refl _)
      simp [step, cfg, execInstr]
  | cons b bits ih =>
      cases b with
      | false =>
          have cycle : Trace program 5
              (cfg (some 1) v present zero (Encoding.frame (false :: bits) ++ rest))
              (cfg (some 1) false true zero (Encoding.frame bits ++ rest)) := by
            refine .cons (b := cfg (some 2) true true zero
              (false :: (Encoding.frame bits ++ rest))) ?_ ?_
            · simp [step, cfg, execInstr, readRegs, Encoding.frame]
            refine .cons (b := cfg (some 3) true true zero
              (false :: (Encoding.frame bits ++ rest))) ?_ ?_
            · simp [step, cfg, execInstr]
            refine .cons (b := cfg (some 4) true true zero
              (false :: (Encoding.frame bits ++ rest))) ?_ ?_
            · simp [step, cfg, execInstr]
            refine .cons (b := cfg (some 5) false true zero (Encoding.frame bits ++ rest)) ?_ ?_
            · simp [step, cfg, execInstr, readRegs]
            refine .cons ?_ (.refl _)
            simp [step, cfg, execInstr]
          simpa [frameCost, Nat.add_comm] using cycle.trans (ih false true zero)
      | true =>
          have cycle : Trace program 6
              (cfg (some 1) v present zero (Encoding.frame (true :: bits) ++ rest))
              (cfg (some 1) true true false (Encoding.frame bits ++ rest)) := by
            refine .cons (b := cfg (some 2) true true zero
              (true :: (Encoding.frame bits ++ rest))) ?_ ?_
            · simp [step, cfg, execInstr, readRegs, Encoding.frame]
            refine .cons (b := cfg (some 3) true true zero
              (true :: (Encoding.frame bits ++ rest))) ?_ ?_
            · simp [step, cfg, execInstr]
            refine .cons (b := cfg (some 4) true true zero
              (true :: (Encoding.frame bits ++ rest))) ?_ ?_
            · simp [step, cfg, execInstr]
            refine .cons (b := cfg (some 5) true true zero (Encoding.frame bits ++ rest)) ?_ ?_
            · simp [step, cfg, execInstr, readRegs]
            refine .cons (b := cfg (some 6) true true zero (Encoding.frame bits ++ rest)) ?_ ?_
            · simp [step, cfg, execInstr]
            refine .cons ?_ (.refl _)
            simp [step, cfg, execInstr]
          simpa [frameCost, Nat.add_comm] using cycle.trans (ih true true false)

theorem frames_trace (words : List (List Bool)) (v present zero : Bool) :
    Trace program ((words.map frameCost).sum + 3)
      (cfg (some 1) v present zero (frames words))
      (cfg none false false (zero && isZero words) []) := by
  induction words generalizing v present zero with
  | nil =>
      refine .cons (b := cfg (some 2) false false zero []) ?_ ?_
      · simp [step, cfg, execInstr, readRegs, frames]
      refine .cons (b := cfg (some 7) false false zero []) ?_ ?_
      · simp [step, cfg, execInstr]
      refine .cons ?_ (.refl _)
      simp [step, cfg, execInstr]
  | cons bits words ih =>
      have h := (frame_trace bits (frames words) v present zero).trans
        (ih false true (zero && bits.all (! ·)))
      simpa [frames, isZero, Bool.and_assoc, Nat.add_assoc] using h

theorem program_trace (words : List (List Bool)) (v present zero : Bool) :
    Trace program ((words.map frameCost).sum + 4)
      (cfg (some program.entry) v present zero (frames words))
      (cfg none false false (isZero words) []) := by
  have h := frames_trace words v present true
  have first : Trace program 1
      (cfg (some program.entry) v present zero (frames words))
      (cfg (some 1) v present true (frames words)) := by
    refine .cons ?_ (.refl _)
    simp [step, cfg, execInstr]
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using first.trans h

theorem frameCost_le (bits : List Bool) : frameCost bits ≤ 3 * (Encoding.frame bits).length := by
  induction bits with
  | nil => simp [frameCost, Encoding.frame_nil]
  | cons b bits ih =>
      have hl := Encoding.length_frame bits
      cases b <;> simp [frameCost, Encoding.frame_cons] <;> omega

theorem cost_le (words : List (List Bool)) :
    (words.map frameCost).sum + 4 ≤ 3 * (frames words).length + 4 := by
  suffices (words.map frameCost).sum ≤ 3 * (frames words).length by omega
  induction words with
  | nil => simp [frames]
  | cons bits words ih =>
      have hb := frameCost_le bits
      simp only [List.map_cons, List.sum_cons, frames, List.flatMap_cons, List.length_append]
      dsimp [frames] at ih
      omega

theorem program_runsIn (words : List (List Bool)) (v present zero : Bool) :
    RunsIn program (3 * (frames words).length + 4)
      (cfg (some program.entry) v present zero (frames words))
      (cfg none false false (isZero words) []) :=
  ⟨_, cost_le words, program_trace words v present zero⟩

theorem isZero_iff (words : List (List Bool)) :
    isZero words = true ↔ ∀ bits ∈ words, ∀ b ∈ bits, b = false := by
  simp [isZero, List.all_eq_true]

/-- Consume a runtime number of complete scalar frames. Stack 0 is the
unary count and stack 1 the framed scalar stream. -/
abbrev skipProgram : Program 3 2 6 where
  inputStack := 1
  outputStack := 1
  entry := 0
  code := ![.pop 0 0 1 1, .branch 1 2 5, .pop 1 0 2 3,
    .branch 0 4 0, .pop 1 0 2 2, .halt]

def skipCfg (pc : Option (Fin 6)) (v countPresent scalarPresent : Bool)
    (count input : List Bool) : Cfg 3 2 6 :=
  ⟨pc, ![v, countPresent, scalarPresent], ![count, input]⟩

theorem skipFrame_trace (bits rest count : List Bool) (v pr sp : Bool) :
    Trace skipProgram (3 * bits.length + 2)
      (skipCfg (some 2) v pr sp count (Encoding.frame bits ++ rest))
      (skipCfg (some 0) false pr true count rest) := by
  induction bits generalizing v sp with
  | nil =>
      refine .cons (b := skipCfg (some 3) false pr true count rest) ?_ ?_
      · simp [step, skipCfg, execInstr, readRegs, Encoding.frame]
      refine .cons ?_ (.refl _)
      simp [step, skipCfg, execInstr]
  | cons bit bits ih =>
      have first : Trace skipProgram 3
          (skipCfg (some 2) v pr sp count (Encoding.frame (bit :: bits) ++ rest))
          (skipCfg (some 2) bit pr true count (Encoding.frame bits ++ rest)) := by
        refine .cons (b := skipCfg (some 3) true pr true count
          (bit :: (Encoding.frame bits ++ rest))) ?_ ?_
        · simp [step, skipCfg, execInstr, readRegs, Encoding.frame]
        refine .cons (b := skipCfg (some 4) true pr true count
          (bit :: (Encoding.frame bits ++ rest))) ?_ ?_
        · simp [step, skipCfg, execInstr]
        refine .cons ?_ (.refl _)
        simp [step, skipCfg, execInstr, readRegs]
      convert first.trans (ih bit true) using 1 ; simp [List.length_cons] ; omega

def skipCost (words : List (List Bool)) : ℕ :=
  3 + (words.map (fun bits => 3 * bits.length + 4)).sum

theorem skipProgram_trace (words : List (List Bool)) (rest count : List Bool)
    (hc : count.length = words.length) (v pr sp : Bool) :
    Trace skipProgram (skipCost words)
      (skipCfg (some skipProgram.entry) v pr sp count (frames words ++ rest))
      (skipCfg none false false (sp || !words.isEmpty) [] rest) := by
  induction words generalizing count v pr sp with
  | nil =>
      have hn : count = [] := List.length_eq_zero_iff.mp (by simpa using hc)
      subst count
      refine .cons (b := skipCfg (some 1) false false sp [] rest) ?_ ?_
      · simp [step, skipCfg, execInstr, readRegs, frames]
      refine .cons (b := skipCfg (some 5) false false sp [] rest) ?_ ?_
      · simp [step, skipCfg, execInstr]
      refine .cons ?_ (.refl _)
      simp [step, skipCfg, execInstr]
  | cons bits words ih =>
      cases count with
      | nil => simp at hc
      | cons bit count =>
          have ht : count.length = words.length := by simpa using hc
          have first : Trace skipProgram 2
              (skipCfg (some skipProgram.entry) v pr sp (bit :: count)
                (frames (bits :: words) ++ rest))
              (skipCfg (some 2) bit true sp count
                (Encoding.frame bits ++ (frames words ++ rest))) := by
            refine .cons (b := skipCfg (some 1) bit true sp count
              (Encoding.frame bits ++ (frames words ++ rest))) ?_ ?_
            · simp [step, skipCfg, execInstr, readRegs, frames, List.append_assoc]
            refine .cons ?_ (.refl _)
            simp [step, skipCfg, execInstr]
          have h := first.trans ((skipFrame_trace bits (frames words ++ rest) count
            bit true sp).trans (ih count ht false true true))
          convert h using 1 <;> simp [skipCost, Bool.or_true, Nat.add_assoc] ; omega

theorem skipCost_le (words : List (List Bool)) :
    skipCost words ≤ 4 * (frames words).length + 3 := by
  induction words with
  | nil => simp [skipCost, frames]
  | cons bits words ih =>
      simp only [skipCost, List.map_cons, List.sum_cons] at *
      simp only [frames, List.flatMap_cons, List.length_append, Encoding.length_frame] at *
      omega

/-- Combine the four verified zero predicates. Inputs are zero(y),
zero(coefficients), zero(tail coefficients), zero(M*y); output is register 4. -/
abbrev classifyProgram : Program 5 1 8 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code := ![.branch 0 1 2, .branch 1 2 5, .branch 3 3 4, .branch 2 6 5,
    .branch 2 5 6, .set 4 false 7, .set 4 true 7, .halt]

def classifyResult (zeroY zeroCoefficients zeroTail zeroImage : Bool) : Bool :=
  ((!zeroY) || zeroCoefficients) && (zeroImage == zeroTail)

def classifySteps (zeroY zeroCoefficients : Bool) : ℕ :=
  if zeroY then (if zeroCoefficients then 6 else 4) else 5

def classifyCfg (pc : Option (Fin 8)) (zy zc zt zm output : Bool) (data : List Bool) :
    Cfg 5 1 8 := ⟨pc, ![zy, zc, zt, zm, output], fun _ => data⟩

theorem classifyProgram_trace (zy zc zt zm output : Bool) (data : List Bool) :
    Trace classifyProgram (classifySteps zy zc)
      (classifyCfg (some classifyProgram.entry) zy zc zt zm output data)
      (classifyCfg none zy zc zt zm (classifyResult zy zc zt zm) data) := by
  apply Computation.Trace.of_iterate
  cases zy <;> cases zc <;> cases zt <;> cases zm <;>
    simp [classifySteps, classifyResult, Function.iterate_succ_apply,
      step, classifyProgram, classifyCfg, execInstr]

theorem classifyProgram_runsIn (zy zc zt zm output : Bool) (data : List Bool) :
    RunsIn classifyProgram 6
      (classifyCfg (some classifyProgram.entry) zy zc zt zm output data)
      (classifyCfg none zy zc zt zm (classifyResult zy zc zt zm) data) := by
  refine ⟨classifySteps zy zc, ?_, classifyProgram_trace zy zc zt zm output data⟩
  cases zy <;> cases zc <;> decide

end SubexponentialSAT.Subexp.BlockZeroProgram

end OAI.Algorithms
