import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpHornerProgram

namespace OAI.Algorithms

/-! A fixed instruction table generates complete Horner postfix source from
coefficient payload records and reusable input/zero literal payloads. -/

namespace SubexponentialSAT.SubexpHornerSource

open BitProgram SubexpHornerProgram

def pushBits (payload : List Bool) : List Bool := false :: Encoding.frame payload

def closeBits : ℕ → List Bool
  | 0 => []
  | n + 1 => [true, true, true, false] ++ closeBits n

def prefixBits (x : List Bool) : List (List Bool) → List Bool
  | [] => []
  | a :: as => pushBits a ++ pushBits x ++ prefixBits x as

def source (x zero : List Bool) (coeffs : List (List Bool)) : List Bool :=
  prefixBits x coeffs ++ pushBits zero ++ closeBits coeffs.length

theorem closeBits_succ_right (n : ℕ) :
    closeBits (n + 1) = closeBits n ++ [true, true, true, false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa [closeBits, List.append_assoc] using
        congrArg (fun bs => [true, true, true, false] ++ bs) ih

theorem source_nil (x zero : List Bool) : source x zero [] = pushBits zero := by
  simp [source, prefixBits, closeBits]

theorem source_cons (x zero a : List Bool) (as : List (List Bool)) :
    source x zero (a :: as) = pushBits a ++ pushBits x ++ source x zero as ++
      [true, true, true, false] := by
  simp [source, prefixBits, closeBits_succ_right, List.append_assoc]

theorem serializeCode_append {A : Type*} (encode : A → List Bool)
    (a b : List (Algorithm.Instr A)) :
    SubexpPostfixControl.serializeCode encode (a ++ b) =
      SubexpPostfixControl.serializeCode encode a ++ SubexpPostfixControl.serializeCode encode b := by
  induction a with
  | nil => rfl
  | cons i is ih => simp [SubexpPostfixControl.serializeCode, ih, List.append_assoc]

/-- The output is exactly the existing semantic Horner expression's serialized
postfix program, with no supplied instruction stream. -/
theorem source_eq_serialize {R A : Type*} [Zero A]
    (encode : A → List Bool) (literal : R → A) (x : A) (coeffs : List R) :
    source (encode x) (encode 0) (coeffs.map fun a => encode (literal a)) =
      SubexpPostfixControl.serializeCode encode
        (SubexpTableInterpolation.hornerExpr literal (.lit x) coeffs).compile := by
  induction coeffs with
  | nil => simp [source, prefixBits, closeBits, pushBits,
      SubexpTableInterpolation.hornerExpr, Algorithm.Expr.compile,
      SubexpPostfixControl.serializeCode, SubexpPostfixControl.serializeInstr]
  | cons a as ih =>
      simp only [List.map_cons, source_cons, SubexpTableInterpolation.hornerExpr,
        Algorithm.Expr.compile, serializeCode_append, ih]
      simp [pushBits, SubexpPostfixControl.serializeCode,
        SubexpPostfixControl.serializeInstr, List.append_assoc]

@[simp] theorem closeBits_length (n : ℕ) : (closeBits n).length = 4 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [closeBits, ih]; omega

theorem prefixBits_length (x : List Bool) (coeffs : List (List Bool)) :
    (prefixBits x coeffs).length =
      2 * (coeffs.map List.length).sum + (2 * x.length + 4) * coeffs.length := by
  induction coeffs with
  | nil => simp [prefixBits]
  | cons a as ih => simp [prefixBits, pushBits, ih, Nat.mul_add, Nat.add_mul]; omega

theorem source_length (x zero : List Bool) (coeffs : List (List Bool)) :
    (source x zero coeffs).length =
      2 * (coeffs.map List.length).sum + (2 * x.length + 8) * coeffs.length +
        2 * zero.length + 2 := by
  simp [source, prefixBits_length, pushBits]
  ring

def seven {α : Type*} (a b c d e f g : α) : Fin 7 → α := fun i =>
  match i.val with | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f | _ => g

@[simp] theorem update_seven_0 {α : Type*} (a b c d e f g h : α) :
    Function.update (seven a b c d e f g) 0 h = seven h b c d e f g := by
  funext i; fin_cases i <;> simp [seven]
@[simp] theorem update_seven_1 {α : Type*} (a b c d e f g h : α) :
    Function.update (seven a b c d e f g) 1 h = seven a h c d e f g := by
  funext i; fin_cases i <;> simp [seven]
@[simp] theorem update_seven_2 {α : Type*} (a b c d e f g h : α) :
    Function.update (seven a b c d e f g) 2 h = seven a b h d e f g := by
  funext i; fin_cases i <;> simp [seven]
@[simp] theorem update_seven_3 {α : Type*} (a b c d e f g h : α) :
    Function.update (seven a b c d e f g) 3 h = seven a b c h e f g := by
  funext i; fin_cases i <;> simp [seven]
@[simp] theorem update_seven_4 {α : Type*} (a b c d e f g h : α) :
    Function.update (seven a b c d e f g) 4 h = seven a b c d h f g := by
  funext i; fin_cases i <;> simp [seven]
@[simp] theorem update_seven_5 {α : Type*} (a b c d e f g h : α) :
    Function.update (seven a b c d e f g) 5 h = seven a b c d e h g := by
  funext i; fin_cases i <;> simp [seven]
@[simp] theorem update_seven_6 {α : Type*} (a b c d e f g h : α) :
    Function.update (seven a b c d e f g) 6 h = seven a b c d e f h := by
  funext i; fin_cases i <;> simp [seven]

/-- Registers are value, presence, and constant true. Stack ports are:
coefficient input, reusable Ce, reusable zero, reversed source, scratch,
pending-operation counter, forward output. All 49 labels are fixed. -/
abbrev program : Program 3 7 49 where
  inputStack := 0
  outputStack := 6
  entry := 0
  code q := match q.val with
    | 0 => .set 2 true 1
    | 1 => .pop 0 0 1 2
    | 2 => .branch 0 3 23
    | 3 => .set 0 false 4
    | 4 => .push 3 0 5
    | 5 => .pop 0 0 1 6
    | 6 => .push 3 0 7
    | 7 => .branch 0 8 10
    | 8 => .pop 0 0 1 9
    | 9 => .push 3 0 5
    | 10 => .set 0 false 11
    | 11 => .push 3 0 12
    | 12 => .pop 1 0 1 13
    | 13 => .branch 1 14 17
    | 14 => .push 4 0 15
    | 15 => .push 3 2 16
    | 16 => .push 3 0 12
    | 17 => .push 3 0 18
    | 18 => .pop 4 0 1 19
    | 19 => .branch 1 20 21
    | 20 => .push 1 0 18
    | 21 => .push 5 2 1
    | 23 => .set 0 false 24
    | 24 => .push 3 0 25
    | 25 => .pop 2 0 1 26
    | 26 => .branch 1 27 30
    | 27 => .push 4 0 28
    | 28 => .push 3 2 29
    | 29 => .push 3 0 25
    | 30 => .push 3 0 31
    | 31 => .pop 4 0 1 32
    | 32 => .branch 1 33 34
    | 33 => .push 2 0 31
    | 34 => .pop 5 0 1 35
    | 35 => .branch 1 36 42
    | 36 => .push 3 2 37
    | 37 => .push 3 2 38
    | 38 => .push 3 2 39
    | 39 => .set 0 false 40
    | 40 => .push 3 0 34
    | 42 => .pop 3 0 1 43
    | 43 => .branch 1 44 45
    | 44 => .push 6 0 42
    | 45 => .set 0 false 46
    | 46 => .set 1 false 47
    | 47 => .set 2 false 48
    | _ => .halt

@[simp] theorem code_0 : program.code 0 = .set 2 true 1 := rfl
@[simp] theorem code_1 : program.code 1 = .pop 0 0 1 2 := rfl
@[simp] theorem code_2 : program.code 2 = .branch 0 3 23 := rfl
@[simp] theorem code_3 : program.code 3 = .set 0 false 4 := rfl
@[simp] theorem code_4 : program.code 4 = .push 3 0 5 := rfl
@[simp] theorem code_5 : program.code 5 = .pop 0 0 1 6 := rfl
@[simp] theorem code_6 : program.code 6 = .push 3 0 7 := rfl
@[simp] theorem code_7 : program.code 7 = .branch 0 8 10 := rfl
@[simp] theorem code_8 : program.code 8 = .pop 0 0 1 9 := rfl
@[simp] theorem code_9 : program.code 9 = .push 3 0 5 := rfl
@[simp] theorem code_10 : program.code 10 = .set 0 false 11 := rfl
@[simp] theorem code_11 : program.code 11 = .push 3 0 12 := rfl
@[simp] theorem code_12 : program.code 12 = .pop 1 0 1 13 := rfl
@[simp] theorem code_13 : program.code 13 = .branch 1 14 17 := rfl
@[simp] theorem code_14 : program.code 14 = .push 4 0 15 := rfl
@[simp] theorem code_15 : program.code 15 = .push 3 2 16 := rfl
@[simp] theorem code_16 : program.code 16 = .push 3 0 12 := rfl
@[simp] theorem code_17 : program.code 17 = .push 3 0 18 := rfl
@[simp] theorem code_18 : program.code 18 = .pop 4 0 1 19 := rfl
@[simp] theorem code_19 : program.code 19 = .branch 1 20 21 := rfl
@[simp] theorem code_20 : program.code 20 = .push 1 0 18 := rfl
@[simp] theorem code_21 : program.code 21 = .push 5 2 1 := rfl
@[simp] theorem code_23 : program.code 23 = .set 0 false 24 := rfl
@[simp] theorem code_24 : program.code 24 = .push 3 0 25 := rfl
@[simp] theorem code_25 : program.code 25 = .pop 2 0 1 26 := rfl
@[simp] theorem code_26 : program.code 26 = .branch 1 27 30 := rfl
@[simp] theorem code_27 : program.code 27 = .push 4 0 28 := rfl
@[simp] theorem code_28 : program.code 28 = .push 3 2 29 := rfl
@[simp] theorem code_29 : program.code 29 = .push 3 0 25 := rfl
@[simp] theorem code_30 : program.code 30 = .push 3 0 31 := rfl
@[simp] theorem code_31 : program.code 31 = .pop 4 0 1 32 := rfl
@[simp] theorem code_32 : program.code 32 = .branch 1 33 34 := rfl
@[simp] theorem code_33 : program.code 33 = .push 2 0 31 := rfl
@[simp] theorem code_34 : program.code 34 = .pop 5 0 1 35 := rfl
@[simp] theorem code_35 : program.code 35 = .branch 1 36 42 := rfl
@[simp] theorem code_36 : program.code 36 = .push 3 2 37 := rfl
@[simp] theorem code_37 : program.code 37 = .push 3 2 38 := rfl
@[simp] theorem code_38 : program.code 38 = .push 3 2 39 := rfl
@[simp] theorem code_39 : program.code 39 = .set 0 false 40 := rfl
@[simp] theorem code_40 : program.code 40 = .push 3 0 34 := rfl
@[simp] theorem code_42 : program.code 42 = .pop 3 0 1 43 := rfl
@[simp] theorem code_43 : program.code 43 = .branch 1 44 45 := rfl
@[simp] theorem code_44 : program.code 44 = .push 6 0 42 := rfl
@[simp] theorem code_45 : program.code 45 = .set 0 false 46 := rfl
@[simp] theorem code_46 : program.code 46 = .set 1 false 47 := rfl
@[simp] theorem code_47 : program.code 47 = .set 2 false 48 := rfl
@[simp] theorem code_48 : program.code 48 = .halt := rfl

theorem step_some (q : Fin 49) (regs : Fin 3 → Bool) (store : Fin 7 → List Bool) :
    step program ⟨some q, regs, store⟩ =
      some (execInstr (program.code q) ⟨some q, regs, store⟩) := rfl

def cfg (pc : Option (Fin 49)) (v p c : Bool)
    (input x zero acc scratch count out : List Bool) : Cfg 3 7 49 :=
  ⟨pc, triple v p c, seven input x zero acc scratch count out⟩

theorem frame_cycle (b v p : Bool) (bs x z acc tmp count out : List Bool) :
    Trace program 5 (cfg (some 5) v p true (true :: b :: bs) x z acc tmp count out)
      (cfg (some 5) b true true bs x z (b :: true :: acc) tmp count out) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step_some, execInstr, readRegs, triple, seven]

theorem frame_finish (v p : Bool) (rest x z acc tmp count out : List Bool) :
    Trace program 3 (cfg (some 5) v p true (false :: rest) x z acc tmp count out)
      (cfg (some 10) false true true rest x z (false :: acc) tmp count out) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step_some, execInstr, readRegs, triple, seven]

theorem frame_trace (payload rest x z acc tmp count out : List Bool) (v p : Bool) :
    Trace program (5 * payload.length + 3)
      (cfg (some 5) v p true (Encoding.frame payload ++ rest) x z acc tmp count out)
      (cfg (some 10) false true true rest x z
        ((Encoding.frame payload).reverse ++ acc) tmp count out) := by
  induction payload generalizing acc v p with
  | nil => simpa [Encoding.frame] using frame_finish v p rest x z acc tmp count out
  | cons b bs ih =>
      have h := (frame_cycle b v p (Encoding.frame bs ++ rest) x z acc tmp count out).trans
        (ih (b :: true :: acc) b true)
      convert h using 1 <;> (try simp [Encoding.frame, List.reverse_cons, List.append_assoc]) ; omega

theorem ce_copy_cycle (b v p : Bool) (input bs z acc tmp count out : List Bool) :
    Trace program 5 (cfg (some 12) v p true input (b :: bs) z acc tmp count out)
      (cfg (some 12) b true true input bs z (b :: true :: acc) (b :: tmp) count out) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step_some, execInstr, readRegs, triple, seven]

theorem ce_copy_finish (v p : Bool) (input z acc tmp count out : List Bool) :
    Trace program 3 (cfg (some 12) v p true input [] z acc tmp count out)
      (cfg (some 18) false false true input [] z (false :: acc) tmp count out) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step_some, execInstr, readRegs, triple, seven]

theorem ce_copy_trace (input x z acc tmp count out : List Bool) (v p : Bool) :
    Trace program (5 * x.length + 3)
      (cfg (some 12) v p true input x z acc tmp count out)
      (cfg (some 18) false false true input [] z
        ((Encoding.frame x).reverse ++ acc) (x.reverse ++ tmp) count out) := by
  induction x generalizing acc tmp v p with
  | nil => simpa [Encoding.frame] using ce_copy_finish v p input z acc tmp count out
  | cons b bs ih =>
      have h := (ce_copy_cycle b v p input bs z acc tmp count out).trans
        (ih (b :: true :: acc) (b :: tmp) b true)
      convert h using 1 <;> (try simp [Encoding.frame, List.reverse_cons, List.append_assoc]) ; omega

theorem ce_restore_cycle (b v p : Bool) (input x z acc tmp count out : List Bool) :
    Trace program 3 (cfg (some 18) v p true input x z acc (b :: tmp) count out)
      (cfg (some 18) b true true input (b :: x) z acc tmp count out) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step_some, execInstr, readRegs, triple, seven]

theorem ce_restore_finish (v p : Bool) (input x z acc count out : List Bool) :
    Trace program 2 (cfg (some 18) v p true input x z acc [] count out)
      (cfg (some 21) false false true input x z acc [] count out) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step_some, execInstr, readRegs, triple, seven]

theorem ce_restore_trace (input x z acc tmp count out : List Bool) (v p : Bool) :
    Trace program (3 * tmp.length + 2)
      (cfg (some 18) v p true input x z acc tmp count out)
      (cfg (some 21) false false true input (tmp.reverse ++ x) z acc [] count out) := by
  induction tmp generalizing x v p with
  | nil => simpa using ce_restore_finish v p input x z acc count out
  | cons b bs ih =>
      have h := (ce_restore_cycle b v p input x z acc bs count out).trans
        (ih (b :: x) b true)
      convert h using 1 <;> (try simp [List.reverse_cons, List.append_assoc]) ; omega

theorem ce_trace (input x z acc count out : List Bool) (v p : Bool) :
    Trace program (8 * x.length + 7)
      (cfg (some 10) v p true input x z acc [] count out)
      (cfg (some 21) false false true input x z ((pushBits x).reverse ++ acc) [] count out) := by
  have hp : Trace program 2 (cfg (some 10) v p true input x z acc [] count out)
      (cfg (some 12) false p true input x z (false :: acc) [] count out) := by
    apply Computation.Trace.of_iterate
    simp [Function.iterate_succ_apply, cfg, step_some, execInstr, triple, seven]
  have hc := ce_copy_trace input x z (false :: acc) [] count out false p
  simp only [List.append_nil] at hc
  have hr := ce_restore_trace input [] z
    ((Encoding.frame x).reverse ++ false :: acc) x.reverse count out false false
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hr
  have h := hp.trans (hc.trans hr)
  convert h using 1 <;> (try simp [pushBits, List.reverse_cons, List.append_assoc]) ; omega

theorem coefficient_cycle (a rest x z acc count out : List Bool) (v p : Bool) :
    Trace program (5 * a.length + 8 * x.length + 15)
      (cfg (some 1) v p true (true :: (Encoding.frame a ++ rest)) x z acc [] count out)
      (cfg (some 1) false false true rest x z
        ((pushBits a ++ pushBits x).reverse ++ acc) [] (true :: count) out) := by
  have hp : Trace program 4
      (cfg (some 1) v p true (true :: (Encoding.frame a ++ rest)) x z acc [] count out)
      (cfg (some 5) false true true (Encoding.frame a ++ rest) x z (false :: acc) [] count out) := by
    apply Computation.Trace.of_iterate
    simp [Function.iterate_succ_apply, cfg, step_some, execInstr, readRegs, triple, seven]
  have hf := frame_trace a rest x z (false :: acc) [] count out false true
  have hx := ce_trace rest x z ((Encoding.frame a).reverse ++ false :: acc) count out false true
  have ht : Trace program 1
      (cfg (some 21) false false true rest x z
        ((pushBits x).reverse ++ ((Encoding.frame a).reverse ++ false :: acc)) [] count out)
      (cfg (some 1) false false true rest x z
        ((pushBits x).reverse ++ ((Encoding.frame a).reverse ++ false :: acc)) [] (true :: count) out) := by
    apply Computation.Trace.of_iterate
    simp [ cfg, step_some, execInstr, triple, seven]
  have h := hp.trans (hf.trans (hx.trans ht))
  convert h using 1 <;> (try simp [pushBits, List.reverse_cons, List.reverse_append, List.append_assoc]) ; omega

theorem coefficients_trace (coeffs : List (List Bool))
    (rest x z acc count out : List Bool) (v p : Bool) :
    Trace program (5 * (coeffs.map List.length).sum + (8 * x.length + 15) * coeffs.length + 2)
      (cfg (some 1) v p true (Encoding.encodeList id coeffs ++ rest) x z acc [] count out)
      (cfg (some 23) false true true rest x z
        ((prefixBits x coeffs).reverse ++ acc) []
        (List.replicate coeffs.length true ++ count) out) := by
  induction coeffs generalizing acc count v p with
  | nil =>
      apply Computation.Trace.of_iterate
      simp [Function.iterate_succ_apply, Encoding.encodeList, prefixBits, cfg,
        step_some, execInstr, readRegs, triple, seven]
  | cons a as ih =>
      have h := (coefficient_cycle a (Encoding.encodeList id as ++ rest) x z acc count out v p).trans
        (ih ((pushBits a ++ pushBits x).reverse ++ acc) (true :: count) false false)
      convert h using 1 <;>
        (try simp [Encoding.encodeList, prefixBits, List.reverse_append, List.append_assoc,
          List.replicate_succ', Nat.mul_add, Nat.add_mul]) ; omega

theorem zero_copy_cycle (b v p : Bool) (input x bs acc tmp count out : List Bool) :
    Trace program 5 (cfg (some 25) v p true input x (b :: bs) acc tmp count out)
      (cfg (some 25) b true true input x bs (b :: true :: acc) (b :: tmp) count out) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step_some, execInstr, readRegs, triple, seven]

theorem zero_copy_finish (v p : Bool) (input x acc tmp count out : List Bool) :
    Trace program 3 (cfg (some 25) v p true input x [] acc tmp count out)
      (cfg (some 31) false false true input x [] (false :: acc) tmp count out) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step_some, execInstr, readRegs, triple, seven]

theorem zero_copy_trace (input x z acc tmp count out : List Bool) (v p : Bool) :
    Trace program (5 * z.length + 3)
      (cfg (some 25) v p true input x z acc tmp count out)
      (cfg (some 31) false false true input x []
        ((Encoding.frame z).reverse ++ acc) (z.reverse ++ tmp) count out) := by
  induction z generalizing acc tmp v p with
  | nil => simpa [Encoding.frame] using zero_copy_finish v p input x acc tmp count out
  | cons b bs ih =>
      have h := (zero_copy_cycle b v p input x bs acc tmp count out).trans
        (ih (b :: true :: acc) (b :: tmp) b true)
      convert h using 1 <;> (try simp [Encoding.frame, List.reverse_cons, List.append_assoc]) ; omega

theorem zero_restore_cycle (b v p : Bool) (input x z acc tmp count out : List Bool) :
    Trace program 3 (cfg (some 31) v p true input x z acc (b :: tmp) count out)
      (cfg (some 31) b true true input x (b :: z) acc tmp count out) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step_some, execInstr, readRegs, triple, seven]

theorem zero_restore_finish (v p : Bool) (input x z acc count out : List Bool) :
    Trace program 2 (cfg (some 31) v p true input x z acc [] count out)
      (cfg (some 34) false false true input x z acc [] count out) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step_some, execInstr, readRegs, triple, seven]

theorem zero_restore_trace (input x z acc tmp count out : List Bool) (v p : Bool) :
    Trace program (3 * tmp.length + 2)
      (cfg (some 31) v p true input x z acc tmp count out)
      (cfg (some 34) false false true input x (tmp.reverse ++ z) acc [] count out) := by
  induction tmp generalizing z v p with
  | nil => simpa using zero_restore_finish v p input x z acc count out
  | cons b bs ih =>
      have h := (zero_restore_cycle b v p input x z acc bs count out).trans
        (ih (b :: z) b true)
      convert h using 1 <;> (try simp [List.reverse_cons, List.append_assoc]) ; omega

theorem zero_trace (input x z acc count out : List Bool) (v p : Bool) :
    Trace program (8 * z.length + 7)
      (cfg (some 23) v p true input x z acc [] count out)
      (cfg (some 34) false false true input x z ((pushBits z).reverse ++ acc) [] count out) := by
  have hp : Trace program 2 (cfg (some 23) v p true input x z acc [] count out)
      (cfg (some 25) false p true input x z (false :: acc) [] count out) := by
    apply Computation.Trace.of_iterate
    simp [Function.iterate_succ_apply, cfg, step_some, execInstr, triple, seven]
  have hc := zero_copy_trace input x z (false :: acc) [] count out false p
  simp only [List.append_nil] at hc
  have hr := zero_restore_trace input x []
    ((Encoding.frame z).reverse ++ false :: acc) z.reverse count out false false
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hr
  have h := hp.trans (hc.trans hr)
  convert h using 1 <;> (try simp [pushBits, List.reverse_cons, List.append_assoc]) ; omega

theorem close_cycle (v p : Bool) (input x z acc count out : List Bool) :
    Trace program 7 (cfg (some 34) v p true input x z acc [] (true :: count) out)
      (cfg (some 34) false true true input x z (false :: true :: true :: true :: acc) [] count out) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step_some, execInstr, readRegs, triple, seven]

theorem close_finish (v p : Bool) (input x z acc out : List Bool) :
    Trace program 2 (cfg (some 34) v p true input x z acc [] [] out)
      (cfg (some 42) false false true input x z acc [] [] out) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step_some, execInstr, readRegs, triple, seven]

theorem close_trace (n : ℕ) (input x z acc out : List Bool) (v p : Bool) :
    Trace program (7 * n + 2)
      (cfg (some 34) v p true input x z acc [] (List.replicate n true) out)
      (cfg (some 42) false false true input x z ((closeBits n).reverse ++ acc) [] [] out) := by
  induction n generalizing acc v p with
  | zero => simpa [closeBits] using close_finish v p input x z acc out
  | succ n ih =>
      have h := (close_cycle v p input x z acc (List.replicate n true) out).trans
        (ih (false :: true :: true :: true :: acc) false true)
      convert h using 1 <;>
        (try simp [closeBits, List.replicate_succ, List.append_assoc]) ; omega

theorem output_cycle (b v p : Bool) (input x z bs out : List Bool) :
    Trace program 3 (cfg (some 42) v p true input x z (b :: bs) [] [] out)
      (cfg (some 42) b true true input x z bs [] [] (b :: out)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step_some, execInstr, readRegs, triple, seven]

theorem output_finish (v p : Bool) (input x z out : List Bool) :
    Trace program 6 (cfg (some 42) v p true input x z [] [] [] out)
      (cfg none false false false input x z [] [] [] out) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step_some, execInstr, readRegs, triple, seven]

theorem output_trace (bits input x z out : List Bool) (v p : Bool) :
    Trace program (3 * bits.length + 6)
      (cfg (some 42) v p true input x z bits [] [] out)
      (cfg none false false false input x z [] [] [] (bits.reverse ++ out)) := by
  induction bits generalizing out v p with
  | nil => simpa using output_finish v p input x z out
  | cons b bs ih =>
      have h := (output_cycle b v p input x z bs out).trans (ih (b :: out) b true)
      convert h using 1 <;> (try simp [List.reverse_cons, List.append_assoc]) ; omega

/-- Exact Boolean-stack instruction count, including traversal, framing,
restoration, pending-operation emission, and final output reversal. -/
def runCost (x zero : List Bool) (coeffs : List (List Bool)) : ℕ :=
  11 * (coeffs.map List.length).sum + (14 * x.length + 46) * coeffs.length +
    14 * zero.length + 24

theorem trace (coeffs : List (List Bool)) (rest x z out : List Bool) (v p c : Bool) :
    Trace program (runCost x z coeffs)
      (cfg (some 0) v p c (Encoding.encodeList id coeffs ++ rest) x z [] [] [] out)
      (cfg none false false false rest x z [] [] [] (source x z coeffs ++ out)) := by
  have hp : Trace program 1
      (cfg (some 0) v p c (Encoding.encodeList id coeffs ++ rest) x z [] [] [] out)
      (cfg (some 1) v p true (Encoding.encodeList id coeffs ++ rest) x z [] [] [] out) := by
    apply Computation.Trace.of_iterate
    simp [ cfg, step_some, execInstr ]
  have hc := coefficients_trace coeffs rest x z [] [] out v p
  simp only [List.append_nil] at hc
  have hz := zero_trace rest x z (prefixBits x coeffs).reverse
    (List.replicate coeffs.length true) out false true
  have hclose := close_trace coeffs.length rest x z
    ((pushBits z).reverse ++ (prefixBits x coeffs).reverse) out false false
  have hout := output_trace
    ((closeBits coeffs.length).reverse ++ ((pushBits z).reverse ++ (prefixBits x coeffs).reverse))
    rest x z out false false
  have h := hp.trans (hc.trans (hz.trans (hclose.trans hout)))
  convert h using 1 <;>
    (try simp [runCost, source, prefixBits_length, pushBits, List.reverse_append,
      List.append_assoc]) ; ring

theorem primitive_execution (coeffs : List (List Bool))
    (rest x z out : List Bool) (v p c : Bool) :
    Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * runCost x z coeffs)
      (BitProgram.primitiveCfg program
        (cfg (some 0) v p c (Encoding.encodeList id coeffs ++ rest) x z [] [] [] out))
      (BitProgram.primitiveCfg program
        (cfg none false false false rest x z [] [] [] (source x z coeffs ++ out))) :=
  BitProgram.primitive_execution program ⟨_, le_rfl, trace coeffs rest x z out v p c⟩

/-- Actual execution directly from encoded semantic coefficients to the
existing serialized Horner program. -/
theorem trace_horner {R A : Type*} [Zero A] (encode : A → List Bool)
    (literal : R → A) (x : A) (coeffs : List R) (rest out : List Bool) (v p c : Bool) :
    Trace program (runCost (encode x) (encode 0) (coeffs.map fun a => encode (literal a)))
      (cfg (some 0) v p c
        (Encoding.encodeList id (coeffs.map fun a => encode (literal a)) ++ rest)
        (encode x) (encode 0) [] [] [] out)
      (cfg none false false false rest (encode x) (encode 0) [] [] []
        (SubexpPostfixControl.serializeCode encode
          (SubexpTableInterpolation.hornerExpr literal (.lit x) coeffs).compile ++ out)) := by
  simpa only [source_eq_serialize] using
    trace (coeffs.map fun a => encode (literal a)) rest (encode x) (encode 0) out v p c

end SubexponentialSAT.SubexpHornerSource

end OAI.Algorithms
