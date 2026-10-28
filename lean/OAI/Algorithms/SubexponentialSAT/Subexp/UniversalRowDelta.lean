import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CollisionStreamProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.CollisionProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Physical Kronecker-delta selection from the two complete type encodings. -/

namespace SubexponentialSAT.Subexp.UniversalRowDelta

open BitProgram StructuredCalls StackRoutines

abbrev Word := List Bool
abbrev Data := State 10 49

abbrev regMap : Fin 5 → Fin 10 := Fin.castAdd 5
abbrev stackMap : Fin 13 → Fin 49 := ![0, 23, 2, 3, 4, 5, 6, 7, 8, 9, 10, 18, 24]
theorem regMap_injective : Function.Injective regMap := Fin.castAdd_injective 5 5
theorem stackMap_injective : Function.Injective stackMap := by decide

def compareProgram := compiled CollisionStreamProgram.sealCommand (1 : Fin 13) 11
abbrev compareTypes : Cmd 10 49 :=
  .call (ProgramLinking.liftProgram compareProgram regMap stackMap)

abbrev compared (a : Data) : Data :=
  ⟨fun j => if j.val < 5 then false else a.regs j,
    Function.update (Function.update (Function.update a.stacks 23 []) 24 []) 18
      (decide (a.stacks 23 = a.stacks 24) :: a.stacks 18)⟩

theorem compareTypes_eval (a : Data) :
    ∃ n ≤ 11 * (a.stacks 23).length + 2 * (a.stacks 24).length + 20,
      Eval compareTypes n a (compared a) := by
  let inner : State 5 13 := ⟨a.regs ∘ regMap, a.stacks ∘ stackMap⟩
  obtain ⟨n, hn, ht⟩ := CollisionStreamProgram.seal_eval inner
  have hin : embedState regMap stackMap a inner = a := by
    apply embedState_eq_of_ports _ _ _ _ _ regMap_injective stackMap_injective
    · intros; rfl
    · intros; rfl
    · intros; rfl
    · intros; rfl
  have hout : embedState regMap stackMap a
      (CollisionStreamProgram.sealed inner (decide (inner.stacks 1 = inner.stacks 12))) =
      compared a := by
    apply embedState_eq_of_ports _ _ _ _ _ regMap_injective stackMap_injective
    · intro j; fin_cases j <;>
        norm_num [regMap, compared, CollisionStreamProgram.sealed]
    · intro j hj
      have hge : ¬ j.val < 5 := by
        intro h; exact hj ⟨⟨j.val, h⟩, Fin.ext rfl⟩
      simp [ hge]
    · intro j; fin_cases j <;>
        simp [stackMap, inner, CollisionStreamProgram.sealed] ; rfl
    · intro j hj
      have h23 : j ≠ 23 := fun h => hj ⟨1, h.symm⟩
      have h24 : j ≠ 24 := fun h => hj ⟨12, h.symm⟩
      have h18 : j ≠ 18 := fun h => hj ⟨11, h.symm⟩
      simp [ h23, h24, h18]
  have he := eval_call_lifted compareProgram regMap stackMap a regMap_injective stackMap_injective
    (a := inner)
    (b := CollisionStreamProgram.sealed inner (decide (inner.stacks 1 = inner.stacks 12)))
    (compiled_halt_trace ht (1 : Fin 13) 11)
  refine ⟨n + 1, ?_, ?_⟩
  · have hn' : n ≤ 11 * (a.stacks 23).length + 2 * (a.stacks 24).length + 19 := by
      simpa [inner, stackMap] using hn
    omega
  · simpa only [compareTypes, hin, hout] using he

abbrev pick : Cmd 10 49 := .ite 8
  (.call (copyProgram 44 18 15 (0 : Fin 10) 1))
  (.call (copyProgram 47 18 15 (0 : Fin 10) 1))

abbrev command : Cmd 10 49 :=
  .seq compareTypes (.seq (.base (.atom (.pop 18 8 9))) pick)

theorem pick_eval (answer : Bool) (zero one : Word) (a : Data)
    (ha : a.regs 8 = answer) (hz : a.stacks 47 = zero) (ho : a.stacks 44 = one)
    (h18 : a.stacks 18 = []) (h15 : a.stacks 15 = []) :
    ∃ b : Data, Eval pick (7 * (if answer then one else zero).length + 6) a b ∧
      b.stacks = Function.update a.stacks 18 (if answer then one else zero) := by
  cases answer with
  | false =>
      have h := TupleProgram.copy_eval (47 : Fin 49) 18 15 (0 : Fin 10) 1
        (by decide) (by decide) (by decide) (by decide) a h15
      refine ⟨⟨readRegs a.regs 0 1 none, copyStacks 47 18 a.stacks⟩, ?_, ?_⟩
      · have he := Eval.ite_false (yes := .call (copyProgram 44 18 15 (0 : Fin 10) 1)) ha h
        simpa [pick, hz, Nat.add_assoc] using he
      · simp [copyStacks, hz, h18]
  | true =>
      have h := TupleProgram.copy_eval (44 : Fin 49) 18 15 (0 : Fin 10) 1
        (by decide) (by decide) (by decide) (by decide) a h15
      refine ⟨⟨readRegs a.regs 0 1 none, copyStacks 44 18 a.stacks⟩, ?_, ?_⟩
      · have he := Eval.ite_true (no := .call (copyProgram 47 18 15 (0 : Fin 10) 1)) ha h
        simpa [pick, ho, Nat.add_assoc] using he
      · simp [copyStacks, ho, h18]

theorem command_eval (left right zero one : Word) (a : Data)
    (hl : a.stacks 23 = left) (hr : a.stacks 24 = right)
    (hz : a.stacks 47 = zero) (ho : a.stacks 44 = one)
    (h18 : a.stacks 18 = []) (h15 : a.stacks 15 = []) :
    ∃ n ≤ 11 * left.length + 2 * right.length +
        7 * (if left = right then one else zero).length + 27,
      ∃ b : Data, Eval command n a b ∧
        b.stacks = Function.update (Function.update (Function.update a.stacks 23 []) 24 []) 18
          (if left = right then one else zero) := by
  obtain ⟨nc, hnc, hc⟩ := compareTypes_eval a
  let mid : Data := ⟨readRegs (compared a).regs 8 9 (some (decide (left = right))),
    Function.update (compared a).stacks 18 []⟩
  have hp : Eval (.base (.atom (.pop 18 8 9))) 1 (compared a) mid := by
    have h := Eval.base (StructuredProgram.Eval.atom (.pop (18 : Fin 49) 8 9) (compared a))
    convert h using 1
    · simp [mid, hl, hr, h18, StructuredProgram.Atom.eval,
        StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]
  obtain ⟨b, hb, hbs⟩ := pick_eval (decide (left = right)) zero one mid
    (by simp [mid, readRegs]) (by simpa [mid, compared] using hz)
    (by simpa [mid, compared] using ho) (by simp [mid])
    (by simpa [mid, compared] using h15)
  refine ⟨nc + (1 + (7 * (if decide (left = right) then one else zero).length + 6)), ?_,
    b, hc.seq (hp.seq hb), ?_⟩
  · simp only [hl, hr] at hnc
    have hd : (if decide (left = right) then one else zero) =
        (if left = right then one else zero) := by
      by_cases h : left = right <;> simp [h]
    rw [hd]
    omega
  · rw [hbs]
    simp [mid ]

theorem typed_command_eval {r Q Δ : ℕ} (u y : MulticolorTypes.UniversalType r Q Δ)
    (zero one : Word) (a : Data)
    (hu : a.stacks 23 = CollisionProgram.encodeType u)
    (hy : a.stacks 24 = CollisionProgram.encodeType y)
    (hz : a.stacks 47 = zero) (ho : a.stacks 44 = one)
    (h18 : a.stacks 18 = []) (h15 : a.stacks 15 = []) :
    ∃ n ≤ 13 * CollisionProgram.typeWidth r Q Δ +
        7 * (if u = y then one else zero).length + 27,
      ∃ b : Data, Eval command n a b ∧
        b.stacks = Function.update (Function.update (Function.update a.stacks 23 []) 24 []) 18
          (if u = y then one else zero) := by
  obtain ⟨n, hn, b, hb, hbs⟩ := command_eval (CollisionProgram.encodeType u)
    (CollisionProgram.encodeType y) zero one a hu hy hz ho h18 h15
  refine ⟨n, ?_, b, hb, ?_⟩
  · simpa only [CollisionProgram.encodeType_length, CollisionProgram.encodeType_eq_iff,
      show 11 * CollisionProgram.typeWidth r Q Δ + 2 * CollisionProgram.typeWidth r Q Δ =
        13 * CollisionProgram.typeWidth r Q Δ by omega] using hn
  · simpa only [CollisionProgram.encodeType_eq_iff] using hbs

end SubexponentialSAT.Subexp.UniversalRowDelta

end OAI.Algorithms
