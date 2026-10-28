import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFieldCacheNodeLoop

namespace OAI.Algorithms

/-! The physical inner scan that emits one row of inverse differences. -/

namespace SubexponentialSAT.SubexpFieldCachePairLoop

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SubexpCRTCofactorControl SubexpFieldCacheControl SubexpFieldCacheLoop
open SubexpQuarticFlatMul (flat)
open SubexpFieldCacheMachine (add power pairIterationBudget)

def ready (base : Words) (node stream : List Bool) : Words :=
  {base with
    stream := stream, node := node
    negative := [], power := [], left := [], right := [], result := []}

noncomputable def PairValue (p μ : ℕ) (c : Fin 4 → ZMod (p^μ)) (exponent : List Bool)
    (node negative inverse : Quad (Word (baseWidth p μ))) : Prop :=
  quotientDenote c (inverse.map (wordValue p μ)) =
    (quotientDenote c (node.map (wordValue p μ)) +
      quotientDenote c (negative.map (wordValue p μ))) ^ BinaryArithmetic.toNat exponent

theorem loop_value (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (c : Fin 4 → ZMod (p^μ))
    (t unit node : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (unit.map (wordValue p μ)) = 1)
    (base : Words) (hm : base.modulus = M.bits) (hr : base.reduction = flat t)
    (hone : base.unit = flat unit) (hw : base.width.length = baseWidth p μ)
    (hblock : base.blockWidth.length = 4 * baseWidth p μ) (hB : 0 < baseWidth p μ)
    (xs : List (Quad (Word (baseWidth p μ)))) (regs : Fin 8 → Bool)
    (frame : Fin 110 → List Bool) :
    ∃ n rf ys, n ≤ xs.length * (pairIterationBudget (baseWidth p μ) base.exponent + 2) + 1 ∧
      List.Forall₂ (PairValue p μ c base.exponent node) xs ys ∧
      Eval (.while 1 (.seq (pairIteration add power) (peek 99))) n
        (state (readRegs regs 0 1 (xs.flatMap flat).head?) frame
          (ready base (flat node) (xs.flatMap flat)))
        (state rf (Function.update frame 103 ((ys.flatMap flat).reverse ++ frame 103))
          (ready base (flat node) [])) := by
  induction xs generalizing regs frame with
  | nil =>
      refine ⟨1, readRegs regs 0 1 none, [], by simp, .nil, ?_⟩
      simp only [List.flatMap_nil, List.reverse_nil, List.nil_append, Function.update_eq_self]
      exact Eval.while_false (by simp [state, readRegs])
  | cons a xs ih =>
      let r0 := readRegs regs 0 1 ((a :: xs).flatMap flat).head?
      let w0 := ready base (flat node) ((a :: xs).flatMap flat)
      obtain ⟨n, r1, b, hn, he, hv⟩ := SubexpFieldCacheMachine.pairIteration_value
        p μ M c t unit node a ht hu r0 frame w0 (xs.flatMap flat)
        hm hr hone rfl rfl hw hblock rfl rfl rfl rfl rfl
      let f1 := Function.update frame 103 ((flat b).reverse ++ frame 103)
      have he' : Eval (pairIteration add power) n (state r0 frame w0)
          (state r1 f1 (ready base (flat node) (xs.flatMap flat))) := he
      have hp := SubexpCRTCofactorLoop.peekNodes_eval r1 f1
        (ready base (flat node) (xs.flatMap flat))
      obtain ⟨m, rf, ys, hm', hys, hi⟩ := ih r1 f1
      have hne : flat a ≠ [] := by
        intro hz
        have hh := congrArg List.length hz
        simp only [SubexpQuarticFlatMul.flat_length, List.length_nil] at hh
        omega
      have hg : (state r0 frame w0).regs 1 = true := by
        cases ha : flat a with
        | nil => exact False.elim (hne ha)
        | cons bit bits => simp [r0, state, readRegs, ha]
      have hh := Eval.while_true hg (he'.seq hp) hi
      refine ⟨n + 1 + m + 1, rf, b :: ys, ?_, .cons hv hys, ?_⟩
      · change n ≤ pairIterationBudget (baseWidth p μ) base.exponent at hn
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
      · simpa only [SubexpCRTCofactorControl.peekNodes, peek, ready, r0, w0,
          List.flatMap_cons, List.reverse_append, List.append_assoc,
          Function.update_same, Function.update_idem, f1] using hh

theorem scan_value (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (c : Fin 4 → ZMod (p^μ))
    (t unit node : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (unit.map (wordValue p μ)) = 1)
    (base : Words) (hm : base.modulus = M.bits) (hr : base.reduction = flat t)
    (hone : base.unit = flat unit) (hw : base.width.length = baseWidth p μ)
    (hblock : base.blockWidth.length = 4 * baseWidth p μ) (hB : 0 < baseWidth p μ)
    (xs : List (Quad (Word (baseWidth p μ)))) (regs : Fin 8 → Bool)
    (frame : Fin 110 → List Bool) :
    ∃ n rf ys, n ≤ xs.length * (pairIterationBudget (baseWidth p μ) base.exponent + 2) + 2 ∧
      List.Forall₂ (PairValue p μ c base.exponent node) xs ys ∧
      Eval (.seq (peek 99) (.while 1 (.seq (pairIteration add power) (peek 99)))) n
        (state regs frame (ready base (flat node) (xs.flatMap flat)))
        (state rf (Function.update frame 103 ((ys.flatMap flat).reverse ++ frame 103))
          (ready base (flat node) [])) := by
  obtain ⟨n, rf, ys, hn, hv, he⟩ := loop_value p μ M c t unit node ht hu base
    hm hr hone hw hblock hB xs regs frame
  have hp := SubexpCRTCofactorLoop.peekNodes_eval regs frame
    (ready base (flat node) (xs.flatMap flat))
  exact ⟨1 + n, rf, ys, by omega, hv, hp.seq he⟩

def rowBudget (B : ℕ) (exponent : List Bool) (count dataBits : ℕ) : ℕ :=
  count * (pairIterationBudget B exponent + 2) + 64 * B + 7 * dataBits + 21

/-- One actual outer-loop row consumes the next positive node, scans every
negative node in order, and appends exactly one complete inverse row. -/
theorem row_value (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (c : Fin 4 → ZMod (p^μ))
    (t unit node : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (unit.map (wordValue p μ)) = 1)
    (base : Words) (hm : base.modulus = M.bits) (hr : base.reduction = flat t)
    (hone : base.unit = flat unit) (hw : base.width.length = baseWidth p μ)
    (hblock : base.blockWidth.length = 4 * baseWidth p μ) (hB : 0 < baseWidth p μ)
    (xs : List (Quad (Word (baseWidth p μ)))) (regs : Fin 8 → Bool)
    (frame : Fin 110 → List Bool) (rest : List Bool)
    (hsource : frame 106 = flat node ++ rest) (htable : frame 100 = xs.flatMap flat) :
    ∃ n rf ys, n ≤ rowBudget (baseWidth p μ) base.exponent xs.length (xs.flatMap flat).length ∧
      List.Forall₂ (PairValue p μ c base.exponent node) xs ys ∧
      Eval (pairRow add power) n (state regs frame (ready base [] []))
        (state rf
          (Function.update (Function.update frame 106 rest) 103
            ((ys.flatMap flat).reverse ++ frame 103)) (ready base [] [])) := by
  let f1 := Function.update frame 106 rest
  let r1 := readRegs regs 0 1 none
  have h1 := take_outer_eval regs frame (ready base [] []) (flat node) rest hsource
    (by simpa only [ready, SubexpQuarticFlatMul.flat_length] using hblock) rfl
  have h2 := copy_extra_stream_eval r1 f1 (ready base (flat node) []) 100
    (by right; left; rfl) rfl
  have htable1 : f1 100 = xs.flatMap flat := by simpa [f1] using htable
  have h2' : Eval (SubexpFieldCacheControl.copy 100 99) (7 * (xs.flatMap flat).length + 5)
      (state r1 f1 (ready base (flat node) []))
      (state r1 f1 (ready base (flat node) (xs.flatMap flat))) := by
    simpa only [htable1, r1, StackRoutines.readRegs_reset, ready] using h2
  obtain ⟨ns, rs, ys, hns, hv, hs⟩ := scan_value p μ M c t unit node ht hu base
    hm hr hone hw hblock hB xs r1 f1
  let f2 := Function.update f1 103 ((ys.flatMap flat).reverse ++ f1 103)
  have h3 := clear_node_eval rs f2 (ready base (flat node) [])
  have he := h1.seq (h2'.seq (SubexpCRTCofactorLoop.seq_assoc (hs.seq h3)))
  refine ⟨14 * (flat node).length + 11 +
      (7 * (xs.flatMap flat).length + 5 + (ns + (2 * (flat node).length + 3))),
    readRegs rs 0 1 none, ys, ?_, hv, ?_⟩
  · simp only [SubexpQuarticFlatMul.flat_length]
    unfold rowBudget
    omega
  · simpa only [pairRow, r1, f1, f2, ready,
      Function.update_of_ne (by decide : (103 : Fin 110) ≠ 106)] using he

/-- The outer scan emits complete rows in the order of the supplied positive
node array. The output is still reversed once globally, as specified. -/
theorem outer_loop_value (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (c : Fin 4 → ZMod (p^μ))
    (t unit : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (unit.map (wordValue p μ)) = 1)
    (base : Words) (hm : base.modulus = M.bits) (hr : base.reduction = flat t)
    (hone : base.unit = flat unit) (hw : base.width.length = baseWidth p μ)
    (hblock : base.blockWidth.length = 4 * baseWidth p μ) (hB : 0 < baseWidth p μ)
    (xs negatives : List (Quad (Word (baseWidth p μ)))) (regs : Fin 8 → Bool)
    (frame : Fin 110 → List Bool)
    (hsource : frame 106 = xs.flatMap flat) (htable : frame 100 = negatives.flatMap flat) :
    ∃ n rf rows,
      n ≤ xs.length * (rowBudget (baseWidth p μ) base.exponent
        negatives.length (negatives.flatMap flat).length + 2) + 1 ∧
      List.Forall₂ (fun node row =>
        List.Forall₂ (PairValue p μ c base.exponent node) negatives row) xs rows ∧
      Eval (.while 1 (.seq (pairRow add power) (peek 106))) n
        (state (readRegs regs 0 1 (frame 106).head?) frame (ready base [] []))
        (state rf (Function.update (Function.update frame 106 []) 103
          ((rows.flatten.flatMap flat).reverse ++ frame 103)) (ready base [] [])) := by
  induction xs generalizing regs frame with
  | nil =>
      have hsrc0 : frame 106 = [] := by simpa only [List.flatMap_nil] using hsource
      have hf : Function.update frame 106 [] = frame := by
        rw [← hsrc0]
        exact Function.update_eq_self _ _
      refine ⟨1, readRegs regs 0 1 none, [], by simp, .nil, ?_⟩
      simp only [List.flatten_nil, List.flatMap_nil, List.reverse_nil, List.nil_append,
        hf, Function.update_eq_self]
      simpa only [hsource, List.flatMap_nil, List.head?_nil] using
        (Eval.while_false (a := state (readRegs regs 0 1 (frame 106).head?) frame (ready base [] []))
          (body := .seq (pairRow add power) (peek 106))
          (by simp [state, readRegs, hsource]))
  | cons a xs ih =>
      let r0 := readRegs regs 0 1 (frame 106).head?
      obtain ⟨n, r1, row, hn, hv, he⟩ := row_value p μ M c t unit a ht hu base
        hm hr hone hw hblock hB negatives r0 frame (xs.flatMap flat)
        (by simpa only [List.flatMap_cons] using hsource) htable
      let f1 := Function.update (Function.update frame 106 (xs.flatMap flat)) 103
        ((row.flatMap flat).reverse ++ frame 103)
      have hp := peek_extra_eval r1 f1 (ready base [] []) 106 (by right; right; right; rfl)
      have hsrc1 : f1 106 = xs.flatMap flat := by simp [f1]
      have htab1 : f1 100 = negatives.flatMap flat := by simpa [f1] using htable
      obtain ⟨m, rf, rows, hm', hrows, hi⟩ := ih r1 f1 hsrc1 htab1
      have hne : flat a ≠ [] := by
        intro hz
        have hl := congrArg List.length hz
        simp only [SubexpQuarticFlatMul.flat_length, List.length_nil] at hl
        omega
      have hg : (state r0 frame (ready base [] [])).regs 1 = true := by
        cases ha : flat a with
        | nil => exact False.elim (hne ha)
        | cons bit bits => simp [r0, state, readRegs, hsource, ha]
      have hh := Eval.while_true hg (he.seq hp) hi
      have hf : Function.update (Function.update f1 106 []) 103
          ((rows.flatten.flatMap flat).reverse ++ f1 103) =
          Function.update (Function.update frame 106 []) 103
            (((row :: rows).flatten.flatMap flat).reverse ++ frame 103) := by
        funext j
        by_cases hj106 : j = 106
        · subst j; simp [f1]
        · by_cases hj103 : j = 103
          · subst j
            simp [f1, List.flatten_cons, List.flatMap_append, List.reverse_append, List.append_assoc]
          · simp [f1, hj106, hj103]
      rw [hf] at hh
      refine ⟨n + 1 + m + 1, rf, row :: rows, ?_, .cons hv hrows, hh⟩
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem rows_length {A C : Type*} {R : A → C → C → Prop}
    {xs : List A} {ys : List C} {rows : List (List C)}
    (h : List.Forall₂ (fun x row => List.Forall₂ (R x) ys row) xs rows) :
    rows.flatten.length = xs.length * ys.length := by
  induction h with
  | nil => simp
  | @cons a row xs rows ha h ih =>
      simp only [List.flatten_cons, List.length_append, List.length_cons]
      rw [← ha.length_eq, ih]
      simp [Nat.add_mul, Nat.add_comm]

def passBudget (B : ℕ) (exponent : List Bool) (count negativeCount : ℕ) : ℕ :=
  count * (rowBudget B exponent negativeCount (4 * B * negativeCount) + 2) +
    28 * B * count + 36 * B * count * negativeCount + 15

/-- The complete pair pass emits an unframed row-major array. The original
node and negative-node arrays and the prior node-inverse array are preserved. -/
theorem pass_value (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (c : Fin 4 → ZMod (p^μ))
    (t unit : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (unit.map (wordValue p μ)) = 1)
    (base : Words) (hm : base.modulus = M.bits) (hr : base.reduction = flat t)
    (hone : base.unit = flat unit) (hw : base.width.length = baseWidth p μ)
    (hblock : base.blockWidth.length = 4 * baseWidth p μ) (hB : 0 < baseWidth p μ)
    (xs negatives : List (Quad (Word (baseWidth p μ)))) (regs : Fin 8 → Bool)
    (frame : Fin 110 → List Bool)
    (hsource : frame 97 = xs.flatMap flat) (htable : frame 100 = negatives.flatMap flat)
    (houter : frame 106 = []) (hzero : frame 103 = []) :
    ∃ n rf rows, n ≤ passBudget (baseWidth p μ) base.exponent xs.length negatives.length ∧
      List.Forall₂ (fun node row =>
        List.Forall₂ (PairValue p μ c base.exponent node) negatives row) xs rows ∧
      Eval (pairPass add power) n (state regs frame (ready base [] []))
        (state rf (Function.update frame 103 (rows.flatten.flatMap flat))
          (ready base [] [])) := by
  let r1 := readRegs regs 0 1 none
  let f1 := Function.update frame 106 (xs.flatMap flat)
  have hc := copy_extra_eval regs frame (ready base [] []) 97 106
    (by left; rfl) (by right; right; right; rfl) (by decide) houter
  have hc' : Eval (SubexpFieldCacheControl.copy 97 106)
      (7 * (xs.flatMap flat).length + 5) (state regs frame (ready base [] []))
      (state r1 f1 (ready base [] [])) := by
    simpa only [hsource, r1, f1] using hc
  have hp := peek_extra_eval r1 f1 (ready base [] []) 106 (by right; right; right; rfl)
  obtain ⟨nl, rl, rows, hnl, hv, hl⟩ := outer_loop_value p μ M c t unit ht hu base
    hm hr hone hw hblock hB xs negatives r1 f1 (by simp [f1])
    (by simpa [f1] using htable)
  have hf : Function.update (Function.update f1 106 []) 103
      ((rows.flatten.flatMap flat).reverse ++ f1 103) =
      Function.update frame 103 (rows.flatten.flatMap flat).reverse := by
    simp only [f1, Function.update_idem,
      Function.update_of_ne (by decide : (103 : Fin 110) ≠ 106), hzero, List.append_nil]
    rw [← houter, Function.update_eq_self]
  rw [hf] at hl
  let f2 := Function.update frame 103 (rows.flatten.flatMap flat).reverse
  have hr := reverse_extra_eval rl f2 (ready base [] []) 103 (by right; right; left; rfl)
  have hr' : Eval (SubexpFieldCacheControl.reverse 103)
      (9 * (rows.flatten.flatMap flat).length + 7)
      (state rl f2 (ready base [] []))
      (state (readRegs rl 0 1 none)
        (Function.update frame 103 (rows.flatten.flatMap flat)) (ready base [] [])) := by
    simpa only [f2, Function.update_same, Function.update_idem,
      List.reverse_reverse, List.length_reverse] using hr
  have he := hc'.seq (hp.seq (hl.seq hr'))
  refine ⟨_, readRegs rl 0 1 none, rows, ?_, hv, he⟩
  rw [SubexpFieldCacheNodeLoop.flatMap_length,
    SubexpFieldCacheNodeLoop.flatMap_length, rows_length hv]
  rw [SubexpFieldCacheNodeLoop.flatMap_length] at hnl
  unfold passBudget
  nlinarith only [hnl]

end SubexponentialSAT.SubexpFieldCachePairLoop

end OAI.Algorithms
