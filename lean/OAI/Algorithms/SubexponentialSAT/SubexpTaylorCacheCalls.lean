import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorCacheControl

namespace OAI.Algorithms

/-! Concrete row and framing calls inside the nested Taylor-cache traversal.
The assertions describe only local tape formats and preserved frames. -/

namespace SubexponentialSAT.SubexpTaylorCacheCalls

open BitProgram StructuredCalls SubexpScanPrimitives SubexpHornerControl
open SubexpTaylorControl SubexpTaylorCacheControl

abbrev Data := State 14 112

def clean (base : Words) (d : Data) : Prop :=
  ∀ i : Fin 90, d.stacks (rowStacks i) =
    (SubexpTaylorRow.rowState (fun _ => false) (done base []) [] [] []).stacks i

def withRow (d : Data) (source count output : List Bool) : Data :=
  ⟨d.regs, Function.update (Function.update (Function.update d.stacks 87 source) 88 count) 89 output⟩

noncomputable def rowResult (d : Data) (regs : Fin 8 → Bool) (output : List Bool) : Data :=
  ⟨Function.extend rowRegs regs d.regs,
    Function.update (Function.update (Function.update d.stacks 87 []) 88 []) 89 output⟩

@[simp] theorem rowStacks_val (i : Fin 90) : (rowStacks i).val = i.val := rfl
@[simp] theorem rowRegs_val (i : Fin 8) : (rowRegs i).val = i.val := rfl

@[simp] theorem rowStacks_eq (i : Fin 90) (j : Fin 90) :
    rowStacks i = rowStacks j ↔ i = j := rowStacks.injective.eq_iff

theorem rowStacks_ne_high (i : Fin 90) (j : Fin 112) (hj : 90 ≤ j.val) :
    rowStacks i ≠ j := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [rowStacks_val] at hv
  omega

theorem rowRegs_ne_high (i : Fin 8) (j : Fin 14) (hj : 8 ≤ j.val) :
    rowRegs i ≠ j := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  simp only [rowRegs_val] at hv
  omega

@[simp] theorem rowResult_regs_high (d : Data) (regs : Fin 8 → Bool)
    (output : List Bool) (j : Fin 14) (hj : 8 ≤ j.val) :
    (rowResult d regs output).regs j = d.regs j := by
  apply Function.extend_apply'
  rintro ⟨i, hi⟩
  exact rowRegs_ne_high i j hj hi

theorem withRow_shape (base : Words) (d : Data) (hc : clean base d)
    (source count output : List Bool) (i : Fin 90) :
    (withRow d source count output).stacks (rowStacks i) =
      (SubexpTaylorRow.rowState (d.regs ∘ rowRegs) (done base []) source count output).stacks i := by
  by_cases h87 : i = 87
  · subst i; simp [withRow, rowStacks]
  by_cases h88 : i = 88
  · subst i; simp [withRow, rowStacks]
  by_cases h89 : i = 89
  · subst i; simp [withRow, rowStacks]
  have hn87 : rowStacks i ≠ 87 := by
    change rowStacks i ≠ rowStacks 87
    exact fun h => h87 (rowStacks.injective h)
  have hn88 : rowStacks i ≠ 88 := by
    change rowStacks i ≠ rowStacks 88
    exact fun h => h88 (rowStacks.injective h)
  have hn89 : rowStacks i ≠ 89 := by
    change rowStacks i ≠ rowStacks 89
    exact fun h => h89 (rowStacks.injective h)
  simp only [withRow, Function.update_of_ne hn89, Function.update_of_ne hn88,
    Function.update_of_ne hn87]
  rw [hc i]
  have hi : i.val < 87 := by
    have := i.isLt
    simp only [Fin.ext_iff, Fin.coe_ofNat_eq_mod] at h87 h88 h89
    omega
  obtain ⟨j, rfl⟩ : ∃ j : Fin 87, Fin.castAdd 3 j = i :=
    ⟨⟨i.val, hi⟩, by apply Fin.ext; rfl⟩
  change (SubexpTaylorRow.rowState _ _ [] [] []).stacks
      (Fin.castAdd 2 (Fin.castAdd 1 j)) =
    (SubexpTaylorRow.rowState _ _ source count output).stacks
      (Fin.castAdd 2 (Fin.castAdd 1 j))
  simp only [SubexpTaylorRow.rowState_inner, SubexpTaylorOuter.outerState_inner]

theorem embed_row_input (base : Words) (d : Data) (hc : clean base d)
    (source count output : List Bool) :
    embedState rowRegs rowStacks (withRow d source count output)
      (SubexpTaylorRow.rowState (d.regs ∘ rowRegs) (done base []) source count output) =
      withRow d source count output := by
  apply embedState_eq _ _ rowRegs.injective rowStacks.injective
  · intro i; rfl
  · intro i; exact withRow_shape base d hc source count output i
  · intros; rfl
  · intros; rfl

theorem embed_row_output (base : Words) (d : Data) (hc : clean base d)
    (source count before output : List Bool) (regs : Fin 8 → Bool) :
    embedState rowRegs rowStacks (withRow d source count before)
      (SubexpTaylorRow.rowState regs (done base []) [] [] output) =
      rowResult d regs output := by
  apply embedState_eq _ _ rowRegs.injective rowStacks.injective
  · intro i; exact rowRegs.injective.extend_apply regs d.regs i
  · intro i
    exact withRow_shape base d hc [] [] output i
  · intro i hi
    exact Function.extend_apply' _ _ _ hi
  · intro i hi
    have h87 : i ≠ 87 := fun h => hi ⟨87, by simpa [rowStacks] using h.symm⟩
    have h88 : i ≠ 88 := fun h => hi ⟨88, by simpa [rowStacks] using h.symm⟩
    have h89 : i ≠ 89 := fun h => hi ⟨89, by simpa [rowStacks] using h.symm⟩
    simp [withRow, rowResult, h87, h88, h89]

theorem clean_reg_change (base : Words) (d : Data) (regs : Fin 14 → Bool)
    (hc : clean base d) : clean base ⟨regs, d.stacks⟩ := hc

theorem clean_update_high (base : Words) (d : Data) (hc : clean base d)
    (j : Fin 112) (hj : 90 ≤ j.val) (bits : List Bool) :
    clean base ⟨d.regs, Function.update d.stacks j bits⟩ := by
  intro i
  simpa only [Function.update_of_ne (rowStacks_ne_high i j hj)] using hc i

@[simp] theorem clean_0 (base : Words) (d : Data) (hc : clean base d) :
    d.stacks 0 = [] := hc 0
@[simp] theorem clean_87 (base : Words) (d : Data) (hc : clean base d) :
    d.stacks 87 = [] := hc 87
@[simp] theorem clean_88 (base : Words) (d : Data) (hc : clean base d) :
    d.stacks 88 = [] := hc 88
@[simp] theorem clean_89 (base : Words) (d : Data) (hc : clean base d) :
    d.stacks 89 = [] := hc 89

def writerResult (d : Data) : Data :=
  ⟨Function.update (Function.update d.regs 0 true) 1 false,
    Function.update (Function.update d.stacks 109 []) 110
      (SubexpTaylorFrames.recordBytes (d.stacks 109).reverse ++ d.stacks 110)⟩

theorem writeRecord_eval (d : Data) :
    Eval writeRecord (5 * (d.stacks 109).length + 7) d (writerResult d) := by
  let small : State 5 6 := ⟨d.regs ∘ writerRegs, d.stacks ∘ writerStacks⟩
  have ht := SubexpArgumentProgram.writer_eval true small (d.stacks 109).reverse
    (by simp [small, writerStacks])
  have hin : embedState writerRegs writerStacks d small = d := by
    apply embedState_eq _ _ writerRegs.injective writerStacks.injective
    · intro i; rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intros; rfl
  have hout : embedState writerRegs writerStacks d
      (SubexpArgumentProgram.afterWriter true small (d.stacks 109).reverse) = writerResult d := by
    apply embedState_eq _ _ writerRegs.injective writerStacks.injective
    · intro i; fin_cases i <;> simp [writerResult, small, writerRegs,
        SubexpArgumentProgram.finishedRegs]
    · intro i; fin_cases i <;>
        simp [writerResult, small, writerStacks,
          SubexpArgumentProgram.destination, SubexpTaylorFrames.recordBytes]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, by simpa [writerRegs] using h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, by simpa [writerRegs] using h.symm⟩
      simp [writerResult, h0, h1]
    · intro i hi
      have h109 : i ≠ 109 := fun h => hi ⟨1, by simpa [writerStacks] using h.symm⟩
      have h110 : i ≠ 110 := fun h => hi ⟨3, by simpa [writerStacks] using h.symm⟩
      simp [writerResult, h109, h110]
  cases ht with
  | call _ ht =>
      have he := eval_call_lifted (SubexpArgumentProgram.writer true) writerRegs writerStacks d
        writerRegs.injective writerStacks.injective ht
      simpa only [writeRecord, hin, hout, List.length_reverse] using he

def finishResult (src dst : Fin 112) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks src []) dst
      ((d.stacks src).reverse ++ false :: d.stacks dst)⟩

theorem finishList_eval (src dst : Fin 112) (hsd : src ≠ dst) (d : Data) :
    Eval (finishList src dst) (3 * (d.stacks src).length + 8) d (finishResult src dst d) := by
  let d₁ : Data := ⟨Function.update d.regs 0 false, d.stacks⟩
  let d₂ : Data := ⟨d₁.regs, Function.update d.stacks src (false :: d.stacks src)⟩
  have h1 : Eval (atom (.set 0 false)) 1 d d₁ := .base (.atom _ _)
  have h2 : Eval (atom (.push src 0)) 1 d₁ d₂ := .base (.atom _ _)
  have h3 := transfer_eval d₂ src dst 0 1 hsd (by decide)
  have he : afterTransfer d₂ src dst 0 1 = finishResult src dst d := by
    apply state_ext
    · funext i
      by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
        simp [afterTransfer, finishResult, d₂, d₁, readRegs, h0, h1]
    · funext i
      by_cases hs : i = src <;> by_cases ht : i = dst <;>
        simp [afterTransfer, StackRoutines.transferStacks, finishResult, d₂, d₁,
          hs, ht, hsd, Ne.symm hsd]
  rw [he] at h3
  convert h1.seq (h2.seq h3) using 1 ; simp [d₂] ; omega

def recordStream (items : List (List Bool)) : List Bool :=
  items.flatMap SubexpTaylorFrames.recordBytes

theorem encodeList_recordStream (items : List (List Bool)) :
    Encoding.encodeList id items = recordStream items ++ [false] := by
  induction items with
  | nil => rfl
  | cons bits items ih =>
      simp [Encoding.encodeList, recordStream, SubexpTaylorFrames.recordBytes, ih,
        List.append_assoc]

theorem visits_packed {C : Type*} (encode output : C → List Bool) (port : Fin 112)
    (effect : List Bool → Data → Data → Prop)
    (heffect : ∀ bits a b, effect bits a b → ∀ x, encode x = bits →
      b.stacks port = (SubexpTaylorFrames.recordBytes (output x)).reverse ++ a.stacks port)
    (items : List C) (a b : Data)
    (hv : RecordPrograms.Visits (fun _ => false) effect (items.map encode) a b) :
    b.stacks port = (recordStream (items.map output)).reverse ++ a.stacks port := by
  induction items generalizing a with
  | nil => cases hv; simp [recordStream]
  | cons x xs ih =>
      cases hv with
      | hit h _ => cases h
      | @miss _ _ _ middle _ _ he hr =>
          rw [ih middle hr, heffect _ _ _ he x rfl]
          simp [recordStream, List.append_assoc]

theorem visits_unchanged {α : Type*} (measure : Data → α)
    (effect : List Bool → Data → Data → Prop)
    (heffect : ∀ bits a b, effect bits a b → measure b = measure a)
    (items : List (List Bool)) (a b : Data)
    (hv : RecordPrograms.Visits (fun _ => false) effect items a b) :
    measure b = measure a := by
  induction hv with
  | nil => rfl
  | hit h _ => cases h
  | @miss _ _ _ middle _ _ he hr ih => exact ih.trans (heffect _ _ _ he)

@[simp] theorem unread_false (items : List (List Bool)) (tail : List Bool) :
    RecordPrograms.unread (fun _ => false) items tail = tail := by
  induction items <;> simp_all [RecordPrograms.unread]

@[simp] theorem budget_constant {C : Type*} (encode : C → List Bool) (cost : ℕ)
    (items : List C) :
    RecordPrograms.budget (fun _ => cost) (items.map encode) =
      6 * (items.map (fun x => (encode x).length)).sum + (cost + 7) * items.length := by
  induction items with
  | nil => simp [RecordPrograms.budget]
  | cons x xs ih => simp [RecordPrograms.budget, ih] ; ring

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

abbrev Code := SubexpTaylorRow.Code p μ

theorem runRow_eval (hμ : 0 < μ) (t theta : Code p μ)
    (width blockWidth : List Bool) (hw : width.length = SubexpLiftRing.baseWidth p μ)
    (hblock : blockWidth.length = 4 * SubexpLiftRing.baseWidth p μ)
    (N : ℕ) (P : List (Code p μ)) (d : Data)
    (hc : clean (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) d) :
    ∃ n ≤ SubexpTaylorRow.budget P.length N (SubexpLiftRing.baseWidth p μ),
      ∃ regs : Fin 8 → Bool,
      Eval runRow n
        (withRow d (encodeList SubexpTaylorRow.flat P).reverse (List.replicate N true) [])
        (rowResult d regs (Encoding.encodeList SubexpTaylorRow.flat
          (SubexpTaylorRow.cache p μ M t theta N P))) := by
  obtain ⟨n, hn, regs, ht⟩ := SubexpTaylorRow.program_trace p μ M hμ t theta
    width blockWidth hw hblock N P (d.regs ∘ rowRegs)
  have he := eval_call_lifted SubexpTaylorRow.program rowRegs rowStacks
    (withRow d (encodeList SubexpTaylorRow.flat P).reverse (List.replicate N true) [])
    rowRegs.injective rowStacks.injective ht
  refine ⟨n, hn, regs, ?_⟩
  simpa only [runRow, embed_row_input _ _ hc, embed_row_output _ _ hc] using he

def rowCallbackBudget (n N B : ℕ) : ℕ :=
  7 * N + SubexpTaylorRow.budget n N B + 14 * ((8 * B + 2) * N + 1) + 24

theorem rowCallbackBudget_mono {n m : ℕ} (hnm : n ≤ m) (N B : ℕ) :
    rowCallbackBudget n N B ≤ rowCallbackBudget m N B := by
  let A := SubexpTaylorProgram.scalarBound B + 33 * (4 * B) + 27
  have hinner : (n + 1) * A + 2 ≤ (m + 1) * A + 2 :=
    Nat.add_le_add_right (Nat.mul_le_mul_right A (Nat.add_le_add_right hnm 1)) 2
  have hprod := Nat.mul_le_mul hnm hinner
  have hlinear := Nat.mul_le_mul_right (4 * B) hnm
  dsimp [A] at hprod
  unfold rowCallbackBudget SubexpTaylorRow.budget
  omega

theorem coordinate_eval (hμ : 0 < μ) (t theta : Code p μ)
    (width blockWidth : List Bool) (hw : width.length = SubexpLiftRing.baseWidth p μ)
    (hblock : blockWidth.length = 4 * SubexpLiftRing.baseWidth p μ)
    (N : ℕ) (P : List (Code p μ)) (d : Data)
    (hc : clean (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) d)
    (hcount : d.stacks 101 = List.replicate N true)
    (h109 : d.stacks 109 = []) (h110 : d.stacks 110 = []) :
    ∃ n ≤ rowCallbackBudget P.length N (SubexpLiftRing.baseWidth p μ),
      ∃ regs : Fin 14 → Bool, (∀ i : Fin 14, 8 ≤ i.val → regs i = d.regs i) ∧
      Eval coordinateCallback n
        (withRow d (encodeList SubexpTaylorRow.flat P).reverse [] [])
        ⟨regs, Function.update d.stacks 106
          ((SubexpTaylorFrames.recordBytes (Encoding.encodeList SubexpTaylorRow.flat
            (SubexpTaylorRow.cache p μ M t theta N P))).reverse ++ d.stacks 106)⟩ := by
  let base := SubexpHornerMachine.baseWords p μ M t theta width blockWidth
  let bits := (encodeList SubexpTaylorRow.flat P).reverse
  let out := Encoding.encodeList SubexpTaylorRow.flat (SubexpTaylorRow.cache p μ M t theta N P)
  let a := withRow d bits [] []
  let r₁ := readRegs d.regs 0 1 none
  let d₁ : Data := ⟨r₁, d.stacks⟩
  have hd₁ : clean base d₁ := hc
  have hcopy := copy_eval a 101 88 0 0 1
    (by decide) (by decide) (by decide) (by decide)
    (by simpa [a, withRow] using clean_0 base d hc)
  have ecopy : afterCopy a 101 88 0 1 = withRow d₁ bits (List.replicate N true) [] := by
    apply state_ext
    · rfl
    · funext i
      by_cases h87 : i = 87 <;> by_cases h88 : i = 88 <;> by_cases h89 : i = 89 <;>
        simp [afterCopy, StackRoutines.copyStacks, a, withRow, d₁, h87, h88, h89, hcount]
  rw [ecopy] at hcopy
  obtain ⟨nr, hnr, rr, hr⟩ := runRow_eval p μ M hμ t theta width blockWidth hw hblock N P d₁ hd₁
  let d₂ := rowResult d₁ rr out
  let d₃ := afterTransfer d₂ 89 109 0 1
  let d₄ := writerResult d₃
  let d₅ := afterTransfer d₄ 110 106 0 1
  have h3 := transfer_eval d₂ 89 109 0 1 (by decide) (by decide)
  have h4 := writeRecord_eval d₃
  have h5 := transfer_eval d₄ 110 106 0 1 (by decide) (by decide)
  have houtlen : out.length = (8 * SubexpLiftRing.baseWidth p μ + 2) * N + 1 :=
    SubexpTaylorRow.cache_encode_length p μ M t theta N P
  have hlen3 : (d₃.stacks 109).length = out.length := by
    simp [d₃, d₂, d₁, afterTransfer, StackRoutines.transferStacks, rowResult, h109]
  have hlen4 : (d₄.stacks 110).length = 2 * out.length + 2 := by
    simp [d₄, d₃, d₂, d₁, writerResult, afterTransfer, StackRoutines.transferStacks,
      rowResult, h109, h110, SubexpTaylorFrames.recordBytes, Encoding.length_frame]
  have hs : d₅.stacks = Function.update d.stacks 106
      ((SubexpTaylorFrames.recordBytes out).reverse ++ d.stacks 106) := by
    funext i
    have hd87 := clean_87 base d hc
    have hd88 := clean_88 base d hc
    have hd89 := clean_89 base d hc
    by_cases h87 : i = 87 <;> by_cases h88 : i = 88 <;> by_cases h89 : i = 89 <;>
      by_cases h106 : i = 106 <;> by_cases hi109 : i = 109 <;> by_cases hi110 : i = 110 <;>
      simp [d₅, d₄, d₃, d₂, d₁, afterTransfer, StackRoutines.transferStacks,
        rowResult, writerResult, h87, h88, h89, h106, hi109, hi110,
        hd87, hd88, hd89, h109, h110]
  refine ⟨(7 * (a.stacks 101).length + 5) +
    (nr + ((3 * (d₂.stacks 89).length + 3) +
      ((5 * (d₃.stacks 109).length + 7) + (3 * (d₄.stacks 110).length + 3)))),
    ?_, d₅.regs, ?_, ?_⟩
  · have ha : (a.stacks 101).length = N := by simp [a, withRow, hcount]
    have hb : d₂.stacks 89 = out := by simp [d₂, rowResult]
    rw [ha, hb, hlen3, hlen4, houtlen]
    unfold rowCallbackBudget
    omega
  · intro i hi
    have hi0 : i ≠ 0 := by intro h; subst i; norm_num at hi
    have hi1 : i ≠ 1 := by intro h; subst i; norm_num at hi
    simp only [d₅, d₄, d₃, afterTransfer, writerResult]
    simp only [readRegs, Function.update_of_ne hi0, Function.update_of_ne hi1]
    exact (rowResult_regs_high d₁ rr out i hi).trans
      (StackRoutines.readRegs_frame d.regs 0 1 i none hi0 hi1)
  · have he := hcopy.seq (hr.seq (h3.seq (h4.seq h5)))
    have heq : d₅ = ⟨d₅.regs, Function.update d.stacks 106
        ((SubexpTaylorFrames.recordBytes out).reverse ++ d.stacks 106)⟩ := state_ext rfl hs
    change Eval coordinateCallback _ (withRow d bits [] []) d₅ at he
    rw [heq] at he
    exact he

end SubexponentialSAT.SubexpTaylorCacheCalls

end OAI.Algorithms
