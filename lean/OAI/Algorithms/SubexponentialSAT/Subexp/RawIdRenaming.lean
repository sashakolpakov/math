import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.RawIdEncoding
import OAI.Algorithms.SubexponentialSAT.SubexpFrontend

namespace OAI.Algorithms

/-! Dense renaming through the actual finite dictionary of occurring ID
words. Dictionary rank is the same byte-comparison index returned by the
published physical lookup routine. -/

namespace SubexponentialSAT.Subexp.RawIdRenaming

open RawIdEncoding

private theorem attach_map_eq_map {A B : Type*} (xs : List A)
    (f : {x // x ∈ xs} → B) (g : A → B) (h : ∀ x, f x = g x.val) :
    xs.attach.map f = xs.map g := by
  calc
    xs.attach.map f = xs.attach.map (g ∘ Subtype.val) := by
      apply congrArg (fun f => xs.attach.map f)
      exact funext h
    _ = (xs.attach.map Subtype.val).map g := (List.map_map).symm
    _ = xs.map g := by rw [List.attach_map_subtype_val]

def oldVariable (F : Formula) (i : Fin (dimension F)) : Word := (dictionary F).get i

def rank (F : Formula) (id : Word) (h : id ∈ dictionary F) : Fin (dimension F) :=
  ⟨(dictionary F).idxOf id, by
    simpa only [dimension, List.idxOf, beq_eq_decide] using List.idxOf_lt_length_iff.mpr h⟩

@[simp] theorem oldVariable_rank (F : Formula) (id : Word) (h : id ∈ dictionary F) :
    oldVariable F (rank F id h) = id := by
  unfold oldVariable rank
  convert List.idxOf_get (List.idxOf_lt_length_iff.mpr h) using 1
  congr 1

@[simp] theorem rank_oldVariable (F : Formula) (i : Fin (dimension F))
    (h : oldVariable F i ∈ dictionary F) : rank F (oldVariable F i) h = i := by
  apply Fin.ext
  simpa only [rank, oldVariable, List.idxOf, beq_eq_decide] using
    List.get_idxOf (dictionary_nodup F) i

def denseLiteral (F : Formula) (C : Clause) (hC : C ∈ F)
    (l : Literal) (hl : l ∈ C) : SAT.Literal (Fin (dimension F)) :=
  ⟨rank F l.variable (literal_id_mem F C hC l hl), l.positive⟩

def denseClause (F : Formula) (C : Clause) (hC : C ∈ F) :
    List (SAT.Literal (Fin (dimension F))) :=
  C.attach.map fun l => denseLiteral F C hC l.val l.property

def denseRows (F : Formula) : List (List (SAT.Literal (Fin (dimension F)))) :=
  F.attach.map fun C => denseClause F C.val C.property

/-- Both prepend-based accumulation orders are retained explicitly. -/
def physicalRows (F : Formula) : List (List (SAT.Literal (Fin (dimension F)))) :=
  ((denseRows F).map List.reverse).reverse

def code (F : Formula) (l : Literal) : ℕ :=
  2 * (dictionary F).idxOf l.variable + if l.positive then 1 else 0

def denseCodes (F : Formula) : List (List ℕ) := F.map (List.map (code F))
def physicalCodes (F : Formula) : List (List ℕ) := ((denseCodes F).map List.reverse).reverse

def outputWord (F : Formula) : Word :=
  Encoding.encodeNat (dimension F) ++
    Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) (physicalCodes F)

@[simp] theorem rename_denseLiteral (F : Formula) (C : Clause) (hC : C ∈ F)
    (l : Literal) (hl : l ∈ C) :
    SubexpFrontend.renameLiteral (oldVariable F) (denseLiteral F C hC l hl) = l := by
  cases l
  simp [SubexpFrontend.renameLiteral, denseLiteral]

@[simp] theorem map_denseClause (F : Formula) (C : Clause) (hC : C ∈ F) :
    (denseClause F C hC).map (SubexpFrontend.renameLiteral (oldVariable F)) = C := by
  unfold denseClause
  rw [List.map_map]
  calc
    _ = C.map id := attach_map_eq_map C _ id (by
      intro l
      exact rename_denseLiteral F C hC l.val l.property)
    _ = C := List.map_id C

@[simp] theorem map_denseRows (F : Formula) :
    (denseRows F).map (List.map (SubexpFrontend.renameLiteral (oldVariable F))) = F := by
  unfold denseRows
  rw [List.map_map]
  calc
    _ = F.map id := attach_map_eq_map F _ id (by
      intro C
      exact map_denseClause F C.val C.property)
    _ = F := List.map_id F

@[simp] theorem denseClause_codes (F : Formula) (C : Clause) (hC : C ∈ F) :
    (denseClause F C hC).map Encoding.literalCode = C.map (code F) := by
  unfold denseClause
  rw [List.map_map]
  exact attach_map_eq_map C _ (code F) (fun _ => rfl)

@[simp] theorem denseRows_codes (F : Formula) :
    (denseRows F).map (List.map Encoding.literalCode) = denseCodes F := by
  unfold denseRows denseCodes
  rw [List.map_map]
  exact attach_map_eq_map F _ (List.map (code F)) (fun C => denseClause_codes F C.val C.property)

@[simp] theorem physicalRows_codes (F : Formula) :
    (physicalRows F).map (List.map Encoding.literalCode) = physicalCodes F := by
  have hinner : ((denseRows F).map List.reverse).map (List.map Encoding.literalCode) =
      ((denseRows F).map (List.map Encoding.literalCode)).map List.reverse := by
    simp only [List.map_map, Function.comp_def, List.map_reverse]
  unfold physicalRows physicalCodes
  rw [List.map_reverse, hinner, denseRows_codes]

private theorem eval_formulaSet {V : Type*} [DecidableEq V]
    (F : List (List (SAT.Literal V))) (a : V → Bool) :
    SAT.CNF.eval a (ExecCNF.formulaSet F) = F.all (fun C => C.any (fun l => l.eval a)) := by
  apply Bool.eq_iff_iff.mpr
  simp [SAT.CNF.eval, SAT.Clause.eval, ExecCNF.formulaSet, ExecCNF.clauseSet]

private theorem eval_map_rows {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : V → W) (F : List (List (SAT.Literal V))) (a : W → Bool) :
    SAT.CNF.eval a (ExecCNF.formulaSet (F.map (List.map (SubexpFrontend.renameLiteral f)))) =
      SAT.CNF.eval (a ∘ f) (ExecCNF.formulaSet F) := by
  rw [eval_formulaSet, eval_formulaSet]
  simp only [List.all_map, List.any_map, Function.comp_def, SubexpFrontend.eval_renameLiteral]

@[simp] theorem eval_denseRows (F : Formula) (a : Word → Bool) :
    SAT.CNF.eval (a ∘ oldVariable F) (ExecCNF.formulaSet (denseRows F)) = (semantics F).eval a := by
  have h := eval_map_rows (oldVariable F) (denseRows F) a
  rw [map_denseRows] at h
  exact h.symm

def extendAssignment (F : Formula) (a : Fin (dimension F) → Bool) : Word → Bool :=
  fun id => if h : id ∈ dictionary F then a (rank F id h) else false

@[simp] theorem extendAssignment_oldVariable (F : Formula)
    (a : Fin (dimension F) → Bool) (i : Fin (dimension F)) :
    extendAssignment F a (oldVariable F i) = a i := by
  have hi : oldVariable F i ∈ dictionary F := List.get_mem _ _
  simp only [extendAssignment, dite_eq_left hi, rank_oldVariable]

theorem dense_satisfiable (F : Formula) :
    SAT.Satisfiable (ExecCNF.formulaSet (denseRows F)) ↔ SAT.Satisfiable (semantics F) := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨extendAssignment F a, ?_⟩
    rw [← eval_denseRows]
    have h : extendAssignment F a ∘ oldVariable F = a := by
      funext i
      exact extendAssignment_oldVariable F a i
    rw [h]
    exact ha
  · rintro ⟨a, ha⟩
    exact ⟨a ∘ oldVariable F, (eval_denseRows F a).trans ha⟩

theorem physical_set_eq (F : Formula) :
    ExecCNF.formulaSet (physicalRows F) = ExecCNF.formulaSet (denseRows F) := by
  simp [physicalRows, ExecCNF.formulaSet, ExecCNF.clauseSet, List.map_map, Function.comp_def]
  rfl

theorem physical_satisfiable (F : Formula) :
    SAT.Satisfiable (ExecCNF.formulaSet (physicalRows F)) ↔ SAT.Satisfiable (semantics F) := by
  rw [physical_set_eq]
  exact dense_satisfiable F

@[simp] theorem denseClause_length (F : Formula) (C : Clause) (hC : C ∈ F) :
    (denseClause F C hC).length = C.length := by simp [denseClause]

@[simp] theorem denseRows_length (F : Formula) : (denseRows F).length = F.length := by
  simp [denseRows]

theorem physical_rawWidth (F : Formula) (k : ℕ) (h : ∀ C ∈ F, C.length ≤ k) :
    ∀ C ∈ physicalRows F, C.length ≤ k := by
  intro C hC
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hC)
  obtain ⟨E, _, rfl⟩ := List.mem_map.mp hD
  simpa only [List.length_reverse, denseClause_length] using h E.val E.property

theorem physical_width (F : Formula) (k : ℕ) (h : ∀ C ∈ F, C.length ≤ k) :
    SAT.WidthAtMost k (ExecCNF.formulaSet (physicalRows F)) := by
  rw [physical_set_eq]
  intro C hC
  obtain ⟨D, hD, rfl⟩ := ExecCNF.mem_formulaSet.mp hC
  obtain ⟨E, _, rfl⟩ := List.mem_map.mp hD
  exact (List.toFinset_card_le _).trans (by
    rw [denseClause_length]
    exact h E.val E.property)

theorem code_lt (F : Formula) (C : Clause) (hC : C ∈ F) (l : Literal) (hl : l ∈ C) :
    code F l < 2 * dimension F := by
  have hr : (dictionary F).idxOf l.variable < (dictionary F).length := by
    simpa only [List.idxOf, beq_eq_decide] using
      List.idxOf_lt_length_iff.mpr (literal_id_mem F C hC l hl)
  unfold code dimension
  cases hp : l.positive <;> simp [] <;> omega

/-- The unary dense output is polynomial in the original encoded byte
length, independently of the largest numeric variable identifier. -/
theorem output_length_le (F : Formula) :
    (outputWord F).length ≤ 16 * ((encode F).length + 1)^3 := by
  let L := (encode F).length
  let K := 1 + (4 * L + 2) * L
  have hd : dimension F ≤ L := dimension_le_bytes F
  have hF : F.length ≤ L := formula_length_le_bytes F
  have hclause (C : Clause) (hC : C ∈ F) :
      (Encoding.encodeList Encoding.encodeNat (C.map (code F)).reverse).length ≤ K := by
    have hc := clause_length_le_input F C hC
    have hb := Encoding.length_encodeList_upper Encoding.encodeNat (C.map (code F)).reverse (2 * L) (by
      intro n hn
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hn)
      have hlb := code_lt F C hC l hl
      rw [Encoding.length_encodeNat]
      omega)
    simp only [List.length_reverse, List.length_map] at hb
    exact hb.trans (by
      dsimp [K]
      nlinarith)
  have hall := Encoding.length_encodeList_upper (Encoding.encodeList Encoding.encodeNat)
    (physicalCodes F) K (by
      intro C hC
      change C ∈ ((F.map (List.map (code F))).map List.reverse).reverse at hC
      have hm : C ∈ (F.map (List.map (code F))).map List.reverse := List.mem_reverse.mp hC
      obtain ⟨B, hB, hBC⟩ := List.mem_map.mp hm
      obtain ⟨D, hD, hDB⟩ := List.mem_map.mp hB
      rw [← hBC, ← hDB]
      exact hclause D hD)
  have hlen : (physicalCodes F).length = F.length := by
    simp [physicalCodes, denseCodes]
  rw [hlen] at hall
  simp only [outputWord, List.length_append, Encoding.length_encodeNat]
  dsimp [K] at hall
  change dimension F + 1 + _ ≤ 16 * (L + 1)^3
  have hmul := Nat.mul_le_mul_left (2 * (1 + (4 * L + 2) * L) + 2) hF
  nlinarith

theorem item_bytes_le {A : Type*} (enc : A → Word) (xs : List A) (x : A) (hx : x ∈ xs) :
    (enc x).length ≤ (Encoding.encodeList enc xs).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      rw [Encoding.length_encodeList_cons]
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · exact (ih hx).trans (by omega)

theorem literal_bytes_le_input (F : Formula) (C : Clause) (hC : C ∈ F)
    (l : Literal) (hl : l ∈ C) : (literalBytes l).length ≤ (encode F).length :=
  (item_bytes_le literalBytes C l hl).trans (item_bytes_le clauseBytes F C hC)

theorem dictionary_item_bytes_le (F : Formula) (id : Word) (hid : id ∈ dictionary F) :
    id.length ≤ (encode F).length := by
  rw [mem_dictionary] at hid
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hid
  obtain ⟨C, hC, hl⟩ := List.mem_flatten.mp hl
  have h := literal_bytes_le_input F C hC l hl
  rw [literalBytes_length] at h
  omega

theorem collected_bytes_le (F : Formula) :
    (Encoding.encodeList id (ids F).reverse).length ≤ 3 * ((encode F).length + 1)^2 := by
  have hn := occurrences_le_bytes F
  have h := Encoding.length_encodeList_upper id (ids F).reverse (encode F).length (by
    intro id hid
    apply dictionary_item_bytes_le F id
    rw [mem_dictionary]
    exact List.mem_reverse.mp hid)
  simp only [List.length_reverse] at h
  have hlen : (ids F).length = F.flatten.length := by simp only [ids, List.length_map]
  rw [hlen] at h
  have hmul := Nat.mul_le_mul_left (2 * (encode F).length + 2) hn
  nlinarith

theorem dictionary_bytes_le (F : Formula) :
    (Encoding.encodeList id (dictionary F)).length ≤ 3 * ((encode F).length + 1)^2 := by
  have hd := dimension_le_bytes F
  have h := Encoding.length_encodeList_upper id (dictionary F) (encode F).length
    (dictionary_item_bytes_le F)
  change (dictionary F).length ≤ (encode F).length at hd
  nlinarith

/-- A finite declared domain also bounds the number of distinct IDs that
actually occur, regardless of the byte encoding chosen for each variable. -/
theorem dimension_renamed_le_card {V : Type*} [Fintype V]
    (f : V → Word) (F : List (List (SAT.Literal V))) :
    dimension (F.map (List.map (SubexpFrontend.renameLiteral f))) ≤ Fintype.card V := by
  classical
  let G : Formula := F.map (List.map (SubexpFrontend.renameLiteral f))
  change dimension G ≤ Fintype.card V
  have hsub : (dictionary G).toFinset ⊆ Finset.univ.image f := by
    intro word hword
    have hm := (mem_dictionary G word).mp (List.mem_toFinset.mp hword)
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hm
    obtain ⟨C, hC, hl⟩ := List.mem_flatten.mp hl
    obtain ⟨C, _, rfl⟩ := List.mem_map.mp hC
    obtain ⟨l, _, rfl⟩ := List.mem_map.mp hl
    exact Finset.mem_image.mpr ⟨l.variable, Finset.mem_univ _, rfl⟩
  calc
    dimension G = (dictionary G).toFinset.card :=
      (List.toFinset_card_of_nodup (dictionary_nodup G)).symm
    _ ≤ (Finset.univ.image f).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset V).card := Finset.card_image_le
    _ = Fintype.card V := Finset.card_univ

theorem dimension_fin_le {n : ℕ} (F : List (List (SAT.Literal (Fin n)))) :
    dimension (F.map (List.map (SubexpFrontend.renameLiteral
      (fun i : Fin n => Nat.bits i.val)))) ≤ n := by
  simpa using dimension_renamed_le_card (fun i : Fin n => Nat.bits i.val) F

/-- Numeric IDs enter only through their canonical bit representation;
renaming never expands their magnitude to a unary domain. -/
theorem numeric_satisfiable (F : List (List (SAT.Literal ℕ))) :
    SAT.Satisfiable (semantics (numericFormula F)) ↔ SAT.Satisfiable (ExecCNF.formulaSet F) := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a ∘ Nat.bits, ?_⟩
    have h := eval_map_rows Nat.bits F a
    exact h.symm.trans ha
  · rintro ⟨a, ha⟩
    let b : Word → Bool := fun bits => a (BinaryArithmetic.toNat bits)
    refine ⟨b, ?_⟩
    have h := eval_map_rows Nat.bits F b
    have hb : b ∘ Nat.bits = a := by
      funext n
      simp [b ]
    rw [hb] at h
    exact h.trans ha

end SubexponentialSAT.Subexp.RawIdRenaming

end OAI.Algorithms
