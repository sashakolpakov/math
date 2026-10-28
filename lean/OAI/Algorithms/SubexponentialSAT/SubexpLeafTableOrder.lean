import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpClauseTableCorrectness
import OAI.Algorithms.SubexponentialSAT.SubexpUnaryOrderedTable
import OAI.Algorithms.SubexponentialSAT.SubexpClauseFamilyProgram
import OAI.Algorithms.SubexponentialSAT.SubexpUnaryFamily

namespace OAI.Algorithms

/-! Exact Boolean table payloads in the physical unary-then-clause factor
order. Labels are interpreted by the descending LE grid, not asserted to have
been serialized by the Boolean-only table constructor. -/

namespace SubexponentialSAT.SubexpLeafTableOrder

open SubexpTableInterpolation SubexpLeafTables

private theorem zip_rows_values {p k : ℕ} (labels : List (List.Vector (Fin p) k))
    (answers : List Bool) (hlen : labels.length = answers.length) :
    (labels.zipWith Row.mk answers).map Row.value = answers := by
  induction labels generalizing answers with
  | nil =>
      have ha : answers = [] := List.length_eq_zero_iff.mp hlen.symm
      subst answers
      rfl
  | cons label labels ih =>
      cases answers with
      | nil => simp at hlen
      | cons answer answers =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          simpa only [List.zipWith_cons_cons, List.map_cons] using
            congrArg (List.cons answer) (ih answers hlen)

theorem attachAnswers_values {p k : ℕ} (answers : List Bool)
    (hlen : answers.length = p ^ k) :
    (SubexpRankedTable.attachAnswers (p := p) (k := k) false true answers).map Row.value = answers := by
  have hb : (fun b : Bool => if b = true then true else false) = id := by
    funext b; cases b <;> rfl
  unfold SubexpRankedTable.attachAnswers
  rw [hb, List.map_id]
  exact zip_rows_values _ answers (by simpa using hlen.symm)

variable {D p : ℕ} [Fact p.Prime] {F : Type*}

def scopeTable (S : Factor.System (Fin D) F (ZMod p)) (e : F)
    (scope : List (Fin D)) (hn : scope.Nodup)
    (hm : ∀ j, j ∈ scope ↔ j ∈ S.scope e) : List Bool :=
  (orderedRows S e (scopeOfList S e scope hn hm) false true).map Row.value

theorem scopeTable_congr (S : Factor.System (Fin D) F (ZMod p)) (e : F)
    (a b : List (Fin D)) (ha : a.Nodup) (hb : b.Nodup)
    (hma : ∀ j, j ∈ a ↔ j ∈ S.scope e) (hmb : ∀ j, j ∈ b ↔ j ∈ S.scope e)
    (h : a = b) : scopeTable S e a ha hma = scopeTable S e b hb hmb := by
  subst b
  rfl

section Canonical

variable {n ell : ℕ}

noncomputable def factorTable (G : SubexpLeafData.Leaf n) (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p)
    (e : Fin (ChunkPartition.count n ell) ⊕ {C // C ∈ ExecCNF.formulaSet G}) : List Bool :=
  scopeTable (SubexpLEFactorSystem.packed hell hcap (ExecCNF.formulaSet G)) e
    (SubexpLeafData.scopes G hG (ChunkPartition.indexEquiv n ell hell) e)
    (SubexpLeafData.scopes_nodup G hG (ChunkPartition.indexEquiv n ell hell) e)
    (SubexpLeafData.scopes_mem G hG (ChunkPartition.indexEquiv n ell hell)
      (PackedSAT.capacity (n := n) hcap) e)

noncomputable def orderedTables (G : SubexpLeafData.Leaf n) (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) : List (List Bool) :=
  (SubexpLeafData.factors (D := ChunkPartition.count n ell) G hG).values.map
    (factorTable G hG hell hcap)

theorem clause_table_eq (c : SubexpClauseFamilyProgram.Inputs)
    (hv : SubexpClauseFamilyProgram.Valid c
      (ChunkPartition.count n (BinaryArithmetic.toNat c.binaryEll)) n)
    (G : SubexpLeafData.Leaf n) (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hcap : 2 ^ BinaryArithmetic.toNat c.binaryEll ≤ p)
    (hp : BinaryArithmetic.toNat c.modulus = p)
    (e : {C // C ∈ ExecCNF.formulaSet G}) :
    SubexpClauseFamilyProgram.table c hv (SubexpLeafData.literals G hG e) =
      factorTable G hG hv.ell_pos hcap (.inr e) := by
  let ls := SubexpLeafData.literals G hG e
  let cc := SubexpClauseFamilyCallback.withClause c ls
  let hc := SubexpClauseFamilyCallback.validClause c hv ls
  let S := SubexpLEFactorSystem.packed hv.ell_pos hcap (ExecCNF.formulaSet G)
  let scope := SubexpClauseFamilyCallback.scope c hv ls
  have hls : ls.toFinset = e.val := SubexpLeafData.literals_set G hG e
  have h := SubexpClauseTableCorrectness.table_eq_orderedRows cc ls hc
    (ExecCNF.formulaSet G) e hls hcap false true hp
  have hvalues := congrArg (List.map Row.value) h
  have hlen : (SubexpClauseFamilyProgram.table c hv ls).length = p ^ scope.length := by
    calc
      _ = BinaryArithmetic.toNat c.modulus ^ scope.length :=
        SubexpClauseFamilyCallback.table_length c hv ls
      _ = p ^ scope.length := by rw [hp]
  have hrawlen :
      (SubexpClauseFactorProgram.table cc (SubexpClauseFactorProgram.scopeOf cc ls hc) ls).length =
        p ^ (SubexpClauseFactorProgram.scopeOf cc ls hc).length := hlen
  have hv' := (attachAnswers_values
    (SubexpClauseFactorProgram.table cc (SubexpClauseFactorProgram.scopeOf cc ls hc) ls) hrawlen).symm.trans hvalues
  have hn := SubexpClauseFamilyCallback.scope_nodup c hv ls
  have hm : ∀ j, j ∈ scope ↔ j ∈ S.scope (.inr e) :=
    SubexpClauseScopeCorrectness.scopeOf_mem_cnfScope cc ls hv.ell_pos hc
      (ExecCNF.formulaSet G) e hls
  have hs : scope = SubexpLeafData.scopes G hG
      (ChunkPartition.indexEquiv n (BinaryArithmetic.toNat c.binaryEll) hv.ell_pos) (.inr e) :=
    SubexpClauseScopeCorrectness.scopeOf_eq_clauseScope cc ls hv.ell_pos hc
  change SubexpClauseFamilyProgram.table c hv ls = scopeTable S (.inr e) scope hn hm at hv'
  exact hv'.trans (scopeTable_congr S (.inr e) _ _ hn
    (SubexpLeafData.scopes_nodup G hG
      (ChunkPartition.indexEquiv n (BinaryArithmetic.toNat c.binaryEll) hv.ell_pos) (.inr e)) hm
    (SubexpLeafData.scopes_mem G hG
      (ChunkPartition.indexEquiv n (BinaryArithmetic.toNat c.binaryEll) hv.ell_pos)
      (PackedSAT.capacity (n := n) hcap) (.inr e)) hs)

theorem unary_table_eq (G : SubexpLeafData.Leaf n)
    (hG : (G.map ExecCNF.clauseSet).Nodup) (hell : 0 < ell) (hcap : 2 ^ ell ≤ p)
    (j : Fin (ChunkPartition.count n ell)) :
    SubexpUnaryFactorTable.table (ChunkPartition.size n ell j) p =
      factorTable G hG hell hcap (.inl j) := by
  let positions := ChunkPartition.indexEquiv n ell hell
  let S := SubexpLEFactorSystem.packed hell hcap (ExecCNF.formulaSet G)
  let index := scopeOfList S (.inl j) (SubexpLeafData.scopes G hG positions (.inl j))
    (SubexpLeafData.scopes_nodup G hG positions (.inl j))
    (SubexpLeafData.scopes_mem G hG positions (PackedSAT.capacity (n := n) hcap) (.inl j))
  exact SubexpUnaryOrderedTable.table_eq_orderedRows positions
    (PackedSAT.capacity (n := n) hcap) (ExecCNF.formulaSet G) j index

private theorem map_get_finRange {α β : Type*} (xs : List α) (f : α → β) :
    (List.finRange xs.length).map (fun i => f (xs.get i)) = xs.map f := by
  rw [← List.ofFn_eq_map]
  simpa only [Function.comp_def, List.ofFn_get] using
    (List.map_ofFn (f := xs.get) (g := f)).symm

theorem prefix_tables_eq (modulus : List Bool) (hp : BinaryArithmetic.toNat modulus = p)
    (G : SubexpLeafData.Leaf n) (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) :
    SubexpUnaryFamily.chunkTables n ell modulus =
      (List.finRange (ChunkPartition.count n ell)).map
        (fun j => factorTable G hG hell hcap (.inl j)) := by
  calc
    _ = (List.finRange (ChunkPartition.count n ell)).map
        (fun j => SubexpUnaryFactorTable.table (ChunkPartition.size n ell j) p) := by
      simp only [SubexpUnaryFamily.chunkTables, SubexpChunkDescriptorEncoding.widths,
        List.map_map, Function.comp_def, CounterPrograms.value_eq_toNat, hp]
      rw [← List.map_coe_finRange (ChunkPartition.count n ell), List.map_map] ; rfl
    _ = _ := by
      apply List.map_congr_left
      intro j _
      exact unary_table_eq G hG hell hcap j

theorem family_tables_eq (c : SubexpClauseFamilyProgram.Inputs)
    (hv : SubexpClauseFamilyProgram.Valid c
      (ChunkPartition.count n (BinaryArithmetic.toNat c.binaryEll)) n)
    (G : SubexpLeafData.Leaf n) (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hcap : 2 ^ BinaryArithmetic.toNat c.binaryEll ≤ p)
    (hp : BinaryArithmetic.toNat c.modulus = p) :
    SubexpClauseFamilyProgram.tables c hv G =
      (List.finRange G.length).map (fun i => factorTable G hG hv.ell_pos hcap
        (.inr (SubexpLeafData.clauseEquiv G hG i))) := by
  change G.map (SubexpClauseFamilyProgram.table c hv) = _
  rw [← map_get_finRange G (SubexpClauseFamilyProgram.table c hv)]
  apply List.map_congr_left
  intro i _
  simpa only [SubexpLeafData.literals_at] using
    clause_table_eq c hv G hG hcap hp (SubexpLeafData.clauseEquiv G hG i)

/-- The whole physical table payload list is in the exact semantic factor
order, including the unary prefix and every clause's actual literal order. -/
theorem produced_tables_eq (c : SubexpClauseFamilyProgram.Inputs)
    (hv : SubexpClauseFamilyProgram.Valid c
      (ChunkPartition.count n (BinaryArithmetic.toNat c.binaryEll)) n)
    (G : SubexpLeafData.Leaf n) (hG : (G.map ExecCNF.clauseSet).Nodup)
    (hcap : 2 ^ BinaryArithmetic.toNat c.binaryEll ≤ p)
    (hp : BinaryArithmetic.toNat c.modulus = p) :
    SubexpUnaryFamily.chunkTables n (BinaryArithmetic.toNat c.binaryEll) c.modulus ++
      SubexpClauseFamilyProgram.tables c hv G = orderedTables G hG hv.ell_pos hcap := by
  unfold orderedTables
  simp only [SubexpLeafData.factors, List.map_append, List.map_map, Function.comp_def]
  exact congrArg₂ List.append (prefix_tables_eq c.modulus hp G hG hv.ell_pos hcap)
    (family_tables_eq c hv G hG hcap hp)

theorem family_tables_dimension_eq {D₁ D₂ n : ℕ}
    (c : SubexpClauseFamilyProgram.Inputs)
    (h₁ : SubexpClauseFamilyProgram.Valid c D₁ n)
    (h₂ : SubexpClauseFamilyProgram.Valid c D₂ n) (G : SubexpLeafData.Leaf n)
    (hD : D₁ = D₂) :
    SubexpClauseFamilyProgram.tables c h₁ G = SubexpClauseFamilyProgram.tables c h₂ G := by
  subst D₂
  rfl

end Canonical

end SubexponentialSAT.SubexpLeafTableOrder

end OAI.Algorithms
