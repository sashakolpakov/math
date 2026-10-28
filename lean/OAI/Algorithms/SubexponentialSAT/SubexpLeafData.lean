import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLEFactorSystem
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
import OAI.Algorithms.SubexponentialSAT.ExecCNFCodeTransport

namespace OAI.Algorithms

/-!
# Factor data in the emitted order of a sparse leaf

The input is the actual typed list of literal lists. Clause-set uniqueness is
the normalizer/worklist invariant; no sorted finite-set enumeration is used.
Unary factors precede clauses, and clause scopes retain the last-occurrence
order of the concrete deduplicator.
-/

namespace SubexponentialSAT.SubexpLeafData

open Subexp.ConstructivePacking

variable {n D p : ℕ} {b : Fin D → ℕ} [NeZero p]

abbrev Leaf (n : ℕ) := List (List (SAT.Literal (Fin n)))

variable (G : Leaf n) (hG : (G.map ExecCNF.clauseSet).Nodup)

/-- The actual empty-clause scan supplies the nonempty-scope condition
needed before invoking the layout constructor. -/
theorem clauses_nonempty (hnoempty : [] ∉ G) :
    ∀ C ∈ ExecCNF.formulaSet G, C.Nonempty := by
  intro C hC
  obtain ⟨ls, hls, rfl⟩ := ExecCNF.mem_formulaSet.mp hC
  apply (List.toFinset_nonempty_iff ls).mpr
  exact fun h => hnoempty (h ▸ hls)

/-- The physical clause index and its finite-set semantic clause. -/
def clauseEquiv : Fin G.length ≃ {C // C ∈ ExecCNF.formulaSet G} :=
  (finCongr (List.length_map (as := G) ExecCNF.clauseSet).symm).trans
    (listSubtypeEquiv (G.map ExecCNF.clauseSet) hG
      (fun C => C ∈ ExecCNF.formulaSet G) (by
        intro C
        simp only [ExecCNF.formulaSet, List.mem_toFinset]))

@[simp] theorem clauseEquiv_val (i : Fin G.length) :
    (clauseEquiv G hG i).val = ExecCNF.clauseSet (G.get i) := by
  simp [clauseEquiv, listSubtypeEquiv, List.get_eq_getElem]

/-- Retrieve the original literal order of a semantic clause. -/
def literals (e : {C // C ∈ ExecCNF.formulaSet G}) : List (SAT.Literal (Fin n)) :=
  G.get ((clauseEquiv G hG).symm e)

@[simp] theorem literals_set (e : {C // C ∈ ExecCNF.formulaSet G}) :
    (literals G hG e).toFinset = e.val := by
  exact (clauseEquiv_val G hG ((clauseEquiv G hG).symm e)).symm.trans
    (congrArg Subtype.val ((clauseEquiv G hG).apply_symm_apply e))

@[simp] theorem literals_at (i : Fin G.length) :
    literals G hG (clauseEquiv G hG i) = G.get i := by
  simp [literals]

/-- The exact factor order: all unary chunks, then the emitted clause list. -/
def factors : FiniteEnumeration (Fin D ⊕ {C // C ∈ ExecCNF.formulaSet G}) where
  values := (List.finRange D).map Sum.inl ++
    (List.finRange G.length).map (fun i => Sum.inr (clauseEquiv G hG i))
  nodup := by
    apply List.nodup_append.mpr
    refine ⟨(List.nodup_finRange D).map Sum.inl_injective,
      (List.nodup_finRange G.length).map
        (Sum.inr_injective.comp (clauseEquiv G hG).injective), ?_⟩
    intro x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, _, he⟩ := List.mem_map.mp hy
    exact Sum.inl_ne_inr (hxy.trans he.symm)
  complete := by
    intro e
    cases e with
    | inl j =>
        exact List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    | inr e =>
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨(clauseEquiv G hG).symm e, List.mem_finRange _,
          congrArg Sum.inr ((clauseEquiv G hG).apply_symm_apply e)⟩

variable (positions : Fin n ≃ ((j : Fin D) × Fin (b j)))

/-- The same last-occurrence deduplication used by the raw scope producer. -/
def clauseScope (ls : List (SAT.Literal (Fin n))) : List (Fin D) :=
  ExecCNF.dedupLiterals (ls.map (fun l => (positions l.variable).1))

def scopes : (Fin D ⊕ {C // C ∈ ExecCNF.formulaSet G}) → List (Fin D)
  | .inl j => [j]
  | .inr e => clauseScope positions (literals G hG e)

theorem scopes_nodup (e : Fin D ⊕ {C // C ∈ ExecCNF.formulaSet G}) :
    (scopes G hG positions e).Nodup := by
  cases e with
  | inl j => simp [scopes]
  | inr e => exact ExecCNF.dedupLiterals_nodup _

theorem scopes_mem (capacity : ∀ j, 2 ^ b j ≤ p)
    (e : Fin D ⊕ {C // C ∈ ExecCNF.formulaSet G}) (j : Fin D) :
    j ∈ scopes G hG positions e ↔
      j ∈ (SubexpLEFactorSystem.system positions capacity (ExecCNF.formulaSet G)).scope e := by
  cases e with
  | inl v =>
      change j ∈ [v] ↔ j ∈ ({v} : Finset (Fin D))
      simp
  | inr e =>
      change j ∈ clauseScope positions (literals G hG e) ↔
        j ∈ FactorReduction.cnfScope positions (ExecCNF.formulaSet G) e
      rw [clauseScope, ExecCNF.mem_dedupLiterals, FactorReduction.cnfScope,
        ← literals_set G hG e]
      simp only [List.mem_map, Finset.mem_image, List.mem_toFinset]

/-- The scope stream in the very same unary-then-clause order. -/
theorem scope_stream :
    (factors (D := D) G hG).values.map (scopes G hG positions) =
      (List.finRange D).map (fun j => [j]) ++ G.map (clauseScope positions) := by
  simp only [factors, List.map_append, List.map_map, Function.comp_def, scopes,
    literals_at]
  congr 1
  rw [← List.ofFn_eq_map]
  simpa only [Function.comp_def, List.ofFn_get] using
    (List.map_ofFn (f := G.get) (g := clauseScope positions)).symm

section Canonical

variable {ell : ℕ}

private theorem literalCode_div_two (l : SAT.Literal (Fin n)) :
    Encoding.literalCode l / 2 = l.variable.val := by
  cases l with
  | mk v positive => cases positive <;> simp [Encoding.literalCode] ; omega

/-- The typed chunk scope is exactly the numeric scope produced from the
raw signed literal codes. This equality preserves the deduplication order. -/
theorem clauseScope_codes (hell : 0 < ell) (ls : List (SAT.Literal (Fin n))) :
    (clauseScope (ChunkPartition.indexEquiv n ell hell) ls).map Fin.val =
      ExecCNF.dedupLiterals
        ((ls.map Encoding.literalCode).map (fun code => (code / 2) / ell)) := by
  rw [clauseScope, ← ExecCNFCodeTransport.dedupLiterals_map Fin.val Fin.val_injective]
  congr 1
  simp only [List.map_map, Function.comp_def, ChunkPartition.indexEquiv_chunk_val,
    literalCode_div_two]

end Canonical

end SubexponentialSAT.SubexpLeafData

end OAI.Algorithms
