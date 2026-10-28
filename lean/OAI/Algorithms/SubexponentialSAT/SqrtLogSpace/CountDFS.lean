import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.EncodingBounds

/-! Typed refinement of the concrete streaming frontier.

Depths and derivation trees below are proof indices. The physical pending tape
contains only formula bodies, and every formula keeps the same declared `Fin n`.
The selector and leaf execution contracts must still be supplied by their actual
finite programs; this module does not postulate a final counting service.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement

open SAT SparsePriorityProgram BitProgram StructuredCalls

variable {n : ℕ}

@[simp] theorem binaryNat_eq_countWord (a : ℕ) :
    binaryNat a = OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord a := rfl

structure Node (n : ℕ) where
  formula : RawCNF n
  depth : ℕ

structure Frontier (n : ℕ) where
  pending : List (Node n)
  total : ℕ

def Node.model (node : Node n) : SparseCountProgram.Entry n :=
  ⟨ExecCNF.formulaSet node.formula, node.depth⟩

def Frontier.model (s : Frontier n) : SparseCountProgram.State n :=
  ⟨s.pending.map Node.model, s.total⟩

def pendingBytes (pending : List (Node n)) : List Bool :=
  Encoding.encodeList (fun node => SparseCountProgram.encodeBody node.formula) pending

@[simp] theorem pendingBytes_nil : pendingBytes ([] : List (Node n)) = [false] := rfl

@[simp] theorem pendingBytes_cons (node : Node n) (rest : List (Node n)) :
    pendingBytes (node :: rest) =
      ExecWorklistProgram.record (SparseCountProgram.encodeBody node.formula) ++
        pendingBytes rest := by
  simp [pendingBytes, Encoding.encodeList, ExecWorklistProgram.record]

/-- The loop boundary charges original input and parameter words separately.
Only the invariant ports needed by the count/frontier refinement appear here. -/
structure Boundary (M : List Bool) (s : Frontier n) (d : SparseDFSProgram.Data) : Prop where
  pending : d.stacks 257 = pendingBytes s.pending
  header : d.stacks 258 = Encoding.encodeNat n
  threshold : d.stacks 259 = M
  total : d.stacks 260 = binaryNat s.total
  left_empty : d.stacks 261 = []
  right_empty : d.stacks 262 = []
  leaf_empty : d.stacks 263 = []
  current_empty : d.stacks 265 = []
  low_empty : ∀ i : Fin 1220, i.val < 256 → d.stacks i = []
  continue_flag : d.regs 2 = !s.pending.isEmpty

/-- Normalized syntax invariants are retained even though encountered clause
order differs from the canonical finite-set encoding. -/
structure Valid (k : ℕ) (F : RawCNF n) : Prop where
  literal_nodup : ∀ C ∈ F, C.Nodup
  clause_nodup : (F.map ExecCNF.clauseSet).Nodup
  width : ∀ C ∈ F, C.length ≤ k
  antichain : SunflowerBranch.Antichain (ExecCNF.formulaSet F)
  not_tautological : ∀ C ∈ ExecCNF.formulaSet F, ¬ SAT.Clause.IsTautology C

def childA (F : RawCNF n) (c : ℕ) (H : List (Literal (Fin n))) : RawCNF n :=
  ExecCoreChildProgram.result F (selectedRaw F c H) H

def childB (F : RawCNF n) (c : ℕ) (H : List (Literal (Fin n))) : RawCNF n :=
  DisjointBranchProgram.resultB Literal.negate F (selectedRaw F c H) H

theorem childA_set (F : RawCNF n) (c : ℕ) (H : List (Literal (Fin n)))
    (hnodup : ∀ C ∈ F, C.Nodup) :
    ExecCNF.formulaSet (childA F c H) =
      DisjointBranch.childA (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) :=
  DisjointBranchProgram.resultA_set F (selectedRaw F c H) H c
    (selectedRaw_set F c H hnodup)

theorem childB_set (F : RawCNF n) (c : ℕ) (H : List (Literal (Fin n)))
    (hc : 2 ≤ c) (hnodup : ∀ C ∈ F, C.Nodup) :
    ExecCNF.formulaSet (childB F c H) =
      DisjointBranch.childB (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H) :=
  DisjointBranchProgram.resultB_set F (selectedRaw F c H) H c hc
    (selectedRaw_set F c H hnodup)

theorem children_count {k M c : ℕ} (F : RawCNF n) (H : List (Literal (Fin n)))
    (hp : RawPriority k F M c H) (hnodup : ∀ C ∈ F, C.Nodup) :
    rawCount F = rawCount (childA F c H) + rawCount (childB F c H) :=
  SparseDFSProgram.raw_branch_count F H hp hnodup

/-- Every raw step names the actual disjoint list outputs. Leaf exact counts
here specify the semantic transition, and do not compute a runtime callback. -/
inductive Transition (k M : ℕ) : Frontier n → Frontier n → Prop
  | leaf (node : Node n) (rest : List (Node n)) (total : ℕ) :
      SparsePriority.select (ExecCNF.formulaSet node.formula) M = none →
      Transition k M ⟨node :: rest, total⟩ ⟨rest, total + rawCount node.formula⟩
  | branch (node : Node n) (rest : List (Node n)) (total c : ℕ)
      (H : List (Literal (Fin n))) : Valid k node.formula →
      RawPriority k node.formula M c H →
      Transition k M ⟨node :: rest, total⟩
        ⟨⟨childA node.formula c H, node.depth + 1⟩ ::
          ⟨childB node.formula c H, node.depth + 1⟩ :: rest, total⟩

theorem Transition.model {k M : ℕ} {s t : Frontier n} (h : Transition k M s t) :
    SparseCountProgram.Transition s.model t.model := by
  cases h with
  | leaf node rest total _ => exact .leaf node.model (rest.map Node.model) total
  | branch node rest total c H hv hp =>
      have hc : 2 ≤ c := by have := hp.core_nonempty; have := hp.core_proper; omega
      have ha := childA_set node.formula c H hv.literal_nodup
      have hb := childB_set node.formula c H hc hv.literal_nodup
      simpa only [Frontier.model, Node.model, List.map_cons, ha, hb] using
        SparseCountProgram.Transition.branch node.model (rest.map Node.model) total c
          (ExecCNF.clauseSet H)

inductive Transitions (k M : ℕ) : ℕ → Frontier n → Frontier n → Prop
  | refl (s : Frontier n) : Transitions k M 0 s s
  | cons {s t u : Frontier n} {visits : ℕ} : Transition k M s t →
      Transitions k M visits t u → Transitions k M (visits + 1) s u

theorem Transitions.model {k M visits : ℕ} {s t : Frontier n}
    (h : Transitions k M visits s t) :
    SparseCountProgram.Transitions visits s.model t.model := by
  induction h with
  | refl => exact .refl _
  | cons first _ ih => exact .cons first.model ih

theorem Transitions.finished_count {k M visits total : ℕ} {F : RawCNF n}
    (h : Transitions k M visits ⟨[⟨F, 0⟩], 0⟩ ⟨[], total⟩) :
    total = rawCount F := by
  have hm := h.model.mass_eq
  simpa [Frontier.model, Node.model, SparseCountProgram.mass, rawCount] using hm

theorem Transitions.next_sum_le_pow {k M visits total : ℕ} {F : RawCNF n}
    {node : Node n} {rest : List (Node n)}
    (h : Transitions k M visits ⟨[⟨F, 0⟩], 0⟩ ⟨node :: rest, total⟩) :
    total + rawCount node.formula ≤ 2 ^ n := by
  have hr : SparseCountProgram.Transitions visits
      (SparseCountProgram.initial (ExecCNF.formulaSet F))
      ⟨node.model :: rest.map Node.model, total⟩ := h.model
  exact SparseCountProgram.Transitions.current_sum_le_pow
    (F := ExecCNF.formulaSet F) (node := node.model) (rest := rest.map Node.model) hr


theorem Valid.normalize (F : RawCNF n) {k : ℕ} (hw : ∀ C ∈ F, C.length ≤ k) :
    Valid k (ExecCNF.normalize Literal.negate F) := by
  refine ⟨ExecCNF.normalize_literal_nodup _ _, ExecCNF.normalize_map_nodup _ _,
    normalize_width_le F hw, ?_, ?_⟩
  · rw [ExecCNF.normalize_set]
    exact SunflowerBranch.antichain_normalize _
  · rw [ExecCNF.normalize_set]
    exact fun _ hC => SAT.normalize_not_tautology hC

theorem width_of_formulaSet (F : RawCNF n) {k : ℕ}
    (hnodup : ∀ C ∈ F, C.Nodup) (hw : WidthAtMost k (ExecCNF.formulaSet F)) :
    ∀ C ∈ F, C.length ≤ k := by
  intro C hC
  have h := hw (ExecCNF.clauseSet C) (ExecCNF.mem_formulaSet.mpr ⟨C, hC, rfl⟩)
  simpa only [ExecCNF.clauseSet, List.toFinset_card_of_nodup (hnodup C hC)] using h

theorem Valid.children {k M c : ℕ} {F : RawCNF n} {H : List (Literal (Fin n))}
    (hv : Valid k F) (hp : RawPriority k F M c H) (hM : 0 < M) :
    Valid k (childA F c H) ∧ Valid k (childB F c H) := by
  have hpriority := hp.toPriority hM hv.width hv.literal_nodup hv.clause_nodup
  obtain ⟨C, hCF, _, hsub⟩ := rawCandidate_spec k F c H hp.candidate
  have hH := hsub.nodup (hv.literal_nodup C hCF)
  have hc : 2 ≤ c := by have := hp.core_nonempty; have := hp.core_proper; omega
  have ha := childA_set F c H hv.literal_nodup
  have hb := childB_set F c H hc hv.literal_nodup
  have hna := DisjointBranchProgram.resultA_literal_nodup F (selectedRaw F c H) H
    hv.literal_nodup hH
  have hnb := DisjointBranchProgram.resultB_literal_nodup Literal.negate F (selectedRaw F c H) H
    hv.literal_nodup (fun D hD => hv.literal_nodup D (selectedRaw_subset F c H hD))
  have pathA : SparseCharging.SelectedPath M (ExecCNF.formulaSet F) [false]
      (DisjointBranch.childA (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H)) :=
    .step false hpriority (.nil _)
  have pathB : SparseCharging.SelectedPath M (ExecCNF.formulaSet F) [true]
      (DisjointBranch.childB (ExecCNF.formulaSet F) c (ExecCNF.clauseSet H)) :=
    .step true hpriority (.nil _)
  have ia := SparseCountProgram.selectedPath_invariants pathA hv.antichain hv.not_tautological
    (formulaSet_width_le F hv.width)
  have ib := SparseCountProgram.selectedPath_invariants pathB hv.antichain hv.not_tautological
    (formulaSet_width_le F hv.width)
  rw [← ha] at ia
  rw [← hb] at ib
  exact ⟨⟨hna, DisjointBranchProgram.resultA_clause_nodup _ _ _,
      width_of_formulaSet _ hna ia.2.2, ia.1, ia.2.1⟩,
    ⟨hnb, DisjointBranchProgram.resultB_clause_nodup _ _ _ _,
      width_of_formulaSet _ hnb ib.2.2, ib.1, ib.2.1⟩⟩

/-- This proof-only tree follows the actual encountered-order children. -/
inductive Derivation (k M : ℕ) : RawCNF n → BranchTree.Tree → Prop
  | leaf {F} : SparsePriority.select (ExecCNF.formulaSet F) M = none → Derivation k M F .leaf
  | branch {F c H A B} : Valid k F → RawPriority k F M c H →
      Derivation k M (childA F c H) A → Derivation k M (childB F c H) B →
      Derivation k M F (.branch A B)

theorem Derivation.toPriority {k M : ℕ} {F : RawCNF n} {tree : BranchTree.Tree}
    (h : Derivation k M F tree) (hM : 0 < M) :
    SparseCountProgram.PriorityDerivation M (ExecCNF.formulaSet F) tree := by
  induction h with
  | leaf hnone => exact .leaf hnone
  | @branch F c H A B hv hp _ _ ihA ihB =>
      have hc : 2 ≤ c := by have := hp.core_nonempty; have := hp.core_proper; omega
      rw [childA_set F c H hv.literal_nodup] at ihA
      rw [childB_set F c H hc hv.literal_nodup] at ihB
      exact .branch (hp.toPriority hM hv.width hv.literal_nodup hv.clause_nodup) ihA ihB


theorem Transition.pending_valid {k M : ℕ} {s t : Frontier n}
    (h : Transition k M s t) (hM : 0 < M)
    (hvalid : ∀ node ∈ s.pending, Valid k node.formula) :
    ∀ node ∈ t.pending, Valid k node.formula := by
  cases h with
  | leaf node rest total _ => exact fun e he => hvalid e (List.mem_cons_of_mem _ he)
  | branch node rest total c H hv hp =>
      have hc := hv.children hp hM
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hc.1
      rcases List.mem_cons.mp he with rfl | he
      · exact hc.2
      · exact hvalid e (List.mem_cons_of_mem _ he)

theorem Transitions.pending_valid {k M visits : ℕ} {s t : Frontier n}
    (h : Transitions k M visits s t) (hM : 0 < M)
    (hvalid : ∀ node ∈ s.pending, Valid k node.formula) :
    ∀ node ∈ t.pending, Valid k node.formula := by
  induction h with
  | refl => exact hvalid
  | cons first _ ih => exact ih (first.pending_valid hM hvalid)

theorem selectedPath_append {M : ℕ} {F G H : CNF (Fin n)} {left right : List Bool}
    (hp : SparseCharging.SelectedPath M F left G)
    (hq : SparseCharging.SelectedPath M G right H) :
    SparseCharging.SelectedPath M F (left ++ right) H := by
  induction hp with
  | nil => exact hq
  | step b hpriority _ ih => exact .step b hpriority (ih hq)

theorem Transition.pending_paths {k M : ℕ} {s t : Frontier n} {root : RawCNF n}
    (h : Transition k M s t) (hM : 0 < M)
    (hpaths : ∀ node ∈ s.pending, ∃ bits : List Bool, bits.length = node.depth ∧
      SparseCharging.SelectedPath M (ExecCNF.formulaSet root) bits (ExecCNF.formulaSet node.formula)) :
    ∀ node ∈ t.pending, ∃ bits : List Bool, bits.length = node.depth ∧
      SparseCharging.SelectedPath M (ExecCNF.formulaSet root) bits (ExecCNF.formulaSet node.formula) := by
  cases h with
  | leaf node rest total _ => exact fun e he => hpaths e (List.mem_cons_of_mem _ he)
  | branch node rest total c H hv hp =>
      obtain ⟨bits, hlen, hpath⟩ := hpaths node (List.mem_cons_self)
      have hpriority := hp.toPriority hM hv.width hv.literal_nodup hv.clause_nodup
      have hc : 2 ≤ c := by have := hp.core_nonempty; have := hp.core_proper; omega
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · refine ⟨bits ++ [false], by simp [hlen], ?_⟩
        rw [childA_set node.formula c H hv.literal_nodup]
        exact selectedPath_append hpath (.step false hpriority (.nil _))
      rcases List.mem_cons.mp he with rfl | he
      · refine ⟨bits ++ [true], by simp [hlen], ?_⟩
        rw [childB_set node.formula c H hc hv.literal_nodup]
        exact selectedPath_append hpath (.step true hpriority (.nil _))
      · exact hpaths e (List.mem_cons_of_mem _ he)

theorem Transitions.pending_paths {k M visits : ℕ} {s t : Frontier n} {root : RawCNF n}
    (h : Transitions k M visits s t) (hM : 0 < M)
    (hpaths : ∀ node ∈ s.pending, ∃ bits : List Bool, bits.length = node.depth ∧
      SparseCharging.SelectedPath M (ExecCNF.formulaSet root) bits (ExecCNF.formulaSet node.formula)) :
    ∀ node ∈ t.pending, ∃ bits : List Bool, bits.length = node.depth ∧
      SparseCharging.SelectedPath M (ExecCNF.formulaSet root) bits (ExecCNF.formulaSet node.formula) := by
  induction h with
  | refl => exact hpaths
  | cons first _ ih => exact ih (first.pending_paths hM hpaths)

theorem Transitions.normalized_pending_invariants {k M visits : ℕ} {s : Frontier n}
    (F : RawCNF n) (hM : 2 ≤ M) (hwidth : ∀ C ∈ F, C.length ≤ k)
    (h : Transitions k M visits ⟨[⟨ExecCNF.normalize Literal.negate F, 0⟩], 0⟩ s) :
    (∀ node ∈ s.pending, Valid k node.formula) ∧
      ∀ node ∈ s.pending, node.depth ≤ F.length * k := by
  have hv := h.pending_valid (by omega) (by
    intro node hnode
    obtain rfl := List.mem_singleton.mp hnode
    exact Valid.normalize F hwidth)
  have hp := h.pending_paths (root := ExecCNF.normalize Literal.negate F) (by omega) (by
    intro node hnode
    obtain rfl := List.mem_singleton.mp hnode
    exact ⟨[], rfl, .nil _⟩)
  refine ⟨hv, ?_⟩
  intro node hnode
  obtain ⟨bits, hlen, hpath⟩ := hp node hnode
  rw [ExecCNF.normalize_set] at hpath
  rw [← hlen]
  exact SparseCountProgram.selectedPath_raw_depth_le F hpath hM hwidth



theorem Transitions.trans {k M a b : ℕ} {s t u : Frontier n}
    (h₁ : Transitions k M a s t) (h₂ : Transitions k M b t u) :
    Transitions k M (a + b) s u := by
  induction h₁ with
  | refl => simpa using h₂
  | @cons s v t a hs _ ih =>
      simpa only [Nat.add_assoc, Nat.add_comm 1 b] using Transitions.cons hs (ih h₂)

theorem Derivation.transitions {k M : ℕ} {F : RawCNF n} {tree : BranchTree.Tree}
    (h : Derivation k M F tree) (depth total : ℕ) (rest : List (Node n)) :
    Transitions k M tree.nodeCount ⟨⟨F, depth⟩ :: rest, total⟩
      ⟨rest, total + rawCount F⟩ := by
  induction h generalizing depth total rest with
  | leaf ht => exact .cons (.leaf _ _ _ ht) (.refl _)
  | @branch F c H A B hv hp _ _ ihA ihB =>
      have hs := Transitions.cons
        (Transition.branch ⟨F, depth⟩ rest total c H hv hp)
        ((ihA (depth + 1) total (⟨childB F c H, depth + 1⟩ :: rest)).trans
          (ihB (depth + 1) (total + rawCount (childA F c H)) rest))
      simpa only [BranchTree.Tree.nodeCount, Nat.add_assoc, Nat.add_comm 1,
        ← children_count F H hp hv.literal_nodup] using hs

theorem Derivation.nodeCount_bound {F : RawCNF n} {tree : BranchTree.Tree}
    (k : ℕ) (σ : ℚ) (hk : 2 ≤ k) (hσ : 0 < σ)
    (h : Derivation k (SparseBudget.chooseForSigma k σ hσ) F tree) (hv : Valid k F) :
    (tree.nodeCount : ℝ) ≤
      ((SparseCharging.depthConstant k (SparseBudget.chooseForSigma k σ hσ) * n + 1 : ℕ) : ℝ) ^ 2 *
        (2 : ℝ) ^ ((σ : ℝ) * n) := by
  have hM : 2 ≤ SparseBudget.chooseForSigma k σ hσ :=
    (SparseBudget.chooseM_spec k σ.num.natAbs σ.den
      (SparseBudget.rational_data σ hσ).1).1
  exact (h.toPriority (by omega)).nodeCount_bound k σ hk hσ
    hv.antichain hv.not_tautological (formulaSet_width_le F hv.width)


/-- The encoded core child agrees with the typed result literal by literal. -/
theorem childA_body {n : ℕ} (F S : RawCNF n) (H : List (SAT.Literal (Fin n))) :
    ExecCoreChildProgram.formulaCode
      (ExecCoreChildProgram.result (F.map (List.map Encoding.literalCode))
        (S.map (List.map Encoding.literalCode)) (H.map Encoding.literalCode)) =
      SparseCountProgram.encodeBody (ExecCoreChildProgram.result F S H) := by
  rw [ExecCoreChildProgram.result_map Encoding.literalCode Encoding.literalCode_injective]
  rfl

theorem childB_body {n : ℕ} (F S : RawCNF n) (H : List (SAT.Literal (Fin n))) :
    ExecCoreChildProgram.formulaCode
      (DisjointBranchProgram.resultB SubexpFrontend.negateCode (F.map (List.map Encoding.literalCode))
        (S.map (List.map Encoding.literalCode)) (H.map Encoding.literalCode)) =
      SparseCountProgram.encodeBody (DisjointBranchProgram.resultB SAT.Literal.negate F S H) := by
  rw [DisjointBranchProgram.resultB_codes]
  rfl

theorem typed_branch_execution {n : ℕ} (d : SparseDFSProgram.Data)
    (F S : RawCNF n) (H : List (SAT.Literal (Fin n)))
    (hF : d.stacks 265 = SparseCountProgram.encodeBody F)
    (hH : d.stacks 9 = Encoding.encodeList Encoding.encodeNat (H.map Encoding.literalCode))
    (hS : d.stacks 12 = SparseCountProgram.encodeBody S)
    (hleft : d.stacks 261 = []) (hright : d.stacks 262 = [])
    (hclean : ∀ i : Fin 1220, i.val < 24 → i ≠ 9 → i ≠ 12 → d.stacks i = []) :
    ∃ t ≤ 621000 * (ExecCoreChildProgram.inputVolume
      (F.map (List.map Encoding.literalCode)) (S.map (List.map Encoding.literalCode))
      (H.map Encoding.literalCode)) ^ 2,
      ∃ e, Eval SparseDFSProgram.branch t d e ∧
        e.stacks 257 =
          ExecWorklistProgram.record (SparseCountProgram.encodeBody (ExecCoreChildProgram.result F S H)) ++
          (ExecWorklistProgram.record (SparseCountProgram.encodeBody
            (DisjointBranchProgram.resultB SAT.Literal.negate F S H)) ++ d.stacks 257) ∧
        e.stacks 258 = d.stacks 258 ∧ e.stacks 261 = [] ∧ e.stacks 262 = [] ∧
        e.stacks 265 = [] ∧ e.stacks 259 = d.stacks 259 ∧
        e.stacks 260 = d.stacks 260 := by
  obtain ⟨t, ht, e, he, hout, hframe⟩ := SparseDFSProgram.branch_execution_from_state d
    (F.map (List.map Encoding.literalCode)) (S.map (List.map Encoding.literalCode))
    (H.map Encoding.literalCode) hF hH hS hleft hright hclean
  rw [childA_body F S H, childB_body F S H] at hout
  exact ⟨t, ht, e, he, hout, hframe⟩


/-- Once the actual raw transition refinement reaches an empty frontier,
export copies its canonical exact count to the physical output tape. -/
theorem finished_output {n k M visits total : ℕ} {F : RawCNF n}
    (threshold : List Bool) (d : SparseDFSProgram.Data)
    (htrace : Transitions k M visits ⟨[⟨F, 0⟩], 0⟩ ⟨[], total⟩)
    (hboundary : Boundary (n := n) threshold ⟨[], total⟩ d) :
    ∃ t ≤ 2 * (d.stacks 256).length + 7 * n + 18, ∃ e,
      Eval SparseDFSProgram.exportCount t d e ∧
      e.stacks 256 = binaryNat (rawCount F) ∧ e.stacks 0 = [] ∧
      ∀ i, i ≠ 0 → i ≠ 256 → e.stacks i = d.stacks i := by
  have hcount := htrace.finished_count
  have htotal : d.stacks 260 = binaryNat (rawCount F) := by
    simpa only [hcount] using hboundary.total
  have hzero := hboundary.low_empty 0 (by decide)
  obtain ⟨e, he, hout, hs, hf⟩ := SparseDFSProgram.exportCount_eval d
  refine ⟨_, ?_, e, he, hout.trans htotal, hs, hf⟩
  rw [hzero, htotal]
  have hlen := binaryNat_rawCount_length F
  simp only [List.length_nil]
  omega


/-- Persistent words after a concrete branch or count addition. Scratch and
current-formula cleanup is performed by the real finishVisit command. -/
structure AfterVisit (threshold : List Bool) (s : Frontier n)
    (d : SparseDFSProgram.Data) : Prop where
  pending : d.stacks 257 = pendingBytes s.pending
  header : d.stacks 258 = Encoding.encodeNat n
  threshold_word : d.stacks 259 = threshold
  total : d.stacks 260 = binaryNat s.total
  left_empty : d.stacks 261 = []
  right_empty : d.stacks 262 = []
  leaf_empty : d.stacks 263 = []

theorem finishVisit_boundary (threshold : List Bool) (s : Frontier n)
    (d : SparseDFSProgram.Data) (bound : ℕ)
    (ha : AfterVisit threshold s d) (hbound : ∀ i, (d.stacks i).length ≤ bound) :
    ∃ t ≤ (2 * bound + 3) * 257 + 1, ∃ e,
      Eval SparseDFSProgram.finishVisit t d e ∧ Boundary threshold s e ∧
      (∀ i, 256 ≤ i.val → i ≠ 265 → e.stacks i = d.stacks i) ∧
      ∀ prefixSteps c, prefixSteps ≤ t →
        Trace (compiled SparseDFSProgram.finishVisit 256 256) prefixSteps
          (d.withPC (some (compiled SparseDFSProgram.finishVisit 256 256).entry)) c →
        ∀ i, (c.stacks i).length ≤ bound := by
  obtain ⟨t, ht, e, he, hlow, hcurrent, hframe, hflag, hspace⟩ :=
    SparseDFSResource.finishVisit_execution_space d bound hbound
  refine ⟨t, ht, e, he, ?_, hframe, hspace⟩
  refine ⟨(hframe 257 (by decide) (by decide)).trans ha.pending,
    (hframe 258 (by decide) (by decide)).trans ha.header,
    (hframe 259 (by decide) (by decide)).trans ha.threshold_word,
    (hframe 260 (by decide) (by decide)).trans ha.total,
    (hframe 261 (by decide) (by decide)).trans ha.left_empty,
    (hframe 262 (by decide) (by decide)).trans ha.right_empty,
    (hframe 263 (by decide) (by decide)).trans ha.leaf_empty,
    hcurrent, hlow, ?_⟩
  rw [hflag, ha.pending]
  cases hp : s.pending <;> simp [pendingBytes, Encoding.encodeList]


theorem accumulate_after_leaf (threshold : List Bool) (node : Node n)
    (rest : List (Node n)) (total bound : ℕ) (d : SparseDFSProgram.Data)
    (hpending : d.stacks 257 = pendingBytes rest)
    (hheader : d.stacks 258 = Encoding.encodeNat n)
    (hthreshold : d.stacks 259 = threshold)
    (htotal : d.stacks 260 = binaryNat total)
    (hleft : d.stacks 261 = []) (hright : d.stacks 262 = [])
    (hleaf : d.stacks 263 = binaryNat (rawCount node.formula))
    (hscratch : d.stacks 30 = [])
    (hcount : total + rawCount node.formula ≤ 2 ^ n)
    (hbound : ∀ i, (d.stacks i).length ≤ bound) :
    ∃ t ≤ 100 * (n + 1), ∃ e,
      Eval SparseDFSProgram.accumulate t d e ∧
      AfterVisit threshold ⟨rest, total + rawCount node.formula⟩ e ∧
      (∀ i, i ≠ 260 → i ≠ 263 → i ≠ 30 → e.stacks i = d.stacks i) ∧
      ∀ prefixSteps c, prefixSteps ≤ t →
        Trace (compiled SparseDFSProgram.accumulate 256 256) prefixSteps
          (d.withPC (some (compiled SparseDFSProgram.accumulate 256 256).entry)) c →
        ∀ i, (c.stacks i).length ≤ max (100 * (n + 1)) bound := by
  let regs := d.regs ∘ SparseDFSProgram.registers 8 (by decide)
  have hp : projectState (SparseDFSProgram.registers 8 (by decide)) SparseDFSProgram.countStack d =
      SparseCountProgram.Accumulator.state regs (binaryNat total) (binaryNat (rawCount node.formula)) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i
    · exact htotal
    · exact hleaf
    · exact hscratch
  obtain ⟨t, ht, e, he, ho, hzero, _, hf, hspace⟩ :=
    SparseDFSResource.accumulate_execution_space d regs total (rawCount node.formula) n bound hcount hbound
  rw [← hp, embedState_project _ _ d (SparseDFSProgram.registers 8 (by decide)).injective
    SparseDFSProgram.countStack.injective] at he hspace
  refine ⟨t, ht, e, he, ?_, hf, hspace⟩
  exact ⟨(hf 257 (by decide) (by decide) (by decide)).trans hpending,
    (hf 258 (by decide) (by decide) (by decide)).trans hheader,
    (hf 259 (by decide) (by decide) (by decide)).trans hthreshold,
    ho, (hf 261 (by decide) (by decide) (by decide)).trans hleft,
    (hf 262 (by decide) (by decide) (by decide)).trans hright, hzero⟩


theorem branch_after_selection {k c : ℕ} (threshold : List Bool)
    (node : Node n) (rest : List (Node n)) (total bound : ℕ)
    (H : List (SAT.Literal (Fin n))) (d : SparseDFSProgram.Data)
    (hv : Valid k node.formula)
    (hpriority : SparsePriorityProgram.RawPriority k node.formula
      (BinaryArithmetic.toNat threshold) c H)
    (hpending : d.stacks 257 = pendingBytes rest)
    (hheader : d.stacks 258 = Encoding.encodeNat n)
    (hthreshold : d.stacks 259 = threshold)
    (htotal : d.stacks 260 = binaryNat total)
    (hleft : d.stacks 261 = []) (hright : d.stacks 262 = [])
    (hleaf : d.stacks 263 = [])
    (hF : d.stacks 265 = SparseCountProgram.encodeBody node.formula)
    (hH : d.stacks 9 = Encoding.encodeList Encoding.encodeNat (H.map Encoding.literalCode))
    (hS : d.stacks 12 = SparseCountProgram.encodeBody
      (SparsePriorityProgram.selectedRaw node.formula c H))
    (hclean : ∀ i : Fin 1220, i.val < 24 → i ≠ 9 → i ≠ 12 → d.stacks i = [])
    (hbound : ∀ i, (d.stacks i).length ≤ bound) :
    let S := SparsePriorityProgram.selectedRaw node.formula c H
    let V := ExecCoreChildProgram.inputVolume (node.formula.map (List.map Encoding.literalCode))
      (S.map (List.map Encoding.literalCode)) (H.map Encoding.literalCode)
    let next : Frontier n :=
      ⟨⟨childA node.formula c H, node.depth + 1⟩ ::
        ⟨childB node.formula c H, node.depth + 1⟩ :: rest, total⟩
    ∃ t ≤ 621000 * V ^ 2, ∃ e,
      Eval SparseDFSProgram.branch t d e ∧
      Transition k (BinaryArithmetic.toNat threshold) ⟨node :: rest, total⟩ next ∧
      AfterVisit threshold next e ∧
      ∀ prefixSteps cfg, prefixSteps ≤ t →
        Trace (compiled SparseDFSProgram.branch 256 256) prefixSteps
          (d.withPC (some (compiled SparseDFSProgram.branch 256 256).entry)) cfg →
        ∀ i, (cfg.stacks i).length ≤
          max bound ((pendingBytes rest).length + (n + 1) + 620001 * V ^ 2) := by
  dsimp only
  let S := SparsePriorityProgram.selectedRaw node.formula c H
  have hproject := SparseDFSProgram.splitter_input_projection_of_clean d
    (node.formula.map (List.map Encoding.literalCode)) (S.map (List.map Encoding.literalCode))
    (H.map Encoding.literalCode) hF hH hS hleft hright hclean
  obtain ⟨t, ht, e, he, hspace⟩ := SparseDFSResource.branch_execution_space d
    (d.regs ∘ SparseDFSProgram.registers 15 (by decide)) (d.stacks 257) (d.stacks 258)
    (node.formula.map (List.map Encoding.literalCode)) (S.map (List.map Encoding.literalCode))
    (H.map Encoding.literalCode) bound hbound
  rw [← hproject, embedState_project _ _ d (SparseDFSProgram.registers 15 (by decide)).injective
    SparseDFSProgram.splitterStack.injective] at he hspace
  obtain ⟨u, _, f, hf, hout, hn, hl, hr, _, hm, hcount⟩ :=
    typed_branch_execution d node.formula S H hF hH hS hleft hright hclean
  have hfinal : f = e := Eval.final_unique 256 hf he
  subst f
  have h263 : e.stacks 263 = [] :=
    (SparseDFSResource.branch_preserves_other_high he 263 (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans hleaf
  refine ⟨t, ht, e, he, .branch node rest total c H hv hpriority, ?_, ?_⟩
  · refine ⟨?_, hn.trans hheader, hm.trans hthreshold, hcount.trans htotal, hl, hr, h263⟩
    rw [hout, hpending]
    simp only [pendingBytes_cons, childA, childB, S]
  · simpa only [hpending, hheader, Encoding.length_encodeNat] using hspace


/- Actual frontier boundary decoding. -/
open SparseDFSProgram

theorem popCurrent_boundary (threshold : List Bool) (node : Node n)
    (rest : List (Node n)) (total : ℕ) (d : Data) (bound : ℕ)
    (hb : Boundary threshold ⟨node :: rest, total⟩ d)
    (hbound : ∀ i, (d.stacks i).length ≤ bound) :
    ∃ e, Eval popCurrent (9 * (SparseCountProgram.encodeBody node.formula).length + 11) d e ∧
      e.stacks 265 = SparseCountProgram.encodeBody node.formula ∧
      e.stacks 257 = pendingBytes rest ∧
      (∀ i, i ≠ 265 → i ≠ 257 → e.stacks i = d.stacks i) ∧
      (∀ i, i.val < 256 → e.stacks i = []) ∧
      e.regs 0 = false ∧ e.regs 1 = false ∧ e.regs 2 = true ∧
      ∀ prefixSteps c,
        prefixSteps ≤ 9 * (SparseCountProgram.encodeBody node.formula).length + 11 →
        Trace (compiled popCurrent 256 256) prefixSteps
          (d.withPC (some (compiled popCurrent 256 256).entry)) c →
        ∀ i, (c.stacks i).length ≤ max
          (n + 1 + (pendingBytes rest).length +
            11 * (SparseCountProgram.encodeBody node.formula).length + 13) bound := by
  let a := SparseFrontierProgram.state (d.regs 0) (d.regs 1) (d.regs 2)
    [] (Encoding.encodeNat n)
    (true :: (Encoding.frame (SparseCountProgram.encodeBody node.formula) ++
      pendingBytes rest)) []
  let b := SparseFrontierProgram.state false false true
    (SparseCountProgram.encodeBody node.formula) (Encoding.encodeNat n) (pendingBytes rest) []
  have hinput : embedState (registers 3 (by decide)) frontierStack d a = d := by
    apply embedState_eq_of_ports _ _ d d a (registers 3 (by decide)).injective
      frontierStack.injective
    · intro i
      fin_cases i <;> rfl
    · intro i hi
      rfl
    · intro i
      fin_cases i
      · exact hb.current_empty
      · exact hb.header
      · change d.stacks 257 =
          true :: (Encoding.frame (SparseCountProgram.encodeBody node.formula) ++
            pendingBytes rest)
        simpa only [pendingBytes_cons, ExecWorklistProgram.record, List.cons_append]
          using hb.pending
      · exact hb.low_empty 23 (by decide)
    · intro i hi
      rfl
  obtain ⟨heval, hspace⟩ := SparseDFSResource.popCurrent_execution_space d
    (SparseCountProgram.encodeBody node.formula) (Encoding.encodeNat n) (pendingBytes rest)
    (d.regs 0) (d.regs 1) (d.regs 2) bound hbound
  change Eval popCurrent _ (embedState _ _ d a) (embedState _ _ d b) at heval
  rw [hinput] at heval
  let e := embedState (registers 3 (by decide)) frontierStack d b
  have hout (i : Fin 4) : e.stacks (frontierStack i) = b.stacks i :=
    embedState_stack _ _ _ _ frontierStack.injective i
  have hframe (i : Fin 1220) (hcurrent : i ≠ 265) (hpending : i ≠ 257) :
      e.stacks i = d.stacks i := by
    by_cases hi : ∃ j, frontierStack j = i
    · obtain ⟨j, rfl⟩ := hi
      fin_cases j
      · exact (hcurrent rfl).elim
      · exact (hout 1).trans hb.header.symm
      · exact (hpending rfl).elim
      · exact (hout 3).trans (hb.low_empty 23 (by decide)).symm
    · exact embedState_stack_frame _ _ _ _ i hi
  refine ⟨e, heval, hout 0, hout 2, hframe, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hframe i (by intro h; subst i; omega) (by intro h; subst i; omega)]
    exact hb.low_empty i hi
  · exact embedState_register _ _ _ _ (registers 3 (by decide)).injective 0
  · exact embedState_register _ _ _ _ (registers 3 (by decide)).injective 1
  · exact embedState_register _ _ _ _ (registers 3 (by decide)).injective 2
  · change ∀ prefixSteps c, prefixSteps ≤ _ →
      Trace (compiled popCurrent 256 256) prefixSteps
        ((embedState _ _ d a).withPC _) c → _ at hspace
    rw [hinput] at hspace
    simpa only [Encoding.length_encodeNat] using hspace


/- Typed empty-input cases. -/
section TrivialCases
variable {k M : ℕ}

theorem formulaSet_singleton_empty {F : RawCNF n} (hv : Valid k F) (he : [] ∈ F) :
    ExecCNF.formulaSet F = {∅} := by
  have hem : (∅ : Clause (Fin n)) ∈ ExecCNF.formulaSet F :=
    ExecCNF.mem_formulaSet.mpr ⟨[], he, rfl⟩
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨hem, ?_⟩
  intro C hC
  exact (hv.antichain ∅ hem C hC (Finset.empty_subset C)).symm

theorem select_none_of_trivial {F : RawCNF n} (hv : Valid k F)
    (he : [] ∈ F ∨ F = []) : SparsePriority.select (ExecCNF.formulaSet F) M = none := by
  rcases he with he | rfl
  · rw [formulaSet_singleton_empty hv he, SparsePriority.select_singleton_empty]
  · exact SparsePriority.select_empty M

theorem transition_of_trivial_flag (node : Node n) (rest : List (Node n)) (total : ℕ)
    (hv : Valid k node.formula) (flag : Bool)
    (hflag : flag = decide ([] ∈ node.formula ∨ node.formula = [])) (htrue : flag = true) :
    Transition k M ⟨node :: rest, total⟩ ⟨rest, total + rawCount node.formula⟩ := by
  apply Transition.leaf
  apply select_none_of_trivial hv
  exact of_decide_eq_true (hflag.symm.trans htrue)

theorem trivial_leaf_preserves_pending (node : Node n) (rest : List (Node n)) (total : ℕ)
    (hv : ∀ entry ∈ node :: rest, Valid k entry.formula)
    (he : [] ∈ node.formula ∨ node.formula = []) :
    Transition k M ⟨node :: rest, total⟩ ⟨rest, total + rawCount node.formula⟩ ∧
      ∀ entry ∈ rest, Valid k entry.formula := by
  exact ⟨Transition.leaf node rest total (select_none_of_trivial
      (hv node List.mem_cons_self) he),
    fun entry hentry => hv entry (List.mem_cons_of_mem node hentry)⟩


end TrivialCases

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement
