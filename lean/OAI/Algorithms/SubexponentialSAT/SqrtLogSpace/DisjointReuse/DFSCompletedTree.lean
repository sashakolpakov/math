import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CountDFS

/-! A completed concrete transition history determines a proof-only branch
forest backwards. This transfers the sharp tree-node bound to the actual
number of visits, without storing a tree or list of visits on the machine.
-/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCompletedTree

open SparseDFSRefinement
variable {n : ℕ}

inductive Forest (k M : ℕ) : List (Node n) → List BranchTree.Tree → Prop
  | nil : Forest k M [] []
  | cons {node nodes tree trees} : Derivation k M node.formula tree →
      Forest k M nodes trees → Forest k M (node :: nodes) (tree :: trees)

def nodes (trees : List BranchTree.Tree) : ℕ := (trees.map BranchTree.Tree.nodeCount).sum

theorem transition_backward {k M : ℕ} {s t : Frontier n} {trees : List BranchTree.Tree}
    (h : Transition k M s t) (hf : Forest k M t.pending trees) :
    ∃ earlier, Forest k M s.pending earlier ∧ nodes earlier = nodes trees + 1 := by
  cases h with
  | leaf node rest total hnone =>
    refine ⟨.leaf :: trees, .cons (.leaf hnone) hf, ?_⟩
    simp [nodes, BranchTree.Tree.nodeCount, Nat.add_comm]
  | branch node rest total c H hv hp =>
    cases hf with
    | cons left tail =>
      cases tail with
      | cons right tail =>
        refine ⟨_ :: _, .cons (.branch hv hp left right) tail, ?_⟩
        simp only [nodes, List.map_cons, List.sum_cons, BranchTree.Tree.nodeCount]
        omega

theorem transitions_backward {k M visits : ℕ} {s t : Frontier n}
    (h : Transitions k M visits s t) {trees : List BranchTree.Tree}
    (hf : Forest k M t.pending trees) :
    ∃ earlier, Forest k M s.pending earlier ∧ nodes earlier = visits + nodes trees := by
  induction h generalizing trees with
  | refl => exact ⟨trees, hf, by omega⟩
  | cons first _ ih =>
    obtain ⟨middle, hm, hsum⟩ := ih hf
    obtain ⟨earlier, he, hnodes⟩ := transition_backward first hm
    exact ⟨earlier, he, by omega⟩

/-- Exact visit count, independent of the physical selector's tie breaking. -/
theorem completed_tree {k M visits total : ℕ} {F : RawCNF n}
    (h : Transitions k M visits ⟨[⟨F, 0⟩], 0⟩ ⟨[], total⟩) :
    ∃ tree, Derivation k M F tree ∧ tree.nodeCount = visits := by
  obtain ⟨trees, ht, hnodes⟩ := transitions_backward h Forest.nil
  cases ht with
  | cons root tail =>
    cases tail
    exact ⟨_, root, by simpa [nodes] using hnodes⟩

theorem completed_visits_bound {F : RawCNF n} {visits total : ℕ}
    (k : ℕ) (σ : ℚ) (hk : 2 ≤ k) (hσ : 0 < σ) (hv : Valid k F)
    (h : Transitions k (SparseBudget.chooseForSigma k σ hσ) visits
      ⟨[⟨F, 0⟩], 0⟩ ⟨[], total⟩) :
    (visits : ℝ) ≤
      ((SparseCharging.depthConstant k (SparseBudget.chooseForSigma k σ hσ) * n + 1 : ℕ) : ℝ) ^ 2 *
        (2 : ℝ) ^ ((σ : ℝ) * n) := by
  obtain ⟨tree, ht, hcount⟩ := completed_tree h
  rw [← hcount]
  exact ht.nodeCount_bound k σ hk hσ hv

/-- The parameter program produces the threshold for the reciprocal budget.
This form matches its natural-number output without rational representation
assumptions at the native interface. -/
theorem completed_visits_reciprocal {F : RawCNF n} {visits total : ℕ}
    (k s : ℕ) (hk : 2 ≤ k) (hs : 0 < s) (hv : Valid k F)
    (h : Transitions k (SparseBudget.chooseM k 1 s (by decide)) visits
      ⟨[⟨F, 0⟩], 0⟩ ⟨[], total⟩) :
    (visits : ℝ) ≤
      ((SparseCharging.depthConstant k (SparseBudget.chooseM k 1 s (by decide)) * n + 1 : ℕ) : ℝ) ^ 2 *
        (2 : ℝ) ^ ((n : ℝ) / s) := by
  have hσ : (0 : ℚ) < 1 / s := div_pos (by norm_num) (by exact_mod_cast hs)
  have hthreshold := SparseBudget.chooseForSigma_reciprocal k s hs hσ
  have bound := completed_visits_bound k (1 / s) hk hσ hv (hthreshold.symm ▸ h)
  simpa only [hthreshold, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
    one_div_mul_eq_div] using bound

/-- A terminating proof measure, never a retained binary machine counter. -/
def potential (s : Frontier n) : ℕ := SparseCountProgram.potential s.model

theorem transition_potential_lt {k M : ℕ} {s t : Frontier n}
    (h : Transition k M s t) (hM : 2 ≤ M) : potential t < potential s := by
  cases h with
  | leaf node rest total hnone =>
    have hp : 0 < 3 ^ SunflowerBranch.literalMass (ExecCNF.formulaSet node.formula) :=
      Nat.pow_pos (by decide)
    simp only [potential, SparseCountProgram.potential, Frontier.model, Node.model,
      List.map_cons, List.sum_cons]
    omega
  | branch node rest total c H hv hp =>
    have priority := hp.toPriority (by omega) hv.width hv.literal_nodup hv.clause_nodup
    have hc : 2 ≤ c := by have := hp.core_nonempty; have := hp.core_proper; omega
    obtain ⟨ha, hb⟩ := SparseCountProgram.priority_literalMass_lt hM priority
    rw [← childA_set node.formula c H hv.literal_nodup] at ha
    rw [← childB_set node.formula c H hc hv.literal_nodup] at hb
    have powers : 3 ^ SunflowerBranch.literalMass (ExecCNF.formulaSet (childA node.formula c H)) +
        3 ^ SunflowerBranch.literalMass (ExecCNF.formulaSet (childB node.formula c H)) <
        3 ^ SunflowerBranch.literalMass (ExecCNF.formulaSet node.formula) := by
      generalize SunflowerBranch.literalMass (ExecCNF.formulaSet node.formula) = m at *
      cases m with
      | zero => omega
      | succ m =>
        have hpa := Nat.pow_le_pow_right (by decide : 0 < 3) (Nat.le_of_lt_succ ha)
        have hpb := Nat.pow_le_pow_right (by decide : 0 < 3) (Nat.le_of_lt_succ hb)
        have hpos : 0 < 3 ^ m := Nat.pow_pos (by decide)
        rw [Nat.pow_succ]
        omega
    simp only [potential, SparseCountProgram.potential, Frontier.model, Node.model,
      List.map_cons, List.sum_cons]
    omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCompletedTree
