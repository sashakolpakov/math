import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeCost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsNativeCostBridge

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.NodeTime
open SubexponentialSAT LeafProgram LeafProgram.NodeNative LeafHeadSetupProgram MomentsAssembly

theorem support_cost_le (n J Z : ℕ) (hZ : 1 ≤ Z) (hn : n ≤ Z) (hJ : J ≤ Z)
    (hp : 0 < J) (hc : SupportProgram.count n J ≤ Z) :
    LeafSupportInputProgram.cost n J ≤ 20000*Z^3 := by
  have hh := SupportProgram.Loop.cost_le n J hp
  have hh' : 3000*(n+1)*(n+J+1)*SupportProgram.count n J ≤ 18000*Z^3 := by
    calc
      _ ≤ 3000*(2*Z)*(3*Z)*Z := by gcongr <;> omega
      _ = _ := by ring
  have ht : SupportProgram.count n J*(11*n+13) ≤ 24*Z^2 := by
    calc
      _ ≤ Z*(24*Z) := by gcongr; omega
      _ = _ := by ring
  have h2 : Z^2 ≤ Z^3 := Nat.pow_le_pow_right hZ (by decide)
  have h1 : Z ≤ Z^3 := by simpa using Nat.pow_le_pow_right hZ (show 1 ≤ 3 by decide)
  have h0 : 1 ≤ Z^3 := Nat.one_le_pow _ _ hZ
  unfold LeafSupportInputProgram.cost LeafSupportInputProgram.Local.cost
  omega

/-- The measured dense loop and every non-head node operation. Payload sizes
are explicit parameters; none are replaced by an input-bit estimate. -/
theorem localBudget_le (s : HeadInputs) (input K B d u J H X Y A W Z : ℕ)
    (hZ : 1 ≤ Z) (hi : input ≤ Z) (hk : K ≤ Z) (hb : B ≤ Z) (hd : d ≤ Z)
    (hn : s.n ≤ Z) (hu : u ≤ Z) (hj : J ≤ Z) (hjp : 0 < J)
    (hL : dictionaryCapacity (Finset.univ : Finset (Fin s.n)) u J ≤ Z)
    (hH : H ≤ Z) (hX : X ≤ Z) (hY : Y ≤ Z) (hA : A ≤ Z) (hW : W ≤ Z)
    (hS : SupportProgram.count s.n J ≤ Z) :
    localBudget s input K B d u J H X Y A W ≤ 4100000*Z^10 := by
  have hs := support_cost_le s.n J Z hZ hn hj hjp hS
  have hw := MomentsNativeCostBridge.work_le B d s.n u J
    (dictionaryCapacity (Finset.univ : Finset (Fin s.n)) u J) H X Y
    (SupportProgram.count s.n J) A K Z hZ hb hd hn hu hj hL hH hX hY hS hA hk
  change Relational.denseBudget B d s.n u J
    (dictionaryCapacity (Finset.univ : Finset (Fin s.n)) u J) H X Y
    (SupportProgram.count s.n J) K A+1 ≤ 4000000*Z^10 at hw
  have hc : Node.cleanupPorts.length ≤ 10000 := by
    calc
      Node.cleanupPorts.length ≤ (List.finRange 768).length := by
        unfold Node.cleanupPorts
        exact List.length_filter_le _ _
      _ = 768 := by simp
      _ ≤ 10000 := by omega
  have hclean : Node.cleanupPorts.length*(2*W+3) ≤ 50000*Z := by
    calc
      _ ≤ 10000*(5*Z) := by gcongr; omega
      _ = _ := by ring
  have h3 : Z^3 ≤ Z^10 := Nat.pow_le_pow_right hZ (by decide)
  have h1 : Z ≤ Z^10 := by simpa using Nat.pow_le_pow_right hZ (show 1 ≤ 10 by decide)
  have h0 : 1 ≤ Z^10 := Nat.one_le_pow _ _ hZ
  unfold localBudget
  omega

end SubexponentialSAT.SqrtLog.NodeTime

end OAI.Algorithms
