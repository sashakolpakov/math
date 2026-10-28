import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeTimeHead
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeTimeDense

namespace OAI.Algorithms

noncomputable section
namespace SubexponentialSAT.SqrtLog.NodeTime
open SubexponentialSAT Subexp SubexpLiftRing SubexpSetupStorage MulticolorTypes
open LeafProgram LeafProgram.NodeNative LeafHeadSetupProgram ProducedQueryResources MomentsAssembly

def commonSize (input V W A time : ℕ) : ℕ := input+V+W+A+time+1

def budgetExponent : ℕ := 850

irreducible_def coefficientExponent : ℕ := 2199

/-- Common-size bound for the actual addressed node. The parameter A is a
storage bound and time is the separately measured assignment cost. -/
theorem query_fullBudget_common (query : LeafQueryFrontend.Query) (k occurrence qi : ℕ)
    (hg : LeafParametersProgram.Guard (query.input k))
    (first : Word (problem query k hg).r (problem query k hg).Q)
    (tail : List (Word (problem query k hg).r (problem query k hg).Q))
    (node : Fin (problem query k hg).Q) {a b : NodeNative.Data}
    (pr : Preparation (Native.queryInputsAddressed query k hg first tail node) a b)
    (ha : Ready (Native.queryInputsAddressed query k hg first tail node) a)
    (input V B d u J A time : ℕ) (hb : WordBound input a)
    (hn : ambient query ≤ V) (hB : B ≤ V) (hd : d ≤ V) (hu : u ≤ V) (hJ : J ≤ V)
    (hJp : 0 < J) (h243 : a.stacks 243=List.replicate J true)
    (hS : SupportProgram.count (ambient query) J ≤
      CostAssembly.assembledWork k (ambient query) (resources query k occurrence qi hg first tail)) :
    fullBudget pr B d u J A A A time A ≤ 10^(1+coefficientExponent)*
      (commonSize input V (CostAssembly.assembledWork k (ambient query)
        (resources query k occurrence qi hg first tail)) A time+1)^budgetExponent := by
  let s := Native.queryInputsAddressed query k hg first tail node
  let W := CostAssembly.assembledWork k (ambient query) (resources query k occurrence qi hg first tail)
  let Z := commonSize input V W A time
  have hz : 1 ≤ Z+1 := by omega
  have hinput : input ≤ Z := by dsimp [Z,commonSize]; omega
  have hv : V ≤ Z := by dsimp [Z,commonSize]; omega
  have hw : W ≤ Z := by dsimp [Z,commonSize]; omega
  have hA : A ≤ Z := by dsimp [Z,commonSize]; omega
  have ht : time ≤ Z := by dsimp [Z,commonSize]; omega
  have hz3 : Z ≤ (Z+1)^3 := by
    exact (Nat.le_succ Z).trans (by simpa using Nat.pow_le_pow_right hz (show 1 ≤ 3 by decide))
  have hcap : dictionaryCapacity (Finset.univ : Finset (Fin s.n)) u J ≤ (Z+1)^3 := by
    rw [MomentsNativeCostBridge.dictionaryCapacity_eq_count]
    simp only [Finset.card_univ,Fintype.card_fin]
    change u*J*SupportProgram.count (ambient query) J ≤ (Z+1)^3
    calc
      _ ≤ (Z+1)*(Z+1)*(Z+1) := by gcongr <;> omega
      _ = _ := by ring
  have hlocal := localBudget_le s input W B d u J A A A time A ((Z+1)^3)
    (Nat.one_le_pow _ _ hz) (hinput.trans hz3) (hw.trans hz3) ((hB.trans hv).trans hz3)
    ((hd.trans hv).trans hz3) ((hn.trans hv).trans hz3) ((hu.trans hv).trans hz3)
    ((hJ.trans hv).trans hz3) hJp hcap (hA.trans hz3) (hA.trans hz3) (hA.trans hz3)
    (ht.trans hz3) (hA.trans hz3) (hS.trans (hw.trans hz3))
  have hhead := query_head_bound query k occurrence qi hg first tail node pr ha input hb
  have hhc : headCap input W ≤ 10^120*(Z+1)^50 := by
    unfold headCap
    have hi : input+2 ≤ Z+1 := by dsimp [Z,commonSize]; omega
    calc
      _ ≤ 10^120*(Z+1)^48*(Z+1)^2 := by gcongr
      _ = _ := by rw [Nat.mul_assoc,←pow_add]
  have hh : pr.head.steps ≤ 10^2090*(Z+1)^budgetExponent := by
    apply hhead.trans
    calc
      _ ≤ 10^50*(10^120*(Z+1)^50)^17 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hhc _)
      _ = _ := by
        simp only [mul_pow,←pow_mul]
        rw [←Nat.mul_assoc,←pow_add]
        simp only [budgetExponent]
  have hl : localBudget s input W B d u J A A A time A ≤
      4100000*(Z+1)^budgetExponent := by
    apply hlocal.trans
    rw [←pow_mul]
    exact Nat.mul_le_mul_left _
      (pow_le_pow_right' (by omega : 1 ≤ Z+1)
        (by simp only [budgetExponent]; omega : 3*10 ≤ budgetExponent))
  have hfull := fullBudget_le_head_add pr ha input W B d u J A A A time A (fun i _=>hb i) h243
    (NodeEnvelope.query_inventory_bound query k occurrence qi hg first tail node pr ha)
  have hpow : (10:ℕ)^2090 ≤ 10^coefficientExponent :=
    pow_le_pow_right' (by decide : 1 ≤ (10:ℕ))
      (by simp only [coefficientExponent]; omega)
  have hsmall : 4100000 ≤ (10:ℕ)^coefficientExponent := by
    apply (show 4100000 ≤ (10:ℕ)^7 by norm_num).trans
    exact pow_le_pow_right' (by decide : 1 ≤ (10:ℕ))
      (by simp only [coefficientExponent]; omega)
  have hc : 10^2090+4100000 ≤ (10:ℕ)^(1+coefficientExponent) := by
    calc
      _ ≤ 10^coefficientExponent+10^coefficientExponent := Nat.add_le_add hpow hsmall
      _ ≤ 10*10^coefficientExponent := by
        rw [show (10:ℕ)=5+5 by norm_num, add_mul]
        gcongr <;> norm_num
      _ = 10^(1+coefficientExponent) := (pow_add 10 1 coefficientExponent).symm
  change _ ≤ 10^(1+coefficientExponent)*(Z+1)^budgetExponent
  calc
    _ ≤ pr.head.steps+localBudget s input W B d u J A A A time A := hfull
    _ ≤ 10^2090*(Z+1)^budgetExponent+4100000*(Z+1)^budgetExponent :=
      Nat.add_le_add hh hl
    _ = (10^2090+4100000)*(Z+1)^budgetExponent := (Nat.add_mul _ _ _).symm
    _ ≤ _ := Nat.mul_le_mul_right _ hc

end SubexponentialSAT.SqrtLog.NodeTime

end

end OAI.Algorithms
