import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramSource

namespace OAI.Algorithms

/-! Every source-wrapper copy and cleanup is charged against actual word
lengths. The fixed finite allocation makes this overhead linear even without
assuming that intermediate destinations were empty. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Source
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

private theorem copy_bound {S : ℕ} (src dst : Fin S) (a : SubexpSetupStorage.Data S)
    (B : ℕ) (ha : WordBound B a) : WordBound (2*B) (copyState src dst a) := by
  intro i
  rw [copyState_stack]
  by_cases hi : i=dst
  · subst i
    simp only [Function.update_same,List.length_append]
    have hs:=ha src
    have hd:=ha dst
    omega
  · rw [Function.update_of_ne hi]
    exact (ha i).trans (by omega)

private theorem copyMany_bound {S : ℕ} (ps : List (Fin S × Fin S))
    (a : SubexpSetupStorage.Data S) (B : ℕ) (ha : WordBound B a) :
    WordBound (2^ps.length*B) (copyManyState ps a) := by
  induction ps generalizing a B with
  | nil => simpa [copyManyState] using ha
  | cons p ps ih =>
    have h := ih (copyState p.1 p.2 a) (2*B) (copy_bound _ _ _ _ ha)
    simpa only [copyManyState,List.length_cons,pow_succ,Nat.mul_assoc] using h

private theorem copyMany_cost_bound {S : ℕ} (ps : List (Fin S × Fin S))
    (a : SubexpSetupStorage.Data S) (B : ℕ) (ha : WordBound B a) :
    copyManyCost ps a ≤ ps.length*(7*(2^ps.length*B)+5) := by
  induction ps generalizing a B with
  | nil => simp [copyManyCost]
  | cons p ps ih =>
    have h := ih (copyState p.1 p.2 a) (2*B) (copy_bound _ _ _ _ ha)
    have hp := ha p.1
    have hpow : 1 ≤ 2^ps.length := Nat.one_le_pow _ _ (by decide)
    have hb : B ≤ 2^(ps.length+1)*B := by
      calc
        B = 1*B := by omega
        _ ≤ 2^(ps.length+1)*B := Nat.mul_le_mul_right _ (Nat.one_le_pow _ _ (by decide))
    calc
      copyManyCost (p::ps) a = (7*(a.stacks p.1).length+5)+
          copyManyCost ps (copyState p.1 p.2 a) := rfl
      _ ≤ (7*(2^ps.length*(2*B))+5)+ps.length*(7*(2^ps.length*(2*B))+5) := by
        apply Nat.add_le_add _ h
        simp only [pow_succ,Nat.mul_assoc] at hb
        omega
      _ = (p::ps).length*(7*(2^(p::ps).length*B)+5) := by
        simp only [List.length_cons,pow_succ]
        ring

/-- Coarse bound for a copy list of statically known size, including any
appending to its destinations. -/
theorem saved_bound (a : Data) (B : ℕ) (ha : WordBound B a) :
    WordBound (16*B) (SourceStaging.saved a) := by
  apply clearMany_wordBound
  simpa [SourceStaging.savePairs] using copyMany_bound SourceStaging.savePairs a B ha

theorem prepared_bound (a : Data) (B : ℕ) (ha : WordBound B a) :
    WordBound (67108864*B+1) (prepared a) := by
  have h := copyMany_bound SourceControls.pairs (SourceStaging.saved a) (16*B)
    (saved_bound a B ha)
  have h' : WordBound (67108864*B)
      (copyManyState SourceControls.pairs (SourceStaging.saved a)) := by
    have he : 2^SourceControls.pairs.length*(16*B)=67108864*B := by
      norm_num [SourceControls.pairs]
      ring
    rw [he] at h
    exact h
  intro i
  change ((SourceControls.deltaState _).stacks i).length ≤ _
  rw [SourceControls.delta_stacks]
  by_cases hi : i=365
  · subst i
    simpa only [Function.update_same,List.length_cons] using Nat.add_le_add_right (h' 365) 1
  · rw [Function.update_of_ne hi]
    exact (h' i).trans (by omega)

private theorem before_cost_bound (a : Data) (B : ℕ) (ha : WordBound B a) :
    SourceStaging.beforeCost a ≤ 576*B+32 := by
  have h0 := copyMany_cost_bound SourceStaging.savePairs a B ha
  have h1 := clearManyCost_le SourceStaging.cachePorts _ (16*B)
    (by simpa [SourceStaging.savePairs] using copyMany_bound SourceStaging.savePairs a B ha)
  norm_num [SourceStaging.savePairs,SourceStaging.cachePorts] at h0 h1
  dsimp only [SourceStaging.beforeCost,SourceStaging.savePairs,SourceStaging.cachePorts]
  omega

private theorem prepare_cost_bound (a : Data) (B : ℕ) (ha : WordBound B a) :
    SourceControls.prepareCost (SourceStaging.saved a) ≤ 10334765056*B+112 := by
  have h := copyMany_cost_bound SourceControls.pairs (SourceStaging.saved a) (16*B)
    (saved_bound a B ha)
  norm_num [SourceControls.pairs] at h
  dsimp only [SourceControls.prepareCost,SourceControls.pairs]
  omega

private theorem after_bound (a : Data) (B : ℕ) (ha : WordBound B a) :
    WordBound (16*B) (SourceStaging.finished a) := by
  apply clearMany_wordBound
  apply clearMany_wordBound
  simpa [SourceStaging.restorePairs] using copyMany_bound SourceStaging.restorePairs
    (clearManyState SourceStaging.cachePorts a) B
    (clearMany_wordBound _ _ B ha)

private theorem after_cost_bound (a : Data) (B : ℕ) (ha : WordBound B a) :
    SourceStaging.afterCost a ≤ 7144*B+659 := by
  have h0 := clearManyCost_le SourceStaging.cachePorts a B ha
  have hc := clearMany_wordBound SourceStaging.cachePorts a B ha
  have h1 := copyMany_cost_bound SourceStaging.restorePairs _ B hc
  have hh : WordBound (16*B) (copyManyState SourceStaging.restorePairs
      (clearManyState SourceStaging.cachePorts a)) := by
    simpa [SourceStaging.restorePairs] using copyMany_bound SourceStaging.restorePairs _ B hc
  have h2 := clearManyCost_le SourceStaging.backupPorts _ (16*B) hh
  have h3 := clearManyCost_le SourceStaging.lowClearPorts _ (16*B)
    (clearMany_wordBound SourceStaging.backupPorts _ (16*B) hh)
  have hl : SourceStaging.lowClearPorts.length ≤ 205 := by
    unfold SourceStaging.lowClearPorts
    simp only [List.length_map]
    exact (List.length_filter_le _ _).trans_eq (List.length_finRange)
  have h3' : clearManyCost SourceStaging.lowClearPorts (SourceStaging.restored a) ≤
      205*(2*(16*B)+3) := h3.trans (Nat.mul_le_mul_right _ hl)
  norm_num [SourceStaging.cachePorts,SourceStaging.restorePairs,SourceStaging.backupPorts] at h0 h1 h2
  dsimp only [SourceStaging.afterCost,SourceStaging.cachePorts,SourceStaging.restorePairs,SourceStaging.backupPorts]
  omega

/-- Full wrapper overhead, including source-private and arithmetic cleanup.
The core invocation is accounted for separately by its actual step count. -/
theorem cost_bound (a : Data) (b : State 16 340) (n A B : ℕ)
    (ha : WordBound A a) (hb : WordBound B b) :
    cost a b n ≤ n+1000000000000*(A+B+1) := by
  let C := 67108864*A+1+B
  have hp := prepared_bound a A ha
  have he : WordBound C (coreOutput a b) := by
    apply embedState_wordBound id workerPort (prepared a) b C workerPort_injective
    · intro i
      exact (hp i).trans (by dsimp [C]; omega)
    · intro i
      exact (hb i).trans (by dsimp [C]; omega)
  have h0 := before_cost_bound a A ha
  have h1 := prepare_cost_bound a A ha
  have h2 := after_cost_bound (coreOutput a b) C he
  have h3 := clearManyCost_le SourceControls.extraPorts _ (16*C)
    (after_bound (coreOutput a b) C he)
  have hl : SourceControls.extraPorts.length=88 := by simp [SourceControls.extraPorts]
  rw [hl] at h3
  unfold cost
  dsimp [C] at h2 h3
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.Source

end OAI.Algorithms
