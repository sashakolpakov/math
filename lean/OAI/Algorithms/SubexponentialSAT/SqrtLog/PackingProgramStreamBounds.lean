import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramStreamLoop

namespace OAI.Algorithms

/-! Uniform polynomial bounds for every bit moved by the weighted stream
combiner. The bounds include unary value lengths, not only input bit widths. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Streams

 theorem scaleBudget_bound (bits : List Bool) (count B W C : ℕ)
    (hb : bits.length ≤ B) (hw : SubexponentialSAT.CounterPrograms.value bits ≤ W) (hc : count ≤ C) :
    scaleBudget bits count ≤ 64*(W+1)*(B+C+1) := by
  have h1 : SubexponentialSAT.CounterPrograms.value bits*(7*count+5) ≤ W*(7*C+5) :=
    Nat.mul_le_mul hw (by omega)
  have h2 : (SubexponentialSAT.CounterPrograms.value bits+1)*(16*bits.length+16) ≤
      (W+1)*(16*B+16) := Nat.mul_le_mul (by omega) (by omega)
  unfold scaleBudget
  nlinarith

 theorem value_bound (wi wh : List Bool) (p : ℕ × ℕ) (W C : ℕ)
    (hi : SubexponentialSAT.CounterPrograms.value wi ≤ W) (hh : SubexponentialSAT.CounterPrograms.value wh ≤ W)
    (hc : p.1 ≤ C) (hd : p.2 ≤ C) : value wi wh p ≤ 2*W*C := by
  have h1 := Nat.mul_le_mul hi hc
  have h2 := Nat.mul_le_mul hh hd
  unfold value
  nlinarith

 theorem pairBudget_bound (wi wh : List Bool) (p : ℕ × ℕ) (B W C : ℕ)
    (hbi : wi.length ≤ B) (hbh : wh.length ≤ B)
    (hi : SubexponentialSAT.CounterPrograms.value wi ≤ W) (hh : SubexponentialSAT.CounterPrograms.value wh ≤ W)
    (hc : p.1 ≤ C) (hd : p.2 ≤ C) :
    pairBudget wi wh p ≤ 200*(W+1)*(B+C+1) := by
  have h1 := scaleBudget_bound wi p.1 B W C hbi hi hc
  have h2 := scaleBudget_bound wh p.2 B W C hbh hh hd
  have h3 := value_bound wi wh p W C hi hh hc hd
  unfold pairBudget
  nlinarith

 theorem resultBody_length_bound (wi wh : List Bool) (ps : List (ℕ × ℕ)) (W C : ℕ)
    (hi : SubexponentialSAT.CounterPrograms.value wi ≤ W) (hh : SubexponentialSAT.CounterPrograms.value wh ≤ W)
    (hc : ∀ p ∈ ps, p.1 ≤ C ∧ p.2 ≤ C) :
    (resultBody wi wh ps).length ≤ ps.length*(4*W*C+2) := by
  induction ps with
  | nil => simp [resultBody]
  | cons p ps ih =>
    have hp := hc p (by simp)
    have hv := value_bound wi wh p W C hi hh hp.1 hp.2
    have ht := ih (fun a ha => hc a (by simp [ha]))
    simp only [resultBody,List.length_append,List.length_cons,SubexponentialSAT.Encoding.length_frame,
      List.length_replicate]
    nlinarith

 theorem pairsBytes_length_bound (ps : List (ℕ × ℕ)) (C : ℕ)
    (hc : ∀ p ∈ ps, p.1 ≤ C ∧ p.2 ≤ C) :
    (pairsBytes ps).length ≤ ps.length*(4*C+3)+1 := by
  induction ps with
  | nil => simp [pairsBytes]
  | cons p ps ih =>
    have hp := hc p (by simp)
    have ht := ih (fun a ha => hc a (by simp [ha]))
    simp only [pairsBytes,payload,List.length_cons,List.length_append,
      SubexponentialSAT.Encoding.length_frame,List.length_replicate]
    nlinarith

 theorem loopBudget_bound (wi wh : List Bool) (ps : List (ℕ × ℕ)) (B W C : ℕ)
    (hbi : wi.length ≤ B) (hbh : wh.length ≤ B)
    (hi : SubexponentialSAT.CounterPrograms.value wi ≤ W) (hh : SubexponentialSAT.CounterPrograms.value wh ≤ W)
    (hc : ∀ p ∈ ps, p.1 ≤ C ∧ p.2 ≤ C) :
    loopBudget wi wh ps ≤ ps.length*(200*(W+1)*(B+C+1)+2)+1 := by
  induction ps with
  | nil => simp [loopBudget]
  | cons p ps ih =>
    have hp := hc p (by simp)
    have h1 := pairBudget_bound wi wh p B W C hbi hbh hi hh hp.1 hp.2
    have h2 := ih (fun a ha => hc a (by simp [ha]))
    simp only [loopBudget,List.length_cons]
    nlinarith

 theorem streamBudget_bound (wi wh : List Bool) (ps : List (ℕ × ℕ)) (B W C : ℕ)
    (hbi : wi.length ≤ B) (hbh : wh.length ≤ B)
    (hi : SubexponentialSAT.CounterPrograms.value wi ≤ W) (hh : SubexponentialSAT.CounterPrograms.value wh ≤ W)
    (hc : ∀ p ∈ ps, p.1 ≤ C ∧ p.2 ≤ C) :
    streamBudget wi wh ps+1 ≤ 300*(ps.length+1)*(W+1)*(B+C+1) := by
  have h1 := loopBudget_bound wi wh ps B W C hbi hbh hi hh hc
  have h2 := resultBody_length_bound wi wh ps W C hi hh hc
  unfold streamBudget
  nlinarith [Nat.zero_le (ps.length*W*B), Nat.zero_le (ps.length*W*C),
    Nat.zero_le (ps.length*B), Nat.zero_le (ps.length*C), Nat.zero_le (W*B), Nat.zero_le (W*C)]
end SubexponentialSAT.SqrtLog.PackingProgram.Streams

end OAI.Algorithms
