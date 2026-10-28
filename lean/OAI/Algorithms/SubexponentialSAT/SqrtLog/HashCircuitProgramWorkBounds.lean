import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramMeaning

namespace OAI.Algorithms

/-! Serialization and invariant-based bounds for the actual dynamic fold.
These lemmas expose the finite-width input costs without hiding a callback or
assuming that its accumulator has a fixed byte length. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram

namespace DynamicFold
variable {R A : Type*}

theorem work_le_invariant (encode : R → List Bool) (step : R → A → A)
    (cost : R → A → ℕ) (Inv : A → Prop) (xs : List R) (a : A) (P C : ℕ)
    (ha : Inv a) (hp : ∀ x ∈ xs, (encode x).length ≤ P)
    (hs : ∀ x ∈ xs, ∀ b, Inv b → Inv (step x b))
    (hc : ∀ x ∈ xs, ∀ b, Inv b → cost x b ≤ C) :
    work encode step cost xs a ≤ xs.length*(6*P+C+7) := by
  induction xs generalizing a with
  | nil => simp [work]
  | cons x xs ih =>
    have hpx := hp x (by simp)
    have hcx := hc x (by simp) a ha
    have hnext := hs x (by simp) a ha
    have hrec := ih (step x a) hnext
      (fun y hy => hp y (by simp [hy]))
      (fun y hy => hs y (by simp [hy]))
      (fun y hy => hc y (by simp [hy]))
    simp only [work,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega
end DynamicFold

namespace Native.Row

theorem literalBits_length {n : ℕ} (l : SAT.Literal (Fin n)) :
    (Clause.literalBits l).length ≤ 2*n+1 := by
  have h := Encoding.literalCode_lt l
  simp only [Clause.literalBits,Encoding.length_encodeNat]
  omega

theorem literalList_length {n B d : ℕ} (w : WeightedClause n B d) :
    (literalList w).length ≤ 1+(4*n+4)*w.literals.length := by
  have h := Encoding.length_encodeList_upper id (w.literals.map Clause.literalBits)
    (2*n+1) (by
      intro a ha
      obtain ⟨l,hl,rfl⟩ := List.mem_map.mp ha
      exact literalBits_length l)
  simpa only [literalList,List.length_map,show 2*(2*n+1)+2=4*n+4 by omega] using h

theorem payload_length {n B d : ℕ} (w : WeightedClause n B d) (k : ℕ)
    (hk : w.literals.length ≤ k) :
    (payload w).length ≤ 2*(d*B)+2+(4*n+4)*k := by
  have h := literalList_length w
  have hm := Nat.mul_le_mul_left (4*n+4) hk
  simp only [payload,List.length_append,Encoding.length_frame,RingProgram.flat_length]
  omega

theorem input_length {n B d : ℕ} (ws : List (WeightedClause n B d)) (k : ℕ)
    (hk : ∀ w ∈ ws, w.literals.length ≤ k) :
    (Encoding.encodeList id (ws.map payload)).length ≤
      1+(2*(2*(d*B)+2+(4*n+4)*k)+2)*ws.length := by
  have h := Encoding.length_encodeList_upper id (ws.map payload)
    (2*(d*B)+2+(4*n+4)*k) (by
      intro a ha
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
      exact payload_length w k (hk w hw))
  simpa only [List.length_map] using h

end Native.Row
end SubexponentialSAT.SqrtLog.HashCircuitProgram

end OAI.Algorithms
