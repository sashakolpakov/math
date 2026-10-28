import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramProductBounds

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

/-- Polynomial cost of one physical scaling-and-addition callback. N bounds
the total input records, W the encoded key length. -/
def weightedEnvelope (B d W N : ℕ) : ℕ :=
  25*N*(2*W+2*(d*B)+2)+11*(d*B)+9*d+
    N*(40000*(d+1)^3*(B+1)^2+35*(d*B)+7*d+22*W+57)+
    N*(220*(N+1)*(W+d*B+1)+MomentsProgram.Dictionary.codeBranchBudget B d+2)+50

theorem weightedBudget_le (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (weight : RingProgram.Code (Word (baseWidth p t)) d)
    (jet seed : List (Product.Entry n (baseWidth p t) d)) (W N : ℕ)
    (hj : Normalize.KeyBound Squarefree.encodeIndex W jet)
    (hs : Normalize.KeyBound Squarefree.encodeIndex W seed)
    (hN : jet.length+seed.length ≤ N) :
    weightedBudget p t M cache table weight jet seed ≤ weightedEnvelope (baseWidth p t) d W N := by
  let scaled := Squarefree.ScaleProgram.scaled p t M cache table weight jet
  have hscaled : Normalize.KeyBound Squarefree.encodeIndex W scaled := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact hj b hb
  have hlength : scaled.length=jet.length := by simp [scaled,Squarefree.ScaleProgram.scaled]
  have hb := Product.bytes_length_le jet W hj
  have hscale := Squarefree.ScaleProgram.budget_le Squarefree.encodeIndex jet W hj
  have hnorm := Normalize.work_le p t M cache Squarefree.encodeIndex W N scaled seed hscaled hs (by omega)
  have hsize : jet.length ≤ N := by omega
  have h1 := Nat.mul_le_mul_right (2*W+2*(d*baseWidth p t)+2) hsize
  have h2 := Nat.mul_le_mul_right
    (40000*(d+1)^3*(baseWidth p t+1)^2+35*(d*baseWidth p t)+7*d+22*W+57) hsize
  have h3 := Nat.mul_le_mul_right
    (220*(N+1)*(W+d*baseWidth p t+1)+MomentsProgram.Dictionary.codeBranchBudget (baseWidth p t) d+2) hsize
  rw [hlength] at hnorm
  simp only [weightedBudget,weightedEnvelope,RingProgram.flat_length]
  dsimp [scaled] at hnorm
  nlinarith

/-- Bounded-state loop accounting. The predicate can be canonical sparse
validity, avoiding an unjustified bound on arbitrary intermediate tapes. -/
theorem scanWork_bound_on {A W : Type*} (cost : A → W → ℕ) (step : A → W → A)
    (P : A → Prop) (xs : List W) (bound : ℕ)
    (hstep : ∀ a, P a → ∀ x ∈ xs, P (step a x))
    (hcost : ∀ a, P a → ∀ x ∈ xs, cost a x ≤ bound)
    (a : A) (ha : P a) :
    scanWork cost step a xs ≤ xs.length*(bound+2)+1 := by
  induction xs generalizing a with
  | nil => simp [scanWork]
  | cons x xs ih =>
      have hc := hcost a ha x (by simp)
      have hn := hstep a ha x (by simp)
      have ht := ih
        (fun a ha y hy => hstep a ha y (by simp [hy]))
        (fun a ha y hy => hcost a ha y (by simp [hy])) (step a x) hn
      simp only [scanWork,List.length_cons]
      nlinarith

end SubexponentialSAT.SqrtLog.MomentsAssembly

end OAI.Algorithms
