import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupBoundSpec

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Setup

open StructuredCalls SubexpSetupStorage

/-- An unconditional envelope for actual bit-program traces. -/
abbrev PolynomialEnvelope {r s : ℕ} (cmd : Cmd r s) : Prop :=
  ∃ C q : ℕ, 1 ≤ C ∧ 1 ≤ q ∧
    ∀ B a t b, WordBound B a → Eval cmd t a b →
      t ≤ C*(B+1)^q ∧ WordBound (C*(B+1)^q) b

theorem PolynomialEnvelope.seq {r s : ℕ} {first second : Cmd r s}
    (hfirst : PolynomialEnvelope first) (hsecond : PolynomialEnvelope second) :
    PolynomialEnvelope (.seq first second) := by
  obtain ⟨C1,q1,hC1,hq1,hfirst⟩ := hfirst
  obtain ⟨C2,q2,hC2,hq2,hsecond⟩ := hsecond
  let K := C2*(C1+1)^q2
  refine ⟨C1+K,q1*q2,by omega,by nlinarith,?_⟩
  intro B a t b ha he
  cases he with
  | @seq _ _ n1 n2 a mid b e1 e2 =>
    obtain ⟨ht1,hm⟩ := hfirst B a n1 mid ha e1
    obtain ⟨ht2,hb⟩ := hsecond (C1*(B+1)^q1) mid n2 b hm e2
    have hpow : 1 ≤ (B+1)^q1 := Nat.one_le_pow _ _ (by omega)
    have hin : C1*(B+1)^q1+1 ≤ (C1+1)*(B+1)^q1 := by nlinarith
    have htotal : C2*(C1*(B+1)^q1+1)^q2 ≤ K*(B+1)^(q1*q2) := by
      calc
        _ ≤ C2*((C1+1)*(B+1)^q1)^q2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hin q2)
        _ = _ := by simp only [mul_pow,← pow_mul,K]; ring
    have hq : q1 ≤ q1*q2 := by nlinarith
    have hfirstBound : C1*(B+1)^q1 ≤ C1*(B+1)^(q1*q2) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hq)
    have hbBound : K*(B+1)^(q1*q2) ≤ (C1+K)*(B+1)^(q1*q2) :=
      Nat.mul_le_mul_right _ (by omega)
    refine ⟨?_,fun i => (hb i).trans (htotal.trans hbBound)⟩
    calc
      n1+n2 ≤ C1*(B+1)^(q1*q2)+K*(B+1)^(q1*q2) :=
        Nat.add_le_add (ht1.trans hfirstBound) (ht2.trans htotal)
      _ = _ := by ring

end SubexponentialSAT.SqrtLog.Setup

end OAI.Algorithms
