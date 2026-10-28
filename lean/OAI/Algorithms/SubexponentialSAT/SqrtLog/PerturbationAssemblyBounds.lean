import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyShift
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram

namespace OAI.Algorithms

/-! Explicit polynomial work and storage bounds for native shifted rows. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT

theorem shiftBudget_polynomial (N J W Km Ka : ℕ) :
    shiftBudget N J W Km Ka ≤
      1000*(N+1)*(J+1)*(W+1)+(N+1)*(Km+Ka) := by
  have hp := PerturbationProgram.Padding.budget_polynomial N J W
  unfold shiftBudget HornerProgram.budget
  ring_nf at hp ⊢
  omega

def rowWorkPolynomial (N J n d B : ℕ) : ℕ :=
  15*(N*(d*B))+30*n+43+1000*(N+1)*(J+1)*(d*B+1)+
    (N+1)*(100000*(J+1)^3*(d+1)^3*(B+1)^2+
      DensePolynomialProgram.AddService.budget d B J J)+
    150*(J+1)*(J+n+d*B+1)

theorem shifted_row_work_bound (N J n d B : ℕ) :
    15*(N*(d*B))+30*n+43+
      shiftBudget N J (d*B) (DensePolynomialProgram.nativeMulBudget J d B)
        (DensePolynomialProgram.AddService.budget d B J J)+
      PerturbationEmitProgram.budget J n (d*B) ≤ rowWorkPolynomial N J n d B := by
  have hs := shiftBudget_polynomial N J (d*B) (DensePolynomialProgram.nativeMulBudget J d B)
    (DensePolynomialProgram.AddService.budget d B J J)
  have hm := DensePolynomialProgram.nativeMulBudget_polynomial J d B
  have he := PerturbationEmitProgram.budget_polynomial J n (d*B)
  have hm' := Nat.mul_le_mul_left (N+1) (Nat.add_le_add_right hm
    (DensePolynomialProgram.AddService.budget d B J J))
  unfold rowWorkPolynomial
  omega

theorem emitted_length_bound (mask : List Bool) (J W : ℕ) (cs : List (List Bool))
    (hc : ∀ c∈cs,c.length=W) (j : ℕ) (hj : j+cs.length ≤ J+1) (acc : List Bool) :
    (PerturbationEmitProgram.emitted mask j cs acc).length ≤
      acc.length+cs.length*(2*(mask.length+J+W+4)) := by
  induction cs generalizing j acc with
  | nil => simp [PerturbationEmitProgram.emitted]
  | cons c cs ih =>
      have htail : ∀ x∈cs,x.length=W := by intro x hx; exact hc x (by simp [hx])
      have hj' : j+1+cs.length ≤ J+1 := by simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hj
      have hh := ih htail (j+1) hj' (PerturbationEmitProgram.record mask j c++acc)
      have hw := hc c (by simp)
      have hrecord : (PerturbationEmitProgram.record mask j c).length ≤ 2*(mask.length+J+W+4) := by
        simp only [PerturbationEmitProgram.record,PerturbationEmitProgram.keyBits,
          PerturbationProgram.Key.bits,List.length_append,List.length_cons,
          List.length_replicate,Encoding.length_frame,hw]
        simp only [List.length_cons] at hj
        omega
      simp only [PerturbationEmitProgram.emitted,List.length_cons]
      simp only [List.length_append] at hh
      nlinarith

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
