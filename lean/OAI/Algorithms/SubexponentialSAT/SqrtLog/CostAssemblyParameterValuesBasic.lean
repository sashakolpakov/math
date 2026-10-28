import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramBanked
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyPolynomial

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues

open LeafParametersProgram LeafParametersProgram.Bank LeafParametersProgram.Circuit


/-- A value-only bound: input padding has no effect on this quantity. -/
def grow (B : ℕ) : ℕ := (B+129)^2

def iter : ℕ → ℕ → ℕ
  | 0,B => B
  | n+1,B => iter n (grow B)

def Constants : Instr → Prop
  | .load _ bs => BinaryArithmetic.toNat bs ≤ 128
  | .addConst _ k => k ≤ 128
  | _ => True

def PowerBound (B : ℕ) (m : Model) : Instr → Prop
  | .pow a b _ _ _ => m.val a^m.val b ≤ B
  | _ => True

def PowerBounds (B : ℕ) : List Instr → Model → Prop
  | [],_ => True
  | i::is,m => PowerBound B m i ∧ PowerBounds B is (next m i)

theorem grow_ge (B : ℕ) : B ≤ grow B := by dsimp [grow]; nlinarith

theorem value_le {B K : ℕ} (hK : K ≤ B) (m : Model) (hm : ∀ j, m.val j ≤ B)
    (i : Instr) (hc : Constants i) (hp : PowerBound K m i) :
    value m.val i ≤ grow B := by
  have hg := grow_ge B
  have hb : 128 ≤ grow B := by dsimp [grow]; nlinarith
  cases i with
  | clear a => exact Nat.zero_le _
  | load a bs => exact hc.trans hb
  | copy a o h => exact (hm a).trans hg
  | add a b o ha hb => dsimp [value,grow]; have := hm a; have := hm b; nlinarith
  | mul a b o ha hb =>
      dsimp [value]
      exact (Nat.mul_le_mul (hm a) (hm b)).trans (by dsimp [grow]; nlinarith)
  | pow a b o ha hb => exact hp.trans (hK.trans hg)
  | quot a b o ha hb => exact (Nat.div_le_self _ _).trans ((hm a).trans hg)
  | sqrt a o h => exact (Nat.sqrt_le_self _).trans ((hm a).trans hg)
  | logSucc a =>
      have := Nat.log2_le_self (m.val a)
      have := hm a
      dsimp [value,grow]
      nlinarith
  | addConst a k => have := hm a; dsimp [Constants] at hc; dsimp [value,grow]; nlinarith
  | pred a => exact (Nat.sub_le _ _).trans ((hm a).trans hg)
  | maxTwo a => exact max_le (by dsimp [grow]; nlinarith) ((hm a).trans hg)

theorem result_le {B K : ℕ} (hK : K ≤ B) (is : List Instr) (m : Model)
    (hm : ∀ j, m.val j ≤ B) (hc : ∀ i ∈ is,Constants i) (hp : PowerBounds K is m) :
    ∀ j, (result is m).val j ≤ iter is.length B := by
  induction is generalizing B m with
  | nil => exact hm
  | cons i is ih =>
      apply ih (hK.trans (grow_ge B)) (next m i)
      · intro j
        by_cases hj : j=output i
        · subst j; simpa [next] using value_le hK m hm i (hc i (by simp)) hp.1
        · simpa [next,hj] using (hm j).trans (grow_ge B)
      · intro a ha; exact hc a (by simp [ha])
      · exact hp.2

theorem iter_ordinary (n : ℕ) {f : ℕ → ℕ} (hf : Polynomial.Ordinary f) :
    Polynomial.Ordinary (fun S => iter n (f S)) := by
  induction n generalizing f with
  | zero => exact hf
  | succ n ih =>
      exact ih (Polynomial.ordinary_pow (Polynomial.ordinary_add hf
        (Polynomial.ordinary_const 129)) 2)

end SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues

end OAI.Algorithms
