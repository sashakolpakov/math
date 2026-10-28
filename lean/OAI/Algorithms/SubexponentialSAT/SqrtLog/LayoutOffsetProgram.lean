import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpBlockParameterProgram
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram

namespace OAI.Algorithms

/-! A fixed native producer of the signed-bucket offset 2*B*(8*Q)^(2*R).
All arithmetic acts on runtime binary words. This offset is unrelated to
the unary scalar-row width 1+2*A*R+Q. -/
namespace SubexponentialSAT.SqrtLog.LayoutOffsetProgram
open SubexponentialSAT BitProgram StructuredCalls BinaryArithmetic
open SubexpBlockParameterProgram

abbrev Data := State 8 22
abbrev Words := Fin 15 → List Bool
abbrev Regs := Fin 8 → Bool
abbrev bank := SubexpBlockParameterProgram.state

def two : List Bool := [false,true]
def eight : List Bool := [false,false,false,true]

@[simp] theorem two_value : BinaryArithmetic.toNat two=2 := by decide
@[simp] theorem eight_value : BinaryArithmetic.toNat eight=8 := by decide
@[simp] theorem two_length : two.length=2 := rfl
@[simp] theorem eight_length : eight.length=4 := rfl

def initial (B Q R : List Bool) : Words := SubexpBlockParameterProgram.inputWords B Q R

def loaded (B Q R : List Bool) : Words :=
  Function.update (Function.update (initial B Q R) 3 two) 4 eight

def filled (B Q R a e p b out : List Bool) : Words :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (loaded B Q R) 5 a) 6 e) 7 p) 8 b) 9 out

abbrev core : Cmd 8 22 :=
  .seq (loadCmd 3 two) (.seq (loadCmd 4 eight)
    (.seq (multiplyCmd 4 1 5 (by decide) (by decide))
      (.seq (multiplyCmd 3 2 6 (by decide) (by decide))
        (.seq (powerCmd 5 6 7 (by decide) (by decide))
          (.seq (multiplyCmd 3 0 8 (by decide) (by decide))
            (multiplyCmd 8 7 9 (by decide) (by decide)))))))

def sourceWidth (B Q R : List Bool) : ℕ := B.length+Q.length+R.length+10

def width (B Q R : List Bool) : ℕ := (2*BinaryArithmetic.toNat R+1)*(sourceWidth B Q R+1)

def outputLength (B Q R : List Bool) : ℕ := B.length+2*BinaryArithmetic.toNat R*(Q.length+5)+5

def coreBudget (B Q R : List Bool) : ℕ := 4000*(width B Q R)^2

def budget (B Q R : List Bool) : ℕ := 5000*(width B Q R)^2

theorem width_pos (B Q R : List Bool) : 1 ≤ width B Q R := by
  unfold width
  exact Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))

theorem sourceWidth_le_width (B Q R : List Bool) : sourceWidth B Q R+1 ≤ width B Q R := by
  unfold width
  exact Nat.le_mul_of_pos_left _ (by omega)

/-- This bound uses the actual base and exponent word lengths, including
any zero padding. The numerical exponent is an explicit parameter. -/
theorem power_cost_le (a e : List Bool) (L E : ℕ)
    (ha : a.length ≤ L) (he : e.length ≤ L) (hv : BinaryArithmetic.toNat e=E) :
    PowerPrograms.runtimeBound a e+9*e.length+8 ≤ 200*((E+1)*(L+1))^2 := by
  let H := (E+1)*(L+1)
  have hH : 1 ≤ H := Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
  have hL : L ≤ H := by
    have := Nat.le_mul_of_pos_left (L+1) (by omega : 0 < E+1)
    dsimp [H]
    omega
  have hEL : E*(L+1) ≤ H := Nat.mul_le_mul_right _ (Nat.le_succ E)
  have hLE : (E+1)*L ≤ H := Nat.mul_le_mul_left _ (Nat.le_succ L)
  have hsq : H ≤ H^2 := by nlinarith
  have hfirst : E*(50*(L+1)*(2+(E+1)*L)) ≤ 150*H^2 := by
    calc
      _ = 50*(E*(L+1))*(2+(E+1)*L) := by ring
      _ ≤ 50*H*(2+H) := by gcongr
      _ ≤ _ := by nlinarith
  have hsecond : (E+1)*(16*L+16)=16*H := by dsimp [H]; ring
  calc
    _ ≤ E*(50*(L+1)*(2+(E+1)*L))+(E+1)*(16*L+16)+3+9*L+8 := by
      unfold PowerPrograms.runtimeBound PowerPrograms.workBound PowerPrograms.callbackBound
      rw [hv]
      gcongr
    _ ≤ 200*H^2 := by rw [hsecond]; nlinarith

theorem arithmetic_cost_le (a b : List Bool) (H : ℕ)
    (ha : a.length ≤ H) (hb : b.length ≤ H) (hH : 1 ≤ H) :
    100*(a.length+b.length+1)^2 ≤ 900*H^2 := by
  calc
    _ ≤ 100*(3*H)^2 := by gcongr; omega
    _ = _ := by ring

end SubexponentialSAT.SqrtLog.LayoutOffsetProgram

end OAI.Algorithms
