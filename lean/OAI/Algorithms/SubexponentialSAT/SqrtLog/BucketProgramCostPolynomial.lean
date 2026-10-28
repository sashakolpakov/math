import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramSignedCost

namespace OAI.Algorithms

/-! One absolute polynomial bound suitable for the final uniform runtime
assembly. The exponential factor is explicitly squared: it is not hidden
inside the polynomial in dimensions and coefficient bit lengths. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram.Cost

/-- The exact cost expression after bounding each ordinary size parameter
by s; N remains the separate number of Boolean assignments. -/
def uniformTotal (N s : ℕ) : ℕ :=
  let width := 1+s*(s+1+s)
  let row := (s+1)*(200*(width+2)^2+34)+9*width+22
  let sigrow := 9*(s*(2*s+1))+7+(7*s+5)+2+(row+1)+8*(width+1)+8
  let key := s*(2*(width+1)+1)
  let matrix := s*(2*(s*(2*s+1))+1)
  let sig := s*(sigrow+2)+1
  let step := 1+(9*s+7)+(7*matrix+5)+(sig+2)+100*(s+1)*(s+1)+
    (7*key+5)+(8*key+8)+2+(8*s+8)+(8*key+8)+(2*s+3)
  let raw := N*(2*key+2*s+2)
  let grouping := 9+N*(6*key+100*(raw+1)*(key+1)+7)+
    3*(1+(2*(2*key+1+raw)+2)*N)
  800*(s+1)*(N+1)*(s+2)+9+48+(N*(step+2)+1)+2+
    120*(N*(2*key+2)+2)^2+grouping+(2*raw+8)+1

theorem total_le_uniform (W : List Bool) (h D B n s : ℕ)
    (hh : h ≤ s) (hD : D ≤ s) (hB : B ≤ s) (hn : n ≤ s) (hw : W.length ≤ s) :
    total W h D B n ≤ uniformTotal (2^h) s := by
  unfold total enumerationCost uniformTotal Label.stepBound Label.matrixBound
    Label.signatureBound signatureRowBound rowCostBound Label.keyBound widthBound
    groupBound recordsBound
  dsimp
  gcongr

theorem uniformTotal_eq (N s : ℕ) :
    uniformTotal N s =
      10880*N^2*s^6+10880*N^2*s^5+30720*N^2*s^4+19488*N^2*s^3+
      20744*N^2*s^2+7072*N^2*s+692*N^2+800*N*s^6+1600*N*s^5+
      3400*N*s^4+8300*N*s^3+6191*N*s^2+10061*N*s+2835*N+
      800*s^2+2400*s+2161 := by
  unfold uniformTotal
  ring

theorem uniformTotal_le (N s : ℕ) (hN : 1 ≤ N) (hs : 1 ≤ s) :
    uniformTotal N s ≤ 139024*N^2*s^6 := by
  have hm (i j : ℕ) (hi : i ≤ 2) (hj : j ≤ 6) : N^i*s^j ≤ N^2*s^6 :=
    Nat.mul_le_mul (pow_le_pow_right₀ hN hi) (pow_le_pow_right₀ hs hj)
  have h25 := hm 2 5 (by decide) (by decide)
  have h24 := hm 2 4 (by decide) (by decide)
  have h23 := hm 2 3 (by decide) (by decide)
  have h22 := hm 2 2 (by decide) (by decide)
  have h21 := hm 2 1 (by decide) (by decide)
  have h20 := hm 2 0 (by decide) (by decide)
  have h16 := hm 1 6 (by decide) (by decide)
  have h15 := hm 1 5 (by decide) (by decide)
  have h14 := hm 1 4 (by decide) (by decide)
  have h13 := hm 1 3 (by decide) (by decide)
  have h12 := hm 1 2 (by decide) (by decide)
  have h11 := hm 1 1 (by decide) (by decide)
  have h10 := hm 1 0 (by decide) (by decide)
  have h02 := hm 0 2 (by decide) (by decide)
  have h01 := hm 0 1 (by decide) (by decide)
  have h00 := hm 0 0 (by decide) (by decide)
  rw [uniformTotal_eq]
  nlinarith only [h25,h24,h23,h22,h21,h20,h16,h15,h14,h13,h12,h11,h10,h02,h01,h00]

/-- D is the actual serialized number of rows, not a rank surrogate. -/
theorem total_coarse (W : List Bool) (h D B n : ℕ) :
    total W h D B n ≤ 139024*(2^h+1)^2*(h+D+B+n+W.length+2)^6 := by
  let s := h+D+B+n+W.length+2
  have hs : 1 ≤ s := by dsimp [s]; omega
  have ht := total_le_uniform W h D B n s (by dsimp [s]; omega)
    (by dsimp [s]; omega) (by dsimp [s]; omega) (by dsimp [s]; omega)
    (by dsimp [s]; omega)
  have hp : 1 ≤ 2^h := Nat.one_le_pow h 2 (by decide)
  apply ht.trans ((uniformTotal_le (2^h) s hp hs).trans ?_)
  dsimp [s]
  gcongr ; omega

/-- Fixed degree six in ordinary input sizes, and exactly a quadratic
Boolean-enumeration factor. This includes actual signed preprocessing. -/
theorem signedTotal_coarse (W : List Bool) (h D L n : ℕ) :
    signedTotal W h D L n ≤ 101358497*(2^h+1)^2*(h+D+L+n+W.length+2)^6 := by
  let s := h+D+L+n+W.length+2
  let N := 2^h+1
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hN : 1 ≤ N := Nat.succ_le_succ (Nat.zero_le (2^h))
  have hb : h+D+(3*L+1)+n+W.length+2 ≤ 3*s := by dsimp [s]; omega
  have ht := total_coarse W h D (3*L+1) n
  have ht' : total W h D (3*L+1) n ≤ 139024*N^2*(3*s)^6 :=
    ht.trans (Nat.mul_le_mul_left (139024*N^2) (Nat.pow_le_pow_left hb 6))
  have hD : D+1 ≤ s := by dsimp [s]; omega
  have hh : h+1 ≤ s := by dsimp [s]; omega
  have hL : L+1 ≤ s := by dsimp [s]; omega
  have hpre : 10000*(D+1)*(h+1)*(L+1)^2 ≤ 10000*s^4 := by
    calc
      _ ≤ 10000*s*s*s^2 := Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul_left 10000 hD) hh) (Nat.pow_le_pow_left hL 2)
      _ = _ := by ring
  have h46 : s^4 ≤ s^6 := pow_le_pow_right₀ hs (by decide)
  have hn2 : 1 ≤ N^2 := one_le_pow₀ hN
  have hscale : s^6 ≤ N^2*s^6 := by simpa using Nat.mul_le_mul_right (s^6) hn2
  have hpre' : 10000*(D+1)*(h+1)*(L+1)^2 ≤ 10000*(N^2*s^6) :=
    hpre.trans (Nat.mul_le_mul_left _ (h46.trans hscale))
  have hone : 1 ≤ N^2*s^6 :=
    (show 1 ≤ s^6 from Nat.one_le_pow 6 s hs).trans hscale
  change 10000*(D+1)*(h+1)*(L+1)^2+total W h D (3*L+1) n+1 ≤ 101358497*N^2*s^6
  calc
    _ ≤ 10000*(N^2*s^6)+139024*N^2*(3*s)^6+(N^2*s^6) := by omega
    _ = _ := by
      have algebra (a b : ℕ) :
          10000*(a^2*b^6)+139024*a^2*(3*b)^6+(a^2*b^6)=101358497*a^2*b^6 := by ring
      exact algebra N s

end SubexponentialSAT.SqrtLog.BucketProgram.Cost

end OAI.Algorithms
