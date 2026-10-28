import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorBounds

namespace OAI.Algorithms

/-! A fixed-degree envelope for source-backed incidence preparation.
The source cost in this bound is the explicit checked native polynomial,
not an oracle or an assumed cost of a callback. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorBounds
open SubexponentialSAT.SubexpLiftRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open PerturbationAssembly

def lowEnvelope (n N J d w E : ℕ) : ℕ :=
  let W := d*w
  1000000*(n+1)*(N+1)*(d+1)^3*(w+1)^2+(33*n+20*W+83)+
    (9*E+14*J+9*(J*W)+7*W+440*(J+1)*(W+1)+47)+
    (7*(n*(2*(N*W)+2)+1)+9*n+n*(rowWorkPolynomial N J n d w+2)+20)+
    (2*(2*(J*W)+2*J+W)+6*E+33)+(2*W+3)

def literalEnvelope (n N J d w E H K : ℕ) : ℕ :=
  let W := d*w
  7*n+(10*n+9*H+18+(10*n+42*n+29*W+109)+K+
    lowEnvelope n N J d w E+1)+22*(n+1)+19*incidenceBitsBound n J W+
    2*(n*(2*(N*W)+2)+1)+54

def incidenceEnvelope (n N J d w A B K : ℕ) : ℕ :=
  40000000*(A+1)+7*n+n*(literalEnvelope n N J d w (3*B) B K+2)+
    6*n*literalRecordBound n (incidenceBitsBound n J (d*w))+15+
    incidenceExportBound B (n*literalRecordBound n (incidenceBitsBound n J (d*w)))

theorem incidencePolynomial_eq {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (n J S A B : ℕ) :
    incidencePolynomial p n J S A B =
      incidenceEnvelope n (p.R+1) J d (baseWidth 3 p.t) A B
        (Source.nativeSourceWorkPolynomial p S) := by
  dsimp only [incidencePolynomial,incidenceEnvelope,relFactorWorkPolynomial,
    literalWorkPolynomial,literalEnvelope,lowWorkPolynomial,lowEnvelope]
  ring

theorem incidenceEnvelope_mono (n N J d w A B K Z : ℕ)
    (hn : n ≤ Z) (hN : N ≤ Z) (hJ : J ≤ Z) (hd : d ≤ Z) (hw : w ≤ Z)
    (hA : A ≤ Z) (hB : B ≤ Z) (hK : K ≤ Z) :
    incidenceEnvelope n N J d w A B K ≤ incidenceEnvelope Z Z Z Z Z Z Z Z := by
  dsimp only [incidenceEnvelope,literalEnvelope,lowEnvelope,rowWorkPolynomial,
    DensePolynomialProgram.AddService.budget,incidenceBitsBound,literalRecordBound,incidenceExportBound]
  gcongr

theorem incidenceEnvelope_diagonal (Z : ℕ) :
    incidenceEnvelope Z Z Z Z Z Z Z Z =
      100000*Z^11+900000*Z^10+3600000*Z^9+9400000*Z^8+19614000*Z^7+
      33643026*Z^6+43456739*Z^5+38648963*Z^4+21951647*Z^3+7117152*Z^2+
      41024290*Z+40001040 := by
  dsimp only [incidenceEnvelope,literalEnvelope,lowEnvelope,rowWorkPolynomial,
    DensePolynomialProgram.AddService.budget,incidenceBitsBound,literalRecordBound,incidenceExportBound]
  ring

theorem incidenceEnvelope_le (n N J d w A B K Z : ℕ) (hZ : 1 ≤ Z)
    (hn : n ≤ Z) (hN : N ≤ Z) (hJ : J ≤ Z) (hd : d ≤ Z) (hw : w ≤ Z)
    (hA : A ≤ Z) (hB : B ≤ Z) (hK : K ≤ Z) :
    incidenceEnvelope n N J d w A B K ≤ 260000000*Z^11 := by
  apply (incidenceEnvelope_mono n N J d w A B K Z hn hN hJ hd hw hA hB hK).trans
  rw [incidenceEnvelope_diagonal]
  have hp (k : ℕ) (hk : k ≤ 11) : Z^k ≤ Z^11 := Nat.pow_le_pow_right hZ hk
  have h0 : 1 ≤ Z^11 := by simpa using hp 0 (by decide)
  have h1 : Z ≤ Z^11 := by simpa using hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 (by decide)
  have h6 := hp 6 (by decide)
  have h7 := hp 7 (by decide)
  have h8 := hp 8 (by decide)
  have h9 := hp 9 (by decide)
  have h10 := hp 10 (by decide)
  omega

/-- Every term is an actual dimension, live tape cap, or the concrete source
polynomial. In particular this is not asserted to be polynomial in input bits. -/
noncomputable def sourceAwareSize {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (n J S A B Z : ℕ) : ℕ :=
  n+(p.R+1)+J+d+baseWidth 3 p.t+A+B+Source.nativeSourceWorkPolynomial p S+Z+1

theorem branchBound_power {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (n J S A B Z : ℕ) :
    branchBound p n J S A B Z ≤ 275000000*(sourceAwareSize p n J S A B Z)^11 := by
  let T := sourceAwareSize p n J S A B Z
  have hT : 1 ≤ T := by dsimp [T,sourceAwareSize]; omega
  have hz : Z ≤ T := by dsimp [T,sourceAwareSize]; omega
  have hi := incidenceEnvelope_le n (p.R+1) J d (baseWidth 3 p.t) A B
    (Source.nativeSourceWorkPolynomial p S) T hT
    (by dsimp [T,sourceAwareSize]; omega) (by dsimp [T,sourceAwareSize]; omega)
    (by dsimp [T,sourceAwareSize]; omega) (by dsimp [T,sourceAwareSize]; omega)
    (by dsimp [T,sourceAwareSize]; omega) (by dsimp [T,sourceAwareSize]; omega)
    (by dsimp [T,sourceAwareSize]; omega) (by dsimp [T,sourceAwareSize]; omega)
  have hp : Z^9 ≤ T^11 := (Nat.pow_le_pow_left hz 9).trans (Nat.pow_le_pow_right hT (by decide))
  rw [← incidencePolynomial_eq p n J S A B] at hi
  change incidencePolynomial p n J S A B+15000000*Z^9 ≤ 275000000*T^11
  omega

/-- A fixed power of assembled work absorbs every live buffer and the
concrete source polynomial once the caller supplies their numerical bound. -/
theorem branchBound_assembled {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (n J S A B Z c work e : ℕ)
    (h : sourceAwareSize p n J S A B Z ≤ c*work^e) :
    branchBound p n J S A B Z ≤ (275000000*c^11)*work^(e*11) := by
  calc
    branchBound p n J S A B Z ≤ 275000000*(sourceAwareSize p n J S A B Z)^11 :=
      branchBound_power p n J S A B Z
    _ ≤ 275000000*(c*work^e)^11 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 11)
    _ = (275000000*c^11)*work^(e*11) := by rw [mul_pow,← pow_mul]; ring

end SubexponentialSAT.SqrtLog.LeafProgram.FactorBounds

end OAI.Algorithms
