import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialIterationControl
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialMultiplyService

namespace OAI.Algorithms

/-! Repeated truncated multiplication by one cached polynomial, controlled
by an actual unary stack. Both the multiplication program and its workspace
cleanup are fixed, independently of the runtime degree and exponent. -/

namespace SubexponentialSAT.SubexpPolynomialPowerProgram

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing

def iteration : Code :=
  SubexpPolynomialIterationControl.step SubexpPolynomialMultiplyService.command
def command : Code := SubexpPolynomialIterationControl.repeatLoop iteration
def program := compiled command 240 240

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

abbrev Coefficient := SubexpTruncatedMultiply.Coefficient p μ
abbrev FixedPolynomial (D : ℕ) := {P : List (Coefficient p μ) // P.length = D}

def encode {D : ℕ} (P : FixedPolynomial p μ D) : List Bool :=
  encodeArray SubexpFlatAdd.encode P.val

omit [Fact p.Prime] in
@[simp] theorem encode_length {D : ℕ} (P : FixedPolynomial p μ D) :
    (encode p μ P).length = D * (4 * baseWidth p μ) := by
  rw [encode, encodeArray_length _ _ (fun a => SubexpFlatAdd.encode_length a), P.property]

def next (t z : Coefficient p μ) {D : ℕ} (Q P : FixedPolynomial p μ D) :
    FixedPolynomial p μ D :=
  ⟨SubexpTruncatedMultiply.result p μ M t z D P.val Q.val,
    SubexpTruncatedMultiply.result_length p μ M t z D P.val Q.val⟩

theorem bufferPorts_lt (i : Fin 11) : (bufferPorts i).val < 205 := by
  fin_cases i <;> decide

omit [Fact p.Prime] in
/-- The arithmetic service reads no metadata above stack 204. -/
theorem baseReady_congr (s s' : Store) (t : Coefficient p μ)
    (width : List Bool) (frame : Fin 6 → List Bool)
    (h : ∀ j : Fin 256, j.val < 205 → s' j = s j)
    (H : SubexpConvolutionPairSpec.BaseReady p μ M s t width frame) :
    SubexpConvolutionPairSpec.BaseReady p μ M s' t width frame := by
  constructor
  · intro j h70 h71
    rw [h _ (by dsimp [SubexpConvolutionPair.highPort]; omega)]
    exact H.high j h70 h71
  · intro j
    rw [h _ (by
      dsimp [SubexpConvolutionPair.lowPort, SubexpJetCellProgram.scalarPorts]
      omega)]
    exact H.low j
  · rw [h 104 (by decide)]
    exact H.width
  · exact H.scalarWidthLength
  · intro j hlo hhi
    rw [h j (by omega)]
    exact H.work j hlo hhi

omit [Fact p.Prime] in
theorem ready_below {D : ℕ} (s : Store) (P : FixedPolynomial p μ D)
    (counter : List Bool) (j : Fin 256) (hj : j.val < 205) :
    SubexpPolynomialIterationControl.ready s (encode p μ) P counter j = s j := by
  have h240 : j ≠ 240 := by intro h; subst j; simp [Fin.coe_ofNat_eq_mod] at hj
  have h246 : j ≠ 246 := by intro h; subst j; simp [Fin.coe_ofNat_eq_mod] at hj
  simp [SubexpPolynomialIterationControl.ready, h240, h246]

theorem iteration_value (s : Store) (t z : Coefficient p μ)
    (width : List Bool) (frame : Fin 6 → List Bool)
    (H : SubexpConvolutionPairSpec.BaseReady p μ M s t width frame)
    (hempty : ∀ i, s (bufferPorts i) = [])
    (h120 : s 120 = []) (h121 : s 121 = []) (h122 : s 122 = [])
    (h244 : s 244 = []) (h245 : s 245 = [])
    (D : ℕ) (P Q : FixedPolynomial p μ D)
    (hright : s 241 = encode p μ Q)
    (hzero : s 242 = encodeArray SubexpFlatAdd.encode (List.replicate D z))
    (hD : (s 243).length = D) (counter : List Bool) :
    ExecutesIn iteration (602000 * (D + 1)^3 * (baseWidth p μ + 1)^2)
      (SubexpPolynomialIterationControl.ready s (encode p μ) P counter)
      (SubexpPolynomialIterationControl.ready s (encode p μ) (next p μ M t z Q P) counter) := by
  let before := SubexpPolynomialIterationControl.ready s (encode p μ) P counter
  let out := encode p μ (next p μ M t z Q P)
  have hb : ∀ j : Fin 256, j.val < 205 → before j = s j :=
    ready_below p μ s P counter
  have hmul := SubexpPolynomialMultiplyService.command_value p μ M before t z width frame
    (baseReady_congr p μ M s before t width frame hb H)
    (fun i => by rw [hb _ (bufferPorts_lt i)]; exact hempty i)
    (by rw [hb 120 (by decide)]; exact h120)
    (by rw [hb 121 (by decide)]; exact h121)
    (by rw [hb 122 (by decide)]; exact h122)
    (by simpa [before, SubexpPolynomialIterationControl.ready] using h244)
    (by simpa [before, SubexpPolynomialIterationControl.ready] using h245)
    D P.val Q.val P.property Q.property
    (by simp [before, SubexpPolynomialIterationControl.ready, encode])
    (by simpa [before, SubexpPolynomialIterationControl.ready, encode] using hright)
    (by simpa [before, SubexpPolynomialIterationControl.ready] using hzero)
    (by simpa [before, SubexpPolynomialIterationControl.ready] using hD)
  have hstep := SubexpPolynomialIterationControl.step_run
    SubexpPolynomialMultiplyService.command
    (601000 * (D + 1)^3 * (baseWidth p μ + 1)^2) before out
    (by simpa [before, SubexpPolynomialIterationControl.ready] using h244)
    (by simpa [before, SubexpPolynomialIterationControl.ready] using h245) hmul
  have he : Function.update before 240 out =
      SubexpPolynomialIterationControl.ready s (encode p μ) (next p μ M t z Q P) counter := by
    funext j
    by_cases h : j = 246 <;> by_cases h240 : j = 240 <;>
      simp [before, out, SubexpPolynomialIterationControl.ready, h, h240]
  rw [he] at hstep
  apply hstep.mono
  have hl : (before 240).length = D * (4 * baseWidth p μ) := by
    simp [before, SubexpPolynomialIterationControl.ready]
  have ho : out.length = D * (4 * baseWidth p μ) := encode_length p μ _
  rw [hl, ho]
  ring_nf
  omega

/-- The actual loop performs exactly as many multiplications as there are
bits in the runtime counter. The counter is consumed, and each array stays
at exactly D coefficients. -/
theorem command_value (s : Store) (t z : Coefficient p μ)
    (width : List Bool) (frame : Fin 6 → List Bool)
    (H : SubexpConvolutionPairSpec.BaseReady p μ M s t width frame)
    (hempty : ∀ i, s (bufferPorts i) = [])
    (h120 : s 120 = []) (h121 : s 121 = []) (h122 : s 122 = [])
    (h244 : s 244 = []) (h245 : s 245 = [])
    (D : ℕ) (P Q : FixedPolynomial p μ D)
    (hright : s 241 = encode p μ Q)
    (hzero : s 242 = encodeArray SubexpFlatAdd.encode (List.replicate D z))
    (hD : (s 243).length = D) (counter : List Bool) :
    ExecutesIn command
      (counter.length * (602000 * (D + 1)^3 * (baseWidth p μ + 1)^2 + 2) + 2)
      (SubexpPolynomialIterationControl.ready s (encode p μ) P counter)
      (SubexpPolynomialIterationControl.ready s (encode p μ)
        (((next p μ M t z Q)^[counter.length]) P) []) := by
  exact SubexpPolynomialIterationControl.repeat_run s (encode p μ) iteration
    (next p μ M t z Q) _
    (fun a count => iteration_value p μ M s t z width frame H hempty h120 h121 h122
      h244 h245 D a Q hright hzero hD count) counter P

end SubexponentialSAT.SubexpPolynomialPowerProgram

end OAI.Algorithms
