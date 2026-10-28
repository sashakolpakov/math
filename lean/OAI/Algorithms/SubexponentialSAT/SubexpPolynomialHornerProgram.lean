import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialPowerProgram
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialAddService

namespace OAI.Algorithms

/-! The actual fixed-D geometric-series recurrence. Each iteration executes
one concrete truncated multiplication and one concrete coefficientwise
addition, then restores the cached defect as the right operand.
-/

namespace SubexponentialSAT.SubexpPolynomialHornerProgram

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing SubexpPolynomialPowerProgram

private def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

def multiply : Code := SubexpPolynomialMultiplyService.command ;;
  SubexpPolynomialIterationControl.commit

def addAndCommit : Code :=
  .seq SubexpPolynomialAddService.command SubexpPolynomialIterationControl.commit

def addOne : Code := clear 241 ;; copy 220 241 ;; addAndCommit ;; clear 241

def iteration : Code := multiply ;; clear 241 ;; copy 220 241 ;;
  addAndCommit ;; clear 241 ;; copy 222 241
def command : Code := SubexpPolynomialIterationControl.repeatLoop iteration

theorem add_length {C : Type*} (ops : SubexpSymbolicCost.RingProgram C)
    (P Q : List C) (hlen : P.length = Q.length) :
    (SubexpDensePolynomial.addProgram ops P Q).1.length = P.length := by
  induction P generalizing Q with
  | nil => cases Q <;> simp_all [SubexpDensePolynomial.addProgram]
  | cons a P ih =>
      cases Q with
      | nil => simp at hlen
      | cons b Q =>
          have htail : P.length = Q.length := by simpa using hlen
          simpa [SubexpDensePolynomial.addProgram] using congrArg Nat.succ (ih Q htail)

variable (p D : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p (D + 1))
variable (t z o : Coefficient p (D + 1))

abbrev Poly := FixedPolynomial p (D + 1) D

def sum (P Q : Poly p D) : Poly p D :=
  ⟨(SubexpDensePolynomial.addProgram (SubexpSymbolicCost.preparedProgram p D M t z o) P.val Q.val).1,
    (add_length _ P.val Q.val (P.property.trans Q.property.symm)).trans P.property⟩

def value (Z O P : Poly p D) : Poly p D :=
  sum p D M t z o (next p (D + 1) M t z Z P) O

omit [Fact p.Prime] in
theorem dense_encode (P : List (Coefficient p (D + 1))) :
    DensePolynomialPrograms.encodePolynomial P = encodeArray SubexpFlatAdd.encode P :=
  SubexpPolynomialAddService.encodePolynomial_eq_flatten_map P

theorem addOne_value (s : Store) (P R O : Poly p D)
    (width : List Bool) (frame : Fin 6 → List Bool)
    (hw : width.length = baseWidth p (D + 1))
    (hadd : ∀ i, s (SubexpPolynomialAddService.ports i) =
      (DensePolynomialLoop.ready (fun _ => false) M.bits [] [] width [] frame).stacks i)
    (h120 : s 120 = []) (h244 : s 244 = []) (h245 : s 245 = [])
    (hleft : s 240 = encode p (D + 1) P)
    (hright : s 241 = encode p (D + 1) R)
    (hone : s 220 = encode p (D + 1) O) :
    ExecutesIn addOne (64000 * (D + 1) * (baseWidth p (D + 1) + 1)^2) s
      (Function.update (Function.update s 240
        (encode p (D + 1) (sum p D M t z o P O))) 241 []) := by
  let B := baseWidth p (D + 1)
  let S := sum p D M t z o P O
  let s₁ := Function.update s 241 []
  let s₂ := Function.update s 241 (encode p (D + 1) O)
  let s₃ := Function.update s₂ 240 (encode p (D + 1) S)
  have h₁ : ExecutesIn (clear 241) (8 * D * B + 3) s s₁ := by
    have h := clear_run 241 s
    convert h using 1
    rw [hright, encode_length]
    ring
  have h₂ : ExecutesIn (copy 220 241) (28 * D * B + 5) s₁ s₂ := by
    have h := copy_run 220 241 s₁ (by decide) (by decide) (by decide)
      (by simp [s₁, h120])
    convert h using 1
    all_goals simp [s₁, s₂, hone, encode_length, B]
    all_goals ring
  have hadd' : ∀ i, s₂ (SubexpPolynomialAddService.ports i) =
      (DensePolynomialLoop.ready (fun _ => false) M.bits [] [] width [] frame).stacks i := by
    intro i
    have hi : SubexpPolynomialAddService.ports i ≠ 241 := by
      intro h
      have he := congrArg Fin.val h
      simp [SubexpPolynomialAddService.ports, Fin.coe_ofNat_eq_mod] at he
      omega
    simpa [s₂, hi] using hadd i
  have hB : 0 < B := Nat.mul_pos (Nat.zero_lt_succ D) (Nat.zero_lt_succ _)
  have hplus := SubexpPolynomialAddService.prepared_command_value p D M t z o s₂ hB
    P.val O.val width frame hw hadd' (by simp [s₂, h120])
    (by simp [s₂, h244]) (by simp [s₂, h245])
    (by simp [s₂, hleft, dense_encode, encode]) (by simp [s₂, dense_encode, encode])
  have hplus' : ExecutesIn SubexpPolynomialAddService.command
      (31000 * (D + D + 1) * (B + 1)^2) s₂
      (Function.update s₂ 244 (encode p (D + 1) S)) := by
    simpa only [B, S, sum, encode, P.property, O.property, dense_encode] using hplus
  have h₃ : ExecutesIn addAndCommit (63000 * (D + 1) * (B + 1)^2) s₂ s₃ := by
    have h := SubexpPolynomialIterationControl.step_run SubexpPolynomialAddService.command
      (31000 * (D + D + 1) * (B + 1)^2) s₂ (encode p (D + 1) S)
      (by simp [s₂, h244]) (by simp [s₂, h245]) hplus'
    apply h.mono
    have hl : (s₂ 240).length = D * (4 * B) := by simp [s₂, hleft, encode_length, B]
    rw [hl, encode_length]
    dsimp only [B]
    ring_nf
    omega
  have hfinal : Function.update s₃ 241 [] =
      Function.update (Function.update s 240 (encode p (D + 1) S)) 241 [] := by
    funext j
    by_cases hj : j = 241 <;> simp [s₃, s₂, Function.update_apply, hj]
  have h₄ : ExecutesIn (clear 241) (8 * D * B + 3) s₃
      (Function.update (Function.update s 240 (encode p (D + 1) S)) 241 []) := by
    have h := clear_run 241 s₃
    rw [hfinal] at h
    convert h using 1
    simp [s₃, s₂, encode_length]
    ring
  have h := h₁.seq (h₂.seq (h₃.seq h₄))
  apply h.mono
  dsimp only [B]
  ring_nf
  omega

theorem iteration_value (s : Store) (P Z O : Poly p D)
    (width : List Bool) (frame : Fin 6 → List Bool)
    (H : SubexpConvolutionPairSpec.BaseReady p (D + 1) M s t width frame)
    (hadd : ∀ i, s (SubexpPolynomialAddService.ports i) =
      (DensePolynomialLoop.ready (fun _ => false) M.bits [] [] width [] frame).stacks i)
    (hempty : ∀ i, s (bufferPorts i) = [])
    (h120 : s 120 = []) (h121 : s 121 = []) (h122 : s 122 = [])
    (h244 : s 244 = []) (h245 : s 245 = [])
    (hleft : s 240 = encode p (D + 1) P)
    (hright : s 241 = encode p (D + 1) Z)
    (hone : s 220 = encode p (D + 1) O)
    (hdefect : s 222 = encode p (D + 1) Z)
    (hzero : s 242 = encodeArray SubexpFlatAdd.encode (List.replicate D z))
    (hD : (s 243).length = D) :
    ExecutesIn iteration (700000 * (D + 1)^3 * (baseWidth p (D + 1) + 1)^2) s
      (Function.update s 240 (encode p (D + 1) (value p D M t z o Z O P))) := by
  let B := baseWidth p (D + 1)
  let R := next p (D + 1) M t z Z P
  let S := value p D M t z o Z O P
  let s₁ := Function.update s 240 (encode p (D + 1) R)
  let s₂ := Function.update s₁ 241 []
  let s₃ := Function.update s₁ 241 (encode p (D + 1) O)
  let s₄ := Function.update s₃ 240 (encode p (D + 1) S)
  let s₅ := Function.update s₄ 241 []
  have hB : 0 < B := Nat.mul_pos (Nat.zero_lt_succ D) (Nat.zero_lt_succ _)
  have hmul := SubexpPolynomialMultiplyService.command_value p (D + 1) M s t z width frame H
    hempty h120 h121 h122 h244 h245 D P.val Z.val P.property Z.property hleft hright hzero hD
  have h₁ : ExecutesIn multiply (602000 * (D + 1)^3 * (B + 1)^2) s s₁ := by
    have h := SubexpPolynomialIterationControl.step_run SubexpPolynomialMultiplyService.command
      (601000 * (D + 1)^3 * (B + 1)^2) s (encode p (D + 1) R) h244 h245 hmul
    apply h.mono
    rw [hleft, encode_length, encode_length]
    dsimp only [B]
    ring_nf
    omega
  have h₂ : ExecutesIn (clear 241) (8 * D * B + 3) s₁ s₂ := by
    have h := clear_run 241 s₁
    convert h using 1
    simp [s₁, hright, encode_length]
    ring
  have h₃ : ExecutesIn (copy 220 241) (28 * D * B + 5) s₂ s₃ := by
    have h := copy_run 220 241 s₂ (by decide) (by decide) (by decide)
      (by simp [s₂, s₁, h120])
    convert h using 1
    all_goals simp [s₂, s₃, s₁, hone, encode_length, B]
    all_goals ring
  have hadd' : ∀ i, s₃ (SubexpPolynomialAddService.ports i) =
      (DensePolynomialLoop.ready (fun _ => false) M.bits [] [] width [] frame).stacks i := by
    intro i
    have h240 : SubexpPolynomialAddService.ports i ≠ 240 := by
      intro h
      have he := congrArg Fin.val h
      simp [SubexpPolynomialAddService.ports, Fin.coe_ofNat_eq_mod] at he
      omega
    have h241 : SubexpPolynomialAddService.ports i ≠ 241 := by
      intro h
      have he := congrArg Fin.val h
      simp [SubexpPolynomialAddService.ports, Fin.coe_ofNat_eq_mod] at he
      omega
    simpa [s₃, s₁, h240, h241] using hadd i
  have hplus := SubexpPolynomialAddService.prepared_command_value p D M t z o s₃ hB
    R.val O.val width frame H.scalarWidthLength hadd'
    (by simp [s₃, s₁, h120]) (by simp [s₃, s₁, h244]) (by simp [s₃, s₁, h245])
    (by simp [s₃, s₁, dense_encode, encode])
    (by simp [s₃, dense_encode, encode])
  have hplus' : ExecutesIn SubexpPolynomialAddService.command
      (31000 * (D + D + 1) * (B + 1)^2) s₃
      (Function.update s₃ 244 (encode p (D + 1) S)) := by
    simpa only [B, S, value, sum, encode, R.property, O.property, dense_encode] using hplus
  have h₄ : ExecutesIn
      (.seq SubexpPolynomialAddService.command SubexpPolynomialIterationControl.commit)
      (63000 * (D + 1) * (B + 1)^2) s₃ s₄ := by
    have h := SubexpPolynomialIterationControl.step_run SubexpPolynomialAddService.command
      (31000 * (D + D + 1) * (B + 1)^2) s₃ (encode p (D + 1) S)
      (by simp [s₃, s₁, h244]) (by simp [s₃, s₁, h245]) hplus'
    apply h.mono
    have hl : (s₃ 240).length = D * (4 * B) := by simp [s₃, s₁, encode_length, B]
    rw [hl, encode_length]
    dsimp only [B]
    ring_nf
    omega
  have h₅ : ExecutesIn (clear 241) (8 * D * B + 3) s₄ s₅ := by
    have h := clear_run 241 s₄
    convert h using 1
    simp [s₄, s₃, encode_length]
    ring
  have he₆ : Function.update s₅ 241 (s₅ 222 ++ s₅ 241) =
      Function.update s 240 (encode p (D + 1) S) := by
    funext j
    by_cases h241 : j = 241 <;> by_cases h240 : j = 240 <;>
      simp [s₅, s₄, s₃, s₁, h241, h240, hdefect, hright]
  have h₆ : ExecutesIn (copy 222 241) (28 * D * B + 5) s₅
      (Function.update s 240 (encode p (D + 1) S)) := by
    have h := copy_run 222 241 s₅ (by decide) (by decide) (by decide)
      (by simp [s₅, s₄, s₃, s₁, h120])
    rw [he₆] at h
    convert h using 1
    all_goals simp [s₅, s₄, s₃, s₁, hdefect, encode_length, B]
    all_goals ring
  have h := h₁.seq (h₂.seq (h₃.seq (h₄.seq (h₅.seq h₆))))
  apply h.mono
  dsimp only [B]
  ring_nf
  omega

theorem command_value (s : Store) (Z O P : Poly p D) (counter : List Bool)
    (width : List Bool) (frame : Fin 6 → List Bool)
    (H : SubexpConvolutionPairSpec.BaseReady p (D + 1) M s t width frame)
    (hadd : ∀ i, s (SubexpPolynomialAddService.ports i) =
      (DensePolynomialLoop.ready (fun _ => false) M.bits [] [] width [] frame).stacks i)
    (hempty : ∀ i, s (bufferPorts i) = [])
    (h120 : s 120 = []) (h121 : s 121 = []) (h122 : s 122 = [])
    (h244 : s 244 = []) (h245 : s 245 = [])
    (hright : s 241 = encode p (D + 1) Z)
    (hone : s 220 = encode p (D + 1) O)
    (hdefect : s 222 = encode p (D + 1) Z)
    (hzero : s 242 = encodeArray SubexpFlatAdd.encode (List.replicate D z))
    (hD : (s 243).length = D) :
    ExecutesIn command
      (counter.length * (700000 * (D + 1)^3 * (baseWidth p (D + 1) + 1)^2 + 2) + 2)
      (SubexpPolynomialIterationControl.ready s (encode p (D + 1)) P counter)
      (SubexpPolynomialIterationControl.ready s (encode p (D + 1))
        (((value p D M t z o Z O)^[counter.length]) P) []) := by
  apply SubexpPolynomialIterationControl.repeat_run s (encode p (D + 1)) iteration
    (value p D M t z o Z O) _ _ counter P
  intro A count
  let before := SubexpPolynomialIterationControl.ready s (encode p (D + 1)) A count
  have below : ∀ j : Fin 256, j.val < 205 → before j = s j :=
    ready_below p (D + 1) s A count
  have hadd' : ∀ i, before (SubexpPolynomialAddService.ports i) =
      (DensePolynomialLoop.ready (fun _ => false) M.bits [] [] width [] frame).stacks i := by
    intro i
    rw [below _ (by
      dsimp [SubexpPolynomialAddService.ports]
      have := i.isLt
      omega)]
    exact hadd i
  have h := iteration_value p D M t z o before A Z O width frame
    (baseReady_congr p (D + 1) M s before t width frame below H) hadd'
    (fun i => by rw [below _ (bufferPorts_lt i)]; exact hempty i)
    (by rw [below 120 (by decide)]; exact h120)
    (by rw [below 121 (by decide)]; exact h121)
    (by rw [below 122 (by decide)]; exact h122)
    (by simp [before, SubexpPolynomialIterationControl.ready, h244])
    (by simp [before, SubexpPolynomialIterationControl.ready, h245])
    (by simp [before, SubexpPolynomialIterationControl.ready])
    (by simp [before, SubexpPolynomialIterationControl.ready, hright])
    (by simp [before, SubexpPolynomialIterationControl.ready, hone])
    (by simp [before, SubexpPolynomialIterationControl.ready, hdefect])
    (by simp [before, SubexpPolynomialIterationControl.ready, hzero])
    (by simp [before, SubexpPolynomialIterationControl.ready, hD])
  have he : Function.update before 240 (encode p (D + 1) (value p D M t z o Z O A)) =
      SubexpPolynomialIterationControl.ready s (encode p (D + 1))
        (value p D M t z o Z O A) count := by
    funext j
    by_cases hj : j = 246 <;> by_cases h240 : j = 240 <;>
      simp [before, SubexpPolynomialIterationControl.ready, hj, h240]
  rw [he] at h
  exact h

end SubexponentialSAT.SubexpPolynomialHornerProgram

end OAI.Algorithms
